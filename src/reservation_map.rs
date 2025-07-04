use core::range;
use std::alloc::{Global, System};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, Bound, HashMap};
use std::collections::btree_set::{CursorMut, UnorderedKeyError};
use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasher, Hash, Hasher, RandomState};
use std::ops::Bound::Included;
use std::ops::{Add, Deref, Div, Sub};
use std::time::SystemTime;
use rand::prelude::SliceRandom;

macro_rules! timed {
    ($($tt:tt)*) => {
        {
            let __start = SystemTime::now();
            let __res = {
                $($tt)*
            };
            let __end = SystemTime::now();
            let __dur = __end.duration_since(__start).unwrap();
            println!("{}:{} {}us", file!(), line!(), __dur.as_micros());
            __res
        }
    };
}

struct SimpleHasher(u64);
impl BuildHasher for SimpleHasher {
    type Hasher = SimpleHasher;

    fn build_hasher(&self) -> Self::Hasher {
        SimpleHasher(0)
    }
}
impl Hasher for SimpleHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, _bytes: &[u8]) {
        panic!("SimpleHasher does not support bytes");
    }

    fn write_u8(&mut self, _i: u8) {
        panic!("SimpleHasher does not support u8");
    }

    fn write_u32(&mut self, val: u32) {
        self.0 = (((val >> 16) ^ val) * 0x45d9f3b) as u64;
    }

    fn write_usize(&mut self, val: usize) {
        self.0 = (((val >> 16) ^ val) * 0x45d9f3b) as u64;
    }
}

type LaneId = u32;

/// A resource requirement that specifies the width of a contiguous block of resources necessary for a reservation
#[derive(Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
struct ResourceWidth {
    width: u32,
}
impl Debug for ResourceWidth {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<-{}->", self.width)
    }
}
impl ResourceWidth {
    pub fn new(width: u32) -> Self {
        ResourceWidth { width }
    }
}


#[derive(Copy, Clone, PartialEq, Eq)]
struct ResourceBlock {
    start: LaneId,
    end: LaneId, // exclusive
}
impl ResourceBlock {
    pub fn new(start: LaneId, end: LaneId) -> Self {
        ResourceBlock { start, end }
    }

    pub fn width(&self) -> u32 {
        self.end - self.start
    }

    pub fn offset_by(&self, offset: u32) -> Self {
        ResourceBlock {
            start: self.start + offset,
            end: self.end + offset,
        }
    }
}
impl Debug for ResourceBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[#{:?}-#{:?}]", self.start, self.end - 1)
    }
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
struct Step(u32);
impl Step {
    pub const UNSET: Step = Step(u32::MAX);

    pub fn is_set(&self) -> bool {
        self.0 != u32::MAX
    }

    pub fn is_unset(&self) -> bool {
        self.0 == u32::MAX
    }

    pub fn clamp_before(min: Step, max_exclusive: Step) -> Self {
        Step(max_exclusive.0.saturating_sub(1).max(min.0))
    }

    pub fn clamp_after(min_exclusive: Step, max: Step) -> Self {
        Step(min_exclusive.0.saturating_add(1).min(max.0))
    }

    fn get_and_increment(&mut self) -> Step {
        let step = self.0;
        self.0 += 1;
        Step(step)
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct Duration {
    start: Step,
    end: Step, // inclusive
}
impl Debug for Duration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}-{}]", self.start.0, self.end.0)
    }
}
impl Duration {
    pub fn new(start: Step, end: Step) -> Self {
        Duration { start, end }
    }

    pub fn new_unbounded(start: Step) -> Self {
        Duration { start, end: Step::UNSET }
    }

    pub fn length(&self) -> u32 {
        if self.end.is_unset() {
            u32::MAX
        } else {
            self.end.0 - self.start.0
        }
    }

    pub fn is_nonzero(&self) -> bool {
        self.start < self.end
    }

    pub fn is_unbounded(&self) -> bool {
        self.end.is_unset()
    }

    pub fn overlaps_with(&self, other: &Duration) -> bool {
        self.start <= other.end || self.end >= other.start
    }

    pub fn can_contain(&self, other: &Duration) -> bool {
        self.start <= other.start && self.end >= other.end
    }
}
impl PartialOrd for Duration {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}
impl Ord for Duration {
    fn cmp(&self, other: &Self) -> Ordering {
        self.start.cmp(&other.start)
    }
}

/// A desired allocation of resources of some minimum width for a given duration
#[derive(Copy, Clone, PartialEq, Eq)]
struct PreAllocation
{
    width: ResourceWidth,
    duration: Duration
}
impl PreAllocation {
    pub fn width(&self) -> u32 {
        self.width.width
    }
    pub fn length(&self) -> u32 {
        self.duration.length()
    }
}
impl Debug for PreAllocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{:?}: {:?}-{:?}]", self.width.width, self.duration.start.0, self.duration.end.0)
    }
}
impl PartialOrd for PreAllocation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // primary sort by width descending
        // secondary sort by start step asc for equal resource widths
        Some(self.cmp(other))
    }
}
impl Ord for PreAllocation {
    fn cmp(&self, other: &Self) -> Ordering {
        other.width.width.cmp(&self.width.width)
            .then_with(|| self.duration.start.cmp(&other.duration.start))
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct ReservationId(usize);
impl Debug for ReservationId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "${:?}", self.0)
    }
}
impl Hash for ReservationId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.0);
    }
}

#[derive(PartialEq, Eq)]
struct Allocation {
    id: ReservationId,
    block: ResourceBlock,
    duration: Duration
}
impl Allocation {
    pub fn new(res_id: ReservationId, res_req: PreAllocation, allocation: ResourceBlock) -> Self {
        Allocation {
            id: res_id,
            duration: res_req.duration,
            block: allocation,
        }
    }
}
impl Debug for Allocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -> {:?} {:?}", self.id, self.block, self.duration)
    }
}
impl PartialOrd for Allocation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}
impl Ord for Allocation {
    fn cmp(&self, other: &Self) -> Ordering {
        self.duration.cmp(&other.duration)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct Vacancy {
    duration: Duration,
    empty_block: ResourceBlock,
}
impl Vacancy {
    pub fn new(allocation: ResourceBlock, duration: Duration) -> Self {
        Vacancy {
            duration,
            empty_block: allocation,
        }
    }

    pub fn range(duration: Duration) -> Self {
        Vacancy {
            duration,
            empty_block: ResourceBlock::new(0, 0),
        }
    }

    pub fn width(&self) -> u32 {
        self.empty_block.width()
    }

    pub fn can_contain(&self, other: &PreAllocation) -> bool {
        self.duration.can_contain(&other.duration) && self.width() >= other.width()
    }

    /// empty vacancies can be returned from calculating margin after allocation
    ///
    /// this returns true if the vacancy is a non-zero width and a non-zero length
    ///
    /// otherwise, the vacancy should be discarded
    pub fn is_non_empty(&self) -> bool {
        self.duration.is_nonzero() && self.empty_block.width() > 0
    }

    pub fn get_allocation_for(&self, res_request: &PreAllocation) -> ResourceBlock {
        let start = self.empty_block.start;
        let end = start + res_request.width();
        ResourceBlock::new(start, end)
    }

    /// returns the left, right, and vertical margins around the given resource request
    ///
    /// if the vertical margin is smaller than the requested resource width, then it should be added to a buffer and added once the pass width is <= the margin width
    /// this is to ensure that vacancies can accommodate the requested width in this pass
    pub fn get_margin_around(&self, res_request: &PreAllocation) -> Option<(Vacancy, Vacancy, Vacancy)> {
        if !self.duration.can_contain(&res_request.duration) || self.width() < res_request.width() {
            return None
        }

        let left_duration = Duration::new(self.duration.start, Step::clamp_before(self.duration.start, res_request.duration.start));
        let right_duration = Duration::new(Step::clamp_after(res_request.duration.end, self.duration.end), self.duration.end);

        let left_margin = Vacancy {
            duration: left_duration,
            empty_block: self.empty_block,
        };
        let right_margin = Vacancy {
            duration: right_duration,
            empty_block: self.empty_block,
        };
        let vertical_margin = Vacancy {
            duration: self.duration,
            empty_block: ResourceBlock::new(
                self.empty_block.start.add(res_request.width()),
                self.empty_block.end,
            ),
        };

        Some((left_margin, right_margin, vertical_margin))
    }
}
impl PartialOrd for Vacancy {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}
impl Ord for Vacancy {
    fn cmp(&self, other: &Self) -> Ordering {
        self.duration.cmp(&other.duration)
    }
}

struct VacanciesCursor<'a> {
    cursor: CursorMut<'a, Vacancy>,
    bounding_box: &'a mut Duration,
}
impl<'a> VacanciesCursor<'a> {
    pub fn peek_prev(&mut self) -> Option<&Vacancy> {
        self.cursor.peek_prev()
    }

    pub fn peek_next(&mut self) -> Option<&Vacancy> {
        self.cursor.peek_next()
    }

    pub fn remove_prev(&mut self) -> Option<Vacancy> {
        let removed = self.cursor.remove_prev()?;
        if removed.duration.start == self.bounding_box.start {
            self.bounding_box.start = removed.duration.end
        } else if removed.duration.end == self.bounding_box.end {
            self.bounding_box.end = removed.duration.start
        }
        
        Some(removed)
    }

    pub fn insert_before(&mut self, value: Vacancy) -> Result<(), UnorderedKeyError> {
        self.cursor.insert_before(value)?;
        
        if self.bounding_box.start > value.duration.start {
            self.bounding_box.start = value.duration.start
        }
        if self.bounding_box.end < value.duration.end {
            self.bounding_box.end = value.duration.end
        }
        
        Ok(())
    }

    pub fn insert_after(&mut self, value: Vacancy) -> Result<(), UnorderedKeyError> {
        self.cursor.insert_after(value)?;

        if self.bounding_box.start > value.duration.start {
            self.bounding_box.start = value.duration.start
        }
        if self.bounding_box.end < value.duration.end {
            self.bounding_box.end = value.duration.end
        }

        Ok(())
    }
}

#[derive(Debug)]
struct Vacancies {
    vacancies: BTreeSet<Vacancy>,
    // the min and max possible values of this vacancy sequence
    step_bounding_box: Duration
}
impl Vacancies {
    pub fn new(vacancy: Vacancy) -> Self {
        Vacancies {
            vacancies: BTreeSet::from([vacancy]),
            step_bounding_box: vacancy.duration
        }
    } 

    pub fn upper_bound_mut(&mut self, bound: Bound<&Vacancy>) -> VacanciesCursor<'_> {
        let Vacancies {
            vacancies,
            step_bounding_box
        } = self;


        VacanciesCursor {
            cursor: unsafe { vacancies.upper_bound_mut(bound) },
            bounding_box: step_bounding_box,
        }
    }
}

/// A structure that tracks vacancies for a given resource width
struct Resources {
    // a set of non-overlapping sequences of vacancies
    sequences: Vec<Vacancies>,
    reservations: Vec<Allocation>,
    next_pass_vacancies: Vec<Vacancy>,
    width: u32,
}
impl Resources {
    pub fn new(width: ResourceWidth) -> Self {
        // start with a single vacancy encompassing the entire timeline
        let vacancies = Vacancies::new(Vacancy::new(
            ResourceBlock::new(0, width.width),
            Duration::new_unbounded(Step(0))
        ));
        
        Resources {
            sequences: vec![vacancies],
            reservations: Vec::new(),
            next_pass_vacancies: Vec::new(),
            width: width.width,
        }
    }

    /// reserves the request, returning the allocation that was reserved
    pub fn reserve_vacancy(&mut self, reservation_id: ReservationId, reservation_request: PreAllocation) -> ResourceBlock {
        
        let allocated_vacancy = self.sequences.iter_mut()
            .find_map(|sequence| {

                if !sequence.step_bounding_box.can_contain(&reservation_request.duration) {
                    return None;
                }
                
                let mut found_spot =
                    sequence.upper_bound_mut(Included(&Vacancy::range(reservation_request.duration)));
                
                found_spot.peek_prev()
                    .filter(|vac| vac.can_contain(&reservation_request))
                    .map(|_| ())
                    .and_then(|_| {
                        found_spot.remove_prev()
                    })
                    .map(|reserved_vac| {
                        // println!("\nReserving vacancy: {:?} for req {:?}", reserved_vac, reservation_request);
                        let (left, right, vertical) = reserved_vac.get_margin_around(&reservation_request)
                            .expect("Found vacancy that cannot contain the reservation request");
                        // println!("Left: {:?}, Right: {:?}, Vertical: {:?}", left, right, vertical);
                        if left.is_non_empty() {
                            found_spot.insert_before(left).expect("Failed to insert left margin");
                        }
                        if right.is_non_empty() {
                            found_spot.insert_after(right).expect("Failed to insert right margin");
                        }

                        let alloc = reserved_vac.get_allocation_for(&reservation_request);
                        // println!("Reserved allocation: {:?}", alloc);
                        (alloc, vertical)
                    })
            });
        
        
        if let Some((allocation, vertical_margin)) = allocated_vacancy {
            // println!("Found vacancy to fit {reservation_id:?} {reservation_request:?}");
            
            if vertical_margin.is_non_empty() {

                if vertical_margin.width() >= reservation_request.width() {
                    
                    // println!("Tracking vertical margin: {:?}", vertical_margin);
                    if vertical_margin.duration.is_unbounded() {
                        self.sequences.push(Vacancies::new(vertical_margin))
                    } else {
                        self.track_vacancy(vertical_margin);
                    }
                } else {
                    // println!("Deferring vertical margin: {:?}", vertical_margin);
                    self.next_pass_vacancies.push(vertical_margin);
                }
            }
            allocation
            
        } else {
            // println!("Could not find vacancy to fit {reservation_id:?} {reservation_request:?}");
            let allocated_vacancy = self.allocate_new_vacancy(reservation_request.width);
            let allocation = allocated_vacancy.get_allocation_for(&reservation_request);
            let (left, right, vertical) = allocated_vacancy.get_margin_around(&reservation_request)
                .expect("Unbounded vacancy that cannot contain the reservation request");

            let mut new_vacancies = Vacancies::new(right);
            let mut cursor = new_vacancies.upper_bound_mut(Included(&allocated_vacancy));

            let insert_left_margin = left.is_non_empty();
            if insert_left_margin {
                cursor.insert_before(left).expect("Failed to insert left margin");
            }

            if vertical.is_non_empty() {
                if vertical.width() >= reservation_request.width() {
                    if !insert_left_margin {
                        cursor.insert_after(vertical).expect("Failed to insert vertical margin");
                    } else {
                        self.sequences.push(Vacancies::new(vertical))
                    }
                } else {
                    if !insert_left_margin {
                        cursor.insert_after(vertical).expect("Failed to insert vertical margin");
                    } else {
                        self.next_pass_vacancies.push(vertical);
                    }
                }
            }
            self.sequences.push(new_vacancies);

            allocation
            
        }
    }

    /// indicates that all subsequent accesses to this lane will have the given resource width or less
    ///
    /// this instructs the lane to make vacancies available that were not large enough to accommodate resources in the previous pass
    pub fn next_pass(&mut self, pass_req: ResourceWidth) {
        timed! {
            if self.next_pass_vacancies.is_empty() {
            return;
        }
        
            let mut next_pass_vacancies = std::mem::take(&mut self.next_pass_vacancies);
            next_pass_vacancies.retain(|vac| {
                if vac.width() >= pass_req.width {
                    self.track_vacancy(*vac);
                    false
                } else {
                    true
                }
            });
            let _ = std::mem::replace(&mut self.next_pass_vacancies, next_pass_vacancies);
        }
    }

    pub fn finalize(&mut self) {
        self.reservations.sort()
    }
    
    fn allocate_new_vacancy(&mut self, resource_requirement: ResourceWidth) -> Vacancy {
        // create a new vacancy that encompasses the entire timeline
        let new_vacancy = Vacancy::new(
            ResourceBlock::new(0, resource_requirement.width).offset_by(self.width),
            Duration::new_unbounded(Step(0))
        );
        self.width += resource_requirement.width;
        new_vacancy
    }

    /// makes a vacancy available for reservation in this lane.
    ///
    /// used to enforce the no-overlapping-vacancies rule.
    fn track_vacancy(&mut self, vacancy: Vacancy) {
        if !vacancy.is_non_empty() {
            return;
        }

        // self.sequences.push(Vacancies::new(vacancy));
        // return;

        let mut tracked = false;
        for sequence in self.sequences.iter_mut() {
            if sequence.step_bounding_box.overlaps_with(&vacancy.duration) {
                // don't bother with vacancy sequences whose bounding box overlaps with the vacancy to track
                break;
            }
            
            // find a vacancy that can contain the reservation
            let mut found_spot = sequence.upper_bound_mut(Included(&vacancy));

            let starts_before_or_at = found_spot.peek_prev();
            if let Some(starts_before_or_at) = starts_before_or_at {
                if starts_before_or_at.duration.end >= vacancy.duration.start {
                    continue
                }
            }

            let starts_after = found_spot.peek_next();
            if let Some(starts_after) = starts_after {
                if starts_after.duration.start <= vacancy.duration.end {
                    continue
                }
            }

            found_spot.insert_before(vacancy)
                .expect("Failed to insert vacancy");
            tracked = true;
            break
        }

        if !tracked {
            // no sequence found, create a new one
            self.sequences.push(Vacancies::new(vacancy));
        }
    }

    /// Attempts to reserve the given reservation request in the lane
    ///
    /// If a vacancy is found that can accommodate the reservation, it will be reserved and split into multiple smaller vacancies making up the margins.
    fn reserve(&mut self, reservation_id: ReservationId, req: &PreAllocation) {
        // find a vacancy that can contain the reservation, and reserve it
        // also tracks the resulting margins
        let allocation = self.reserve_vacancy(reservation_id, *req);
        self.reservations.push(
            Allocation::new(
                reservation_id,
                *req,
                allocation
            )
        );
    }
}
impl Debug for Resources {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut max_lane = self.reservations.iter()
            .map(|alloc| alloc.block.end)
            .max()
            .unwrap_or(0) - 1;

        fn unique(reservation_id: ReservationId) -> String {
            char::from_u32(reservation_id.0 as u32 + '0' as u32).unwrap().to_string()
        }

        for lane in 0..=max_lane {
            write!(f, "\n#{lane:<2}: ")?;
            let mut end_of_prev = 0;

            for res in &self.reservations {
                if res.block.start <= lane && res.block.end > lane {
                    // println!("{res:?} dur start: {}, end of prev: {}", res.duration.start.0, end_of_prev);
                    let gap_len = res.duration.start.0 - end_of_prev;
                    write!(f, "{}", " ".repeat(gap_len as usize))?;
                    write!(f, "{}", unique(res.id).repeat(res.duration.length() as usize))?;
                    end_of_prev = res.duration.end.0;
                }
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
struct ReservationData {
    id: ReservationId,
    request: PreAllocation,
}
impl ReservationData {
    pub fn new(id: ReservationId, request: PreAllocation) -> Self {
        ReservationData { id, request }
    }
}

/// the structure used to collect reservations before they are packed into the reservation map
struct ReservationBuilder {
    step: Step,
    checked_out: HashMap<ReservationId, (ResourceWidth, Vec<ReservationData>), SimpleHasher>,
    requests: HashMap<ResourceWidth, Vec<Vec<ReservationData>>, SimpleHasher>,
    id_counter: usize
}
impl ReservationBuilder {
    pub fn new() -> Self {
        ReservationBuilder {
            step: Step(0),
            checked_out: HashMap::with_hasher(SimpleHasher(0)),
            requests: HashMap::with_hasher(SimpleHasher(0)),
            id_counter: 0
        }
    }

    pub fn reserve(&mut self, req: ResourceWidth) -> ReservationId {
        let id = ReservationId(self.id_counter);
        self.id_counter += 1;
        let request = PreAllocation {
            width: req,
            duration: Duration::new_unbounded(self.step.get_and_increment()),
        };
        self.check_out(ReservationData::new(id, request));
        id
    }

    pub fn free(&mut self, id: ReservationId) -> Result<(), &str> {
        let end_step = self.step.get_and_increment();
        self.un_check_out(id, end_step)
    }

    fn check_out(&mut self, rsvn: ReservationData) {
        let width = rsvn.request.width;
        let mut sequence = self.requests.get_mut(&width)
            .and_then(|lane| lane.pop())
            .unwrap_or_else(|| vec![]);

        let id = rsvn.id;
        sequence.push(rsvn);
        // println!("Inserting {id:?}");
        self.checked_out.insert(id, (width, sequence));
    }

    fn un_check_out(&mut self, id: ReservationId, end_step: Step) -> Result<(), &str> {
        // println!("Removing {id:?}");
        let Some((width, mut sequence)) = self.checked_out.remove(&id)
            else { return Err("element did not exist") };

        let Some(_) = sequence.last_mut()
            .and_then(|data| {
                match data.request.duration.is_unbounded() {
                    true => {
                        data.request.duration.end = end_step;
                        Some(())
                    }
                    _ => None
                }
            })
            else { return Err("reservation was bounded") };
        
        self.requests.entry(width)
            .or_default()
            .push(sequence);

        Ok(())
    }

    pub fn build(&mut self) -> Option<Resources> {

        // check that all durations are fully set i.e. no resources are leaked
        for (_, res) in self.checked_out.values() {
            let res = res.last()
                .expect("sequence must have a value");
            panic!("Reservation end is not set: {:?}", res);
        }
        
        let mut requests = self.requests.iter().collect::<Vec<_>>();
        
        // sort lanes from widest to narrowest resource width
        // similar to a coin change problem, we can ensure that the optimal packing is achieved if the largest items are packed first
        requests.sort_by(|(width_l, _), (width_r, _)| width_r.cmp(width_l));
        
        // for (width, lane) in &requests {
        //     println!("{width:?}: {lane:?}")
        // }

        let Some((width, _)) = requests.first()
            else { return None };
        // println!("Starting width: {width:?}");
        let mut resource_lanes = Resources::new(**width);
        for (width, lanes) in requests {
            resource_lanes.next_pass(*width);
            
            lanes.iter().flatten().for_each(|reservation| {
                resource_lanes.reserve(reservation.id, &reservation.request)
            })
        }

        resource_lanes.finalize();
        
        Some(resource_lanes)
    }
}

#[test]
fn test_build_reservations() {
    let mut builder = ReservationBuilder::new();

    let _3 = builder.reserve(ResourceWidth::new(8));

    let _1 = builder.reserve(ResourceWidth::new(8));
    builder.free(_1).unwrap();

    let _2 = builder.reserve(ResourceWidth::new(4));
    let _21 = builder.reserve(ResourceWidth::new(2));
    let _22 = builder.reserve(ResourceWidth::new(2));
    builder.free(_2).unwrap();
    builder.free(_21).unwrap();
    builder.free(_22).unwrap();

    builder.free(_3).unwrap();

    let resources = builder.build().expect("Empty resources");

    println!("Resources: {resources:?}");
}

#[test]
fn bench_tree_append_largest() {
    let mut sum = 0;
    for _ in 0..10 {

        let mut tree = BTreeSet::new();
        let mut values = (1..500).collect::<Vec<_>>();
        values.shuffle(&mut rand::rng());

        
        for i in &values {
            tree.insert(*i);
        }
        
        timed! {
            for i in &values {
                sum += tree.upper_bound(Bound::Included(i)).peek_prev().unwrap_or(&0);
            }
        }
        
        println!("Last: {:?}", tree.last())
    }
    println!("Sum: {sum}")
}

#[test]
fn bench_reservation_map() {
    let mut _1 = Vec::with_capacity(10);
    let mut _2 = Vec::with_capacity(10);

    for _ in 0..1 {
        
        let mut builder = ReservationBuilder::new();

        timed! {
            for i in 1..150 {
    
                _1.push(builder.reserve(ResourceWidth::new(i)));
    
                for j in 1..10 {
                    _2.push(builder.reserve(ResourceWidth::new(j)));
                }
    
                for id in _2.drain(..) {
                    builder.free(id).unwrap();
                }
            }
    
            for id in _1.drain(..) {
                builder.free(id).unwrap();
            }
        }

        let resources = timed! {
            builder.build()
        }.unwrap();
        // println!("Resources: {resources:?}")
    }
}