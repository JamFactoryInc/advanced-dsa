use core::range;
use std::alloc::System;
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Bound::Included;
use std::ops::{Add, Deref, Div, Sub};
use std::time::SystemTime;

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

type LaneId = usize;

/// A resource requirement that specifies the width of a contiguous block of resources necessary for a reservation
#[derive(Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
struct ResourceRequirement {
    width: usize,
}
impl Debug for ResourceRequirement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<-{}->", self.width)
    }
}
impl ResourceRequirement {
    pub fn new(width: usize) -> Self {
        ResourceRequirement { width }
    }
}
impl Hash for ResourceRequirement {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.width);
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct Allocation {
    start: LaneId,
    end: LaneId, // exclusive
}
impl Allocation {
    pub fn new(start: LaneId, end: LaneId) -> Self {
        Allocation { start, end }
    }

    pub fn width(&self) -> usize {
        self.end - self.start
    }

    pub fn offset_by(&self, offset: usize) -> Self {
        Allocation {
            start: self.start + offset,
            end: self.end + offset,
        }
    }
}
impl Debug for Allocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[#{:?}-#{:?}]", self.start, self.end - 1)
    }
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
struct Step(usize);
impl Step {
    pub const UNSET: Step = Step(usize::MAX);

    pub fn is_set(&self) -> bool {
        self.0 != usize::MAX
    }

    pub fn is_unset(&self) -> bool {
        self.0 == usize::MAX
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
    end: Step,
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

    pub fn length(&self) -> usize {
        if self.end.is_unset() {
            usize::MAX
        } else {
            self.end.0 - self.start.0
        }
    }

    pub fn is_nonzero(&self) -> bool {
        self.start != self.end
    }

    pub fn is_unbounded(&self) -> bool {
        self.end.is_unset()
    }

    pub fn overlaps(&self, other: &Duration) -> bool {
        self.start < other.end && other.start < self.end
    }

    pub fn can_contain(&self, other: &Duration) -> bool {
        self.start <= other.start && self.end >= other.end
    }

    pub fn get_margin_around(&self, other: &Duration) -> Option<(Duration, Duration)> {
        if self.can_contain(other) {
            let left_margin = Duration::new(self.start, Step::clamp_before(self.start, other.start));
            let right_margin = Duration::new(Step::clamp_after(other.end, self.end),  self.end);
            Some((left_margin, right_margin))
        } else {
            None
        }

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

#[derive(Copy, Clone, PartialEq, Eq)]
struct ReservationRequest
{
    resource_requirement: ResourceRequirement,
    duration: Duration
}
impl ReservationRequest {
    pub fn width(&self) -> usize {
        self.resource_requirement.width
    }
    pub fn length(&self) -> usize {
        self.duration.length()
    }
}
impl Debug for ReservationRequest {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{:?}: {:?}-{:?}]", self.resource_requirement.width, self.duration.start.0, self.duration.end.0)
    }
}
impl PartialOrd for ReservationRequest {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // primary sort by width descending
        // secondary sort by start step asc for equal resource widths
        Some(self.cmp(other))
    }
}
impl Ord for ReservationRequest {
    fn cmp(&self, other: &Self) -> Ordering {
        other.resource_requirement.width.cmp(&self.resource_requirement.width)
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

#[derive(Copy, Clone, PartialEq, Eq)]
struct Reservation
{
    allocation: Allocation,
    duration: Duration
}
impl Reservation {
    pub fn overlaps(&self, other: &Reservation) -> bool {
        self.duration.overlaps(&other.duration)
    }
}
impl PartialOrd for Reservation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let self_width = self.allocation.width();
        let other_width = other.allocation.width();

        if self_width != other_width {
            // primary sort by width descending
            Some(self_width.cmp(&other_width).reverse())
        } else {
            // secondary sort by start step asc for equal resource widths
            Some(self.duration.start.cmp(&other.duration.start))
        }
    }
}
impl Ord for Reservation {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}

struct ReservationMap {
    lanes: Vec<ResourceLane>,
}
impl ReservationMap {
    pub fn new() -> Self {
        ReservationMap {
            lanes: Vec::new(),
        }
    }

    pub fn reserve(&mut self, reservation_id: ReservationId, req: &ReservationRequest) {
        let reserved = self.lanes.iter_mut().any(|lane| {
            lane.try_reserve(reservation_id, req).is_some()
        });
        if reserved {
            return;
        }

        let mut new_lane = ResourceLane::new(req.resource_requirement);
        new_lane.try_reserve(reservation_id, req)
            .expect("Failed to reserve in new lane");
        self.lanes.push(new_lane);
    }
}
impl Debug for ReservationMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ReservationMap:")?;
        for (lane_idx, lane) in self.lanes.iter().enumerate() {
            // write!(f, "\n\nLane {lane_idx:?}:")?;
            write!(f, "{lane:?}")?;
        }

        Ok(())
    }
}

#[derive(PartialEq, Eq)]
struct SavedReservation {
    res_id: ReservationId,
    allocation: Allocation,
    res_req: ReservationRequest
}
impl SavedReservation {
    pub fn new(res_id: ReservationId, res_req: ReservationRequest, allocation: Allocation) -> Self {
        SavedReservation {
            res_id,
            res_req,
            allocation,
        }
    }
}
impl Debug for SavedReservation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} -> {:?} {:?}", self.res_id, self.allocation, self.res_req.duration)
    }
}
impl PartialOrd for SavedReservation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}
impl Ord for SavedReservation {
    fn cmp(&self, other: &Self) -> Ordering {
        self.res_req.duration.cmp(&other.res_req.duration)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct Vacancy {
    duration: Duration,
    available_resources: Allocation,
}
impl Vacancy {
    pub fn new(allocation: Allocation, duration: Duration) -> Self {
        Vacancy {
            duration,
            available_resources: allocation,
        }
    }

    pub fn empty() -> Self {
        Vacancy {
            duration: Duration::new(Step(0), Step(0)),
            available_resources: Allocation::new(0, 0),
        }
    }

    pub fn range(duration: Duration) -> Self {
        Vacancy {
            duration,
            available_resources: Allocation::new(0, 0),
        }
    }

    pub fn length(&self) -> usize {
        self.duration.length()
    }

    pub fn width(&self) -> usize {
        self.available_resources.width()
    }

    pub fn can_contain(&self, other: &ReservationRequest) -> bool {
        self.duration.can_contain(&other.duration) && self.width() >= other.width()
    }

    /// empty vacancies can be returned from calculating margin after allocation
    ///
    /// this returns true if the vacancy is a non-zero width and a non-zero length
    ///
    /// otherwise, the vacancy should be discarded
    pub fn is_non_empty(&self) -> bool {
        self.duration.is_nonzero() && self.available_resources.width() > 0
    }

    pub fn get_allocation_for(&self, res_request: &ReservationRequest) -> Allocation {
        let start = self.available_resources.start;
        let end = start + res_request.width();
        Allocation::new(start, end)
    }

    /// returns the left, right, and vertical margins around the given resource request
    ///
    /// if the vertical margin is smaller than the requested resource width, then it should be added to a buffer and added once the pass width is <= the margin width
    /// this is to ensure that vacancies can accommodate the requested width in this pass
    pub fn get_margin_around(&self, res_request: &ReservationRequest) -> Option<(Vacancy, Vacancy, Vacancy)> {
        if !self.duration.can_contain(&res_request.duration) || self.width() < res_request.width() {
            return None
        }

        let left_duration = Duration::new(self.duration.start, Step::clamp_before(self.duration.start, res_request.duration.start));
        let right_duration = Duration::new(Step::clamp_after(res_request.duration.end, self.duration.end), self.duration.end);

        let left_margin = Vacancy {
            duration: left_duration,
            available_resources: self.available_resources,
        };
        let right_margin = Vacancy {
            duration: right_duration,
            available_resources: self.available_resources,
        };
        let vertical_margin = Vacancy {
            duration: self.duration,
            available_resources: Allocation::new(
                self.available_resources.start.add(res_request.width()),
                self.available_resources.end,
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


/// A structure that tracks vacancies for a given resource width
struct ResourceLane {
    // a set of non-overlapping sequences of vacancies
    vacancies: Vec<BTreeSet<Vacancy>>,
    reservations: Vec<SavedReservation>,
    next_pass_vacancies: Vec<Vacancy>,
    width: usize,
}
impl ResourceLane {
    pub fn new(width: ResourceRequirement) -> Self {
        // start with a single vacancy encompassing the entire timeline
        let vacancies = BTreeSet::from([
            Vacancy::new(
                Allocation::new(0, width.width),
                Duration::new_unbounded(Step(0))
            )
        ]);
        
        ResourceLane {
            vacancies: vec![vacancies],
            reservations: Vec::new(),
            next_pass_vacancies: Vec::new(),
            width: width.width,
        }
    }

    /// attempts to reserve the request, returning the allocation that was reserved if successful
    pub fn try_reserve_vacancy(&mut self, reservation_request: ReservationRequest) -> Option<Allocation> {
        let vertical_margin = self.vacancies.iter_mut()
            .find_map(|sequence| {
                let mut found_spot = unsafe {
                    sequence.upper_bound_mut(Included(&Vacancy::range(reservation_request.duration)))
                };

                found_spot.peek_prev()
                    .filter(|vac| vac.can_contain(&reservation_request))
                    .map(|_| ())
                    .and_then(|_| found_spot.remove_prev())
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

        if let Some((allocation, vertical_margin)) = vertical_margin {
            if vertical_margin.is_non_empty() {

                if vertical_margin.width() >= reservation_request.width() {
                    // println!("Tracking vertical margin: {:?}", vertical_margin);
                    if vertical_margin.duration.is_unbounded() {
                        self.vacancies.push(BTreeSet::from([vertical_margin]))
                    } else {
                        self.track_vacancy(vertical_margin);
                    }
                } else {
                    // println!("Deferring vertical margin: {:?}", vertical_margin);
                    self.next_pass_vacancies.push(vertical_margin);
                }
            }
            Some(allocation)
        } else {
            let allocated_vacancy = self.allocate_new_vacancy(reservation_request.resource_requirement);
            let allocation = allocated_vacancy.get_allocation_for(&reservation_request);
            let (left, right, vertical) = allocated_vacancy.get_margin_around(&reservation_request)
                .expect("Unbounded vacancy that cannot contain the reservation request");
            
            let mut set = BTreeSet::new();
            let mut cursor = unsafe {
                set.upper_bound_mut(Included(&allocated_vacancy))
            };

            let mut inserted = false;
            if left.is_non_empty() {
                cursor.insert_before(left).expect("Failed to insert left margin");
                inserted = true;
            }
            if right.is_non_empty() {
                cursor.insert_after(right).expect("Failed to insert right margin");
                inserted = true;
            }
            
            if vertical.is_non_empty() {
                if vertical.width() >= reservation_request.width() {
                    if !inserted {
                        cursor.insert_after(vertical).expect("Failed to insert vertical margin");
                    } else {
                        self.vacancies.push(BTreeSet::from([vertical]))
                    }
                } else {
                    if !inserted {
                        cursor.insert_after(vertical).expect("Failed to insert vertical margin");
                    } else {
                        self.next_pass_vacancies.push(vertical);
                    }
                }
            }
            
            Some(allocation)
        }
    }

    /// indicates that all subsequent accesses to this lane will have the given resource width or less
    ///
    /// this instructs the lane to make vacancies available that were not large enough to accommodate resources in the previous pass
    pub fn next_pass(&mut self, pass_req: ResourceRequirement) {
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

    pub fn finalize(&mut self) {
        self.reservations.sort()
    }
    
    fn allocate_new_vacancy(&mut self, resource_requirement: ResourceRequirement) -> Vacancy {
        // create a new vacancy that encompasses the entire timeline
        let new_vacancy = Vacancy::new(
            Allocation::new(0, resource_requirement.width).offset_by(self.width),
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

        let mut tracked = false;
        for sequence in self.vacancies.iter_mut() {
            // find a vacancy that can contain the reservation
            let mut found_spot = unsafe {
                sequence.upper_bound_mut(Included(&vacancy))
            };

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
            self.vacancies.push(BTreeSet::from([
                vacancy
            ]));
        }
    }

    /// Attempts to reserve the given reservation request in the lane
    ///
    /// If a vacancy is found that can accommodate the reservation, it will be reserved and split into multiple smaller vacancies making up the margins.
    fn try_reserve(&mut self, reservation_id: ReservationId, req: &ReservationRequest) -> Option<()> {
        // find a vacancy that can contain the reservation, and reserve it
        // also tracks the resulting margins
        self.try_reserve_vacancy(*req).inspect(|allocation| {
            // if the reservation was successfully reserved, we need to save it
            self.reservations.push(
                SavedReservation::new(
                    reservation_id,
                    *req,
                    *allocation
                )
            );
        }).map(|_| ())
    }
}
impl Debug for ResourceLane {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut max_lane = self.reservations.iter()
            .map(|alloc| alloc.allocation.end)
            .max()
            .unwrap_or(0) - 1;

        fn unique(reservation_id: ReservationId) -> String {
            char::from_u32(reservation_id.0 as u32 + '0' as u32).unwrap().to_string()
        }

        for lane in 0..=max_lane {
            write!(f, "\n#{lane}: ")?;
            let mut end_of_prev = 0;

            for res in &self.reservations {
                if res.allocation.start <= lane && res.allocation.end > lane {
                    println!("{res:?} dur start: {}, end of prev: {}", res.res_req.duration.start.0, end_of_prev);
                    let gap_len = res.res_req.duration.start.0 - end_of_prev;
                    write!(f, "{}", " ".repeat(gap_len))?;
                    write!(f, "{}", unique(res.res_id).repeat(res.res_req.length()))?;
                    end_of_prev = res.res_req.duration.end.0;
                }
            }
        }

        Ok(())
    }
}

/// the structure used to collect reservations before they are packed into the reservation map
struct ReservationBuilder {
    step: Step,
    // used to look up a reservation index from its external id
    requests: Vec<(ReservationId, ReservationRequest)>,
}
impl ReservationBuilder {
    pub fn new() -> Self {
        ReservationBuilder {
            step: Step(0),
            requests: vec![],
        }
    }

    pub fn reserve(&mut self, req: ResourceRequirement) -> ReservationId {
        let id = ReservationId(self.requests.len());
        let request = ReservationRequest {
            resource_requirement: req,
            duration: Duration::new_unbounded(self.step.get_and_increment()),
        };
        self.requests.push((id, request));
        id
    }

    pub fn free(&mut self, id: ReservationId) -> Result<(), ()> {
        let Some(request) = self.requests.get_mut(id.0)
            else { return Err(()) };
        if request.1.duration.is_unbounded() {
            request.1.duration.end = self.step.get_and_increment();
            Ok(())
        } else { Err(()) }
    }

    pub fn build(&mut self) {
        let mut resource_lanes = ReservationMap::new();

        // check that all durations are fully set i.e. no resources are leaked
        for (_, res) in &self.requests {
            if res.duration.is_unbounded() {
                panic!("Reservation end is not set: {:?}", res);
            }
        }
        

        // println!("Reservation requests: {:?}", self.requests);

        // sort from widest to narrowest resource width, and sort equal widths by step ascending
        // similar to a coin change problem, we can ensure that the optimal packing is achieved if the largest items are packed first
        self.requests.sort_by_key(|(_, res)| *res);
        
        

        let Some((_, first)) = self.requests.first()
            else { return };
        let mut width = first.width();

        
        for (res_id, res) in &self.requests {
            if res.width() < width {
                width = res.width();
                
                resource_lanes.lanes.iter_mut().for_each(|lane| {
                    lane.next_pass(ResourceRequirement::new(width));
                });
            }

            resource_lanes.reserve(*res_id, res);
        }

        // resource_lanes.lanes.iter_mut().for_each(|lane| {
        //     lane.finalize();
        // });

        // println!("Reservation Map: {resource_lanes:?}");
    }
}

#[test]
fn test_build_reservations() {
    let mut builder = ReservationBuilder::new();

    let _3 = builder.reserve(ResourceRequirement::new(8));

    let _1 = builder.reserve(ResourceRequirement::new(8));
    builder.free(_1).unwrap();

    let _2 = builder.reserve(ResourceRequirement::new(4));
    let _21 = builder.reserve(ResourceRequirement::new(2));
    let _22 = builder.reserve(ResourceRequirement::new(2));
    builder.free(_2).unwrap();
    builder.free(_21).unwrap();
    builder.free(_22).unwrap();

    builder.free(_3).unwrap();

    builder.build()
}

#[test]
fn bench_reservation_map() {
    let mut _1 = Vec::with_capacity(10);
    let mut _2 = Vec::with_capacity(10);

    for _ in 0..10 {
        let mut builder = ReservationBuilder::new();

        for i in 1..150 {

            _1.push(builder.reserve(ResourceRequirement::new(i)));

            for j in 1..10 {
                _2.push(builder.reserve(ResourceRequirement::new(j)));
            }

            for id in _2.drain(..) {
                builder.free(id).unwrap();
            }
        }

        for id in _1.drain(..) {
            builder.free(id).unwrap();
        }

        timed! {
            builder.build();
        }
    }
}