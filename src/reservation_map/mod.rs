use core::range;
use std::alloc::{Global, System};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, Bound, HashMap};
use std::collections::btree_set::{CursorMut, UnorderedKeyError};
use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasher, Hash, Hasher, RandomState};
use std::{iter, mem};
use std::ops::Bound::Included;
use std::ops::{Add, Deref, Div, Sub};
use std::slice::Iter;
use std::time::SystemTime;
use rand::prelude::SliceRandom;
use allocation::{Allocation, PreAllocation};
use duration::Duration;
use resource_block::ResourceBlock;
use step::Step;
use vacancy::{Vacancy, VacancySequence};
use crate::reservation_map::vacancy::VacanciesCursor;

mod vacancy;
mod resource_block;
mod step;
mod duration;
mod allocation;

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
        self.0 = (((val >> 16) ^ val).wrapping_mul(0x45d9f3b)) as u64;
    }

    fn write_usize(&mut self, val: usize) {
        self.0 = (((val >> 16) ^ val).wrapping_mul(0x45d9f3b)) as u64;
    }
}

type LaneId = u32;

/// A resource requirement that specifies the width of a contiguous block of resources necessary for a reservation
type ResourceWidth = u32;

#[derive(Copy, Clone, PartialEq, Eq)]
struct ReservationId(u32);
impl Debug for ReservationId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "${:?}", self.0)
    }
}
impl Hash for ReservationId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.0);
    }
}

/// A structure that tracks vacancies for a given resource width
struct Resources {
    // a set of non-overlapping sequences of vacancies
    sequences: Vec<VacancySequence>,
    allocations: Vec<Allocation>,
    width: u32,
}
impl Resources {
    pub fn new(width: ResourceWidth) -> Self {
        // start with a single vacancy encompassing the entire timeline
        let vacancies = VacancySequence::new(Vacancy::new(
            ResourceBlock::new(0, width),
            Duration::new_unbounded(Step(0))
        ));
        
        Resources {
            sequences: vec![vacancies],
            allocations: Vec::new(),
            width,
        }
    }
    
    fn save_alloc(&mut self, res_id: &ReservationId, res_req: &PreAllocation, allocation: &ResourceBlock) {
        self.allocations.push(Allocation::new(res_id, res_req, allocation))
    }
    
    fn reserve_vacancy_or_none(reservation_request: &PreAllocation, vacancy_sequence: &mut VacancySequence) -> Option<ResourceBlock> {
        if !vacancy_sequence.duration_bounds.can_contain(&reservation_request.duration) {
            return None;
        }

        let mut cursor =
            vacancy_sequence.upper_bound_mut(Included(&Vacancy::range(reservation_request.duration)));

        // TODO: make this check subsequent contiguous vacancies
        if !cursor.peek_prev().is_some_and(|vac| vac.can_contain(&reservation_request)) {
            return None;
        }

        let reserved_vac = cursor.remove_prev()
            .expect("Already checked for previous vacancy");

        reserved_vac.get_margin_around(&reservation_request)
            .inspect(|margins| cursor.insert_margins(margins));

        let alloc = reserved_vac.get_allocation_for(&reservation_request);
        Some(alloc)
    }

    /// reserves the request, returning the allocation that was reserved
    pub fn reserve_vacancies_non_overlapping(&mut self, non_overlapping: &[ReservationData]) {

        let mut self_sequences = Vec::new();
        mem::swap(&mut self.sequences, &mut self_sequences);
        
        let mut iter = non_overlapping.iter().peekable();
        
        while let Some(data) = iter.next() {
            let res_id = &data.id;
            let reservation_request = &data.request;
            let allocated_vacancy = self_sequences.iter_mut()
                .find_map(|sequence| Self::reserve_vacancy_or_none(reservation_request, sequence));

            if let Some(ref allocation) = allocated_vacancy {
                self.save_alloc(&res_id, &reservation_request, &allocation);
                continue;
            }

            // create a new unbounded vacancy of the given width, since the value couldn't fit in the existing vacancies
            let allocated_vacancy = self.allocate_new_vacancy(reservation_request.width);
            let allocation = &allocated_vacancy.get_allocation_for(&reservation_request);
            self.save_alloc(res_id, reservation_request, allocation);

            // the vacancy was made to be the same width as the request, so there shouldn't be any vertical margin
            let (left, right, _) = allocated_vacancy.get_margin_around(&reservation_request)
                .expect("Unbounded vacancy that cannot contain the reservation request");

            let mut new_vacancies = VacancySequence::new(right);
            let mut cursor = new_vacancies.upper_bound_mut(Bound::Excluded(&right));

            if left.is_non_empty() {
                cursor.insert_before(left).expect("Failed to insert left margin");
            }

            // greedily consume the unbounded vacancy until we run out of reservations
            // we can do this since each slice passed to this function is non-overlapping!
            cursor.next();
            while let Some(data) = iter.next() {
                let reservation_request = &data.request;
                let removed_tail = cursor.remove_prev()
                    .expect("tail did not exist");

                removed_tail.get_margin_around(&reservation_request)
                    .inspect(|margins| cursor.insert_margins(margins));

                let allocation = &removed_tail.get_allocation_for(&reservation_request);
                self.save_alloc(&data.id, reservation_request, allocation);
            }

            self_sequences.push(new_vacancies);
        }

        mem::swap(&mut self.sequences, &mut self_sequences);
    }

    pub fn finalize(&mut self) {
        self.allocations.sort()
    }
    
    fn allocate_new_vacancy(&mut self, resource_requirement: ResourceWidth) -> Vacancy {
        // create a new vacancy that encompasses the entire timeline
        let new_vacancy = Vacancy::new(
            ResourceBlock::new(0, resource_requirement).offset_by(self.width),
            Duration::new_unbounded(Step(0))
        );
        self.width += resource_requirement;
        new_vacancy
    }

    /// Attempts to reserve the given reservation request in the lane
    ///
    /// If a vacancy is found that can accommodate the reservation, it will be reserved and split into multiple smaller vacancies making up the margins.
    fn reserve_non_overlapping(&mut self, non_overlapping: &[ReservationData]) {
        // find a vacancy that can contain the reservation, and reserve it
        // also tracks the resulting margins
        self.reserve_vacancies_non_overlapping(non_overlapping);
    }
}
impl Debug for Resources {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Max concurrent width: {}", self.width)?;
        let mut max_lane = self.allocations.iter()
            .map(|alloc| alloc.block.end)
            .max()
            .unwrap_or(0) - 1;

        fn unique(reservation_id: ReservationId) -> String {
            let val = reservation_id.0;
            char::from_u32(match val {
                0..10 => val + '0' as u32,
                10..36 => val - 10 + 'a' as u32,
                36..62 => val - 36 + 'A' as u32,
                _ => b'?' as u32
            }).unwrap().to_string()
        }

        for lane in 0..=max_lane {
            write!(f, "\n#{lane:<2}: ")?;
            let mut end_of_prev = 0;

            for res in &self.allocations {
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

#[derive(Debug, Copy, Clone)]
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
    checked_out: HashMap<ReservationId, (ResourceWidth, Vec<ReservationData>), SimpleHasher>,
    requests: HashMap<ResourceWidth, Vec<Vec<ReservationData>>, SimpleHasher>,
    step: Step,
    id_counter: u32
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
        self.check_out(&ReservationData::new(id, request));
        id
    }

    pub fn free(&mut self, id: ReservationId) -> Result<(), &str> {
        let end_step = self.step.get_and_increment();
        self.un_check_out(id, end_step)
    }

    fn check_out(&mut self, rsvn: &ReservationData) {
        let width = rsvn.request.width;
        let mut sequence = self.requests.get_mut(&width)
            .and_then(|lane| lane.pop())
            .unwrap_or_else(|| vec![]);

        let id = rsvn.id;
        sequence.push(*rsvn);
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

        let mut requests = self.requests.iter()
            .collect::<Vec<_>>();

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
        for (_, lanes) in requests {
            lanes.iter().for_each(|non_overlapping| {
                resource_lanes.reserve_non_overlapping(non_overlapping.as_slice())
            });
        }

        resource_lanes.finalize();

        Some(resource_lanes)
    }
}

#[test]
fn test_build_reservations_simple() {
    let mut builder = ReservationBuilder::new();

    let _0 = builder.reserve(8);

    // let _1 = builder.reserve(8);
    // builder.free(_1).unwrap();

    builder.free(_0).unwrap();

    let resources = builder.build().expect("Empty resources");

    println!("Resources: {resources:?}");
}

#[test]
fn test_build_reservations() {
    let mut builder = ReservationBuilder::new();

    let _0 = builder.reserve(8);

    let _1 = builder.reserve(8);
    builder.free(_1).unwrap();

    let _2 = builder.reserve(4);
    let _3 = builder.reserve(2);
    let _4 = builder.reserve(2);
    builder.free(_2).unwrap();
    builder.free(_3).unwrap();
    builder.free(_4).unwrap();

    builder.free(_0).unwrap();

    let resources = builder.build().expect("Empty resources");

    println!("Resources: {resources:?}");
}

#[test]
fn test_large_reservation_map() {
    let mut _1 = Vec::with_capacity(10);
    let mut _2 = Vec::with_capacity(10);

    let mut i = 0;
    let sizes = [1, 2, 3, 4];
    let mut sizes = iter::repeat_with(move || {
        i = (i + 1) % sizes.len();
        sizes[i]
    });

    let mut builder = ReservationBuilder::new();

        for _ in 1..5 {

            _1.push(builder.reserve(sizes.next().unwrap()));

            for _ in 1..5 {
                _2.push(builder.reserve(sizes.next().unwrap()));
            }

            for id in _2.drain(..) {
                builder.free(id).unwrap();
            }
        }

        for id in _1.drain(..) {
            builder.free(id).unwrap();
        }


    println!("Packing...");
    let resources = timed! {
        builder.build()
    }.unwrap();
    println!("{resources:?}")

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
    let mut _1 = Vec::with_capacity(200);
    let mut _2 = Vec::with_capacity(200);

    let mut x = 0u32;
    let mut sizes = iter::repeat_with(move || {
        x = (x % 10) + 1;
        x
    });

    for _ in 0..10 {

        let mut builder = ReservationBuilder::new();

        timed! {
            for _ in 1..200 {

                _1.push(builder.reserve(sizes.next().unwrap()));

                for _ in 1..200 {
                    _2.push(builder.reserve(sizes.next().unwrap()));
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