use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Bound::Included;
use std::ops::{Add, Deref, Sub};

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
    end: LaneId,
}
impl Allocation {
    pub fn width(&self) -> usize {
        self.end - self.start
    }
}
impl Debug for Allocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[#{:?}-#{:?}]", self.start, self.end)
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

    pub fn is_freed(&self) -> bool {
        self.end.is_set()
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
        Some(self.start.cmp(&other.start))
    }
}
impl Ord for Duration {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
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
        let self_width = self.resource_requirement.width;
        let other_width = self.resource_requirement.width;

        if self_width != other_width {
            // primary sort by width descending
            Some(other_width.cmp(&self_width))
        } else {
            // secondary sort by start step asc for equal resource widths
            Some(self.duration.start.cmp(&other.duration.start))
        }
    }
}
impl Ord for ReservationRequest {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
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
    pub fn is_freed(&self) -> bool {
        self.duration.is_freed()
    }

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
    lanes: BTreeMap<ResourceRequirement, Vec<ResourceLane>>,
}
impl ReservationMap {
    pub fn new() -> Self {
        ReservationMap {
            lanes: BTreeMap::new(),
        }
    }
    
    pub fn initialize_resource_size(&mut self, req: ResourceRequirement) {
        self.lanes.entry(req)
            .or_insert_with(|| vec![ResourceLane::new()]);
    } 
    
    pub fn reserve(&mut self, reservation_id: ReservationId, req: &ReservationRequest) {
        self.lanes.iter_mut()
            .rev()
            .any(|(lane_width, lanes)| {

                let reserved = lanes.iter_mut().any(|lane| {
                    lane.try_reserve(reservation_id, req).is_some()
                });
                if reserved {
                    return true;
                }
                // check if this is the minimum-sized lane that can accommodate the request
                // if so, we have to create a new lane for it
                if lane_width.width == req.resource_requirement.width {
                    let mut new_lane = ResourceLane::new();
                    new_lane.try_reserve(reservation_id, req)
                        .expect("Failed to reserve in new lane");
                    lanes.push(new_lane);
                    return true;
                }
                false
            });
    }
}
impl Debug for ReservationMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ReservationMap:")?;
        for (res_req, lanes) in self.lanes.iter() {
            write!(f, "\n{res_req:?}")?;
            for (lane_idx, lane) in lanes.iter().enumerate() {
                write!(f, "\n    Lane {lane_idx:?}:")?;
                for item in lane.reservations.iter() {
                    write!(f, " {:?}", item.1)?;
                }
            }
        }
        
        Ok(())
    }
}

#[derive(PartialEq, Eq)]
struct SavedReservation(ReservationId, ReservationRequest);
impl PartialOrd for SavedReservation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.1.cmp(&other.1))
    }
}
impl Ord for SavedReservation {
    fn cmp(&self, other: &Self) -> Ordering {
        self.1.cmp(&other.1)
    }
}

/// A structure that tracks vacancies for a given resource width
struct ResourceLane {
    vacancies: BTreeSet<Duration>,
    reservations: BTreeSet<SavedReservation>
}
impl ResourceLane {
    fn new() -> Self {
        let mut vacancies = BTreeSet::new();
        // start with a single vacancy encompassing the entire timeline
        vacancies.insert(Duration::new_unbounded(Step(0)));
        ResourceLane {
            vacancies,
            reservations: BTreeSet::new()
        }
    }

    fn try_reserve(&mut self, reservation_id: ReservationId, req: &ReservationRequest) -> Option<()> {
        let vacancy_starting_before_req = {
            // find a vacancy that can contain the reservation
            let vacancy = self.vacancies.upper_bound(Included(&req.duration));
            
            match vacancy.peek_prev() {
                Some(vacancy_starting_before_req) => {
                    *vacancy_starting_before_req
                },
                _ => {
                    return None
                }, // no vacancy found that can contain the reservation
            }
        };

        let Some((head_margin, tail_margin)) =
            vacancy_starting_before_req.get_margin_around(&req.duration)
            else { return None; }; // the vacancy cannot contain the requested duration
        
        self.vacancies.remove(&vacancy_starting_before_req);
        if head_margin.is_nonzero() {
            self.vacancies.insert(head_margin);
        }
        if tail_margin.is_nonzero() {
            self.vacancies.insert(tail_margin);
        }
        
        self.reservations.insert(SavedReservation(reservation_id, *req));
        
        Some(())
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
            resource_lanes.initialize_resource_size(res.resource_requirement);
            if res.duration.is_unbounded() {
                panic!("Reservation end is not set: {:?}", res);
            }
        }

        println!("Reservation requests: {:?}", self.requests);

        // sort from widest to narrowest resource width, and sort equal widths by step ascending
        // similar to a coin change problem, we can ensure that the optimal packing is achieved if the largest items are packed first
        self.requests.sort_by_key(|(_, res)| *res);

        
        for (res_id, res) in &self.requests {
            resource_lanes.reserve(*res_id, res)
        }

        println!("Reservation Map: {resource_lanes:?}");
    }
}

#[test]
fn test_build_reservations() {
    let mut builder = ReservationBuilder::new();
    
    let _3 = builder.reserve(ResourceRequirement::new(8));
    
    let _1 = builder.reserve(ResourceRequirement::new(8));
    builder.free(_1).unwrap();
    
    let _2 = builder.reserve(ResourceRequirement::new(4));
    builder.free(_2).unwrap();

    builder.free(_3).unwrap();
    
    builder.build()
}