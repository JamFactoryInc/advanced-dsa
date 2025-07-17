use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use crate::reservation_map::duration::Duration;
use crate::reservation_map::{ReservationId, ResourceWidth};
use crate::reservation_map::resource_block::ResourceBlock;

/// A desired allocation of resources of some minimum width for a given duration
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct PreAllocation
{
    pub width: ResourceWidth,
    pub duration: Duration
}

impl PreAllocation {
    pub fn new(width: ResourceWidth, duration: Duration) -> PreAllocation {
        PreAllocation {
            width,
            duration
        }
    }
    
    pub fn width(&self) -> u32 {
        self.width
    }
    
    pub fn length(&self) -> u32 {
        self.duration.length()
    }
}

impl Debug for PreAllocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{:?}: {:?}-{:?}]", self.width, self.duration.start.0, self.duration.end.0)
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
        other.width.cmp(&self.width)
            .then_with(|| self.duration.start.cmp(&other.duration.start))
    }
}

#[derive(PartialEq, Eq)]
pub struct Allocation {
    pub id: ReservationId,
    pub block: ResourceBlock,
    pub duration: Duration
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