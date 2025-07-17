use std::fmt::{Debug, Formatter};
use std::cmp::Ordering;
use std::ops::{Range, RangeInclusive};
use crate::reservation_map::resource_block::ResourceBlock;
use crate::reservation_map::step::Step;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Duration {
    pub start: Step,
    pub end: Step, // inclusive
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

    pub fn starts_after(&self, other: &Duration) -> bool {
        self.start > other.start
    }

    pub fn ends_before(&self, other: &Duration) -> bool {
        self.end < other.end
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

impl From<RangeInclusive<u32>> for Duration {
    fn from(value: RangeInclusive<u32>) -> Self {
        Duration::new(
            Step(*value.start()),
            Step(*value.end())
        )
    }
}