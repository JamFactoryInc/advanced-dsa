use std::fmt::{Debug, Formatter};
use std::ops::Range;
use crate::reservation_map::LaneId;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct ResourceBlock {
    pub start: LaneId,
    pub end: LaneId, // exclusive
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
impl From<Range<u32>> for ResourceBlock {
    fn from(value: Range<u32>) -> Self {
        ResourceBlock::new(
            value.start,
            value.end
        )
    }
}

impl Debug for ResourceBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[#{:?}-#{:?}]", self.start, self.end - 1)
    }
}