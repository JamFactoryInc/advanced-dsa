use std::assert_matches::{assert_matches, debug_assert_matches};
use std::cmp::{Ordering};
use std::ops::Add;
use std::collections::btree_map::UnorderedKeyError;
use std::collections::{BTreeSet, Bound};
use std::collections::btree_set::CursorMut;
use crate::reservation_map::allocation::PreAllocation;
use crate::reservation_map::duration::Duration;
use crate::reservation_map::resource_block::ResourceBlock;
use crate::reservation_map::step::Step;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Vacancy {
    /// represents the duration for which the associated resources are unused
    pub duration: Duration,
    /// represents the vacant resources
    pub block: ResourceBlock,
}

impl Vacancy {
    pub fn new(allocation: ResourceBlock, duration: Duration) -> Self {
        Vacancy {
            duration,
            block: allocation,
        }
    }

    pub fn range(duration: Duration) -> Self {
        Vacancy {
            duration,
            block: ResourceBlock::new(0, 0),
        }
    }

    pub fn width(&self) -> u32 {
        self.block.width()
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
        self.duration.is_nonzero() && self.block.width() > 0
    }

    pub fn get_allocation_for(&self, res_request: &PreAllocation) -> ResourceBlock {
        let start = self.block.start;
        let end = start + res_request.width();
        ResourceBlock::new(start, end)
    }

    /// returns the left, right, and vertical margins around the given resource request
    ///
    /// vertical vacancies have the same width as the given PreAllocation, meaning the returned vacancies are non-overlapping
    ///
    /// if the vertical margin is smaller than the requested resource width, then it should be added to a buffer and added once the pass width is <= the margin width
    /// this is to ensure that vacancies can accommodate the requested width in this pass
    pub fn get_margin_around(&self, res_request: &PreAllocation) -> Option<(Vacancy, Vacancy, Vacancy)> {
        if !self.can_contain(res_request) {
            return None
        }

        let left_duration = Duration::new(self.duration.start, Step::clamp_before(self.duration.start, res_request.duration.start));
        let right_duration = Duration::new(Step::clamp_after(res_request.duration.end, self.duration.end), self.duration.end);

        let left_margin = Vacancy {
            duration: left_duration,
            block: self.block,
        };
        let right_margin = Vacancy {
            duration: right_duration,
            block: self.block,
        };
        let vertical_margin = Vacancy {
            duration: res_request.duration,
            block: ResourceBlock::new(
                self.block.start.add(res_request.width()),
                self.block.end,
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

pub struct VacanciesCursor<'a> {
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

    pub fn next(&mut self) -> Option<&Vacancy> {
        self.cursor.next()
    }

    pub fn remove_next(&mut self) -> Option<Vacancy> {
        self.cursor.remove_next()
            .inspect(|value| self.update_bounding_box_post_remove(&value.duration))
    }

    pub fn remove_prev(&mut self) -> Option<Vacancy> {
        self.cursor.remove_prev()
            .inspect(|value| self.update_bounding_box_post_remove(&value.duration))
    }

    fn update_bounding_box_post_remove(&mut self, removed: &Duration) {
        if removed.start == self.bounding_box.start {
            self.bounding_box.start = removed.end
        } else if removed.end == self.bounding_box.end {
            self.bounding_box.end = removed.start
        }
    }

    fn update_bounding_box_post_insert(&mut self, inserted_dur: &Duration) {
        self.bounding_box.start = self.bounding_box.start.min(inserted_dur.start);
        self.bounding_box.end = self.bounding_box.end.max(inserted_dur.end);
    }

    pub fn insert_before(&mut self, value: Vacancy) -> Result<(), UnorderedKeyError> {
        self.cursor.insert_before(value)
            .inspect(|_| self.update_bounding_box_post_insert(&value.duration))
    }

    pub fn insert_after(&mut self, value: Vacancy) -> Result<(), UnorderedKeyError> {
        self.cursor.insert_after(value)
            .inspect(|_| self.update_bounding_box_post_insert(&value.duration))
    }
    
    pub fn insert_margins(&mut self, margins: &(Vacancy, Vacancy, Vacancy)) {
        let (left, right, vertical) = *margins;
        if left.is_non_empty() {
            self.insert_before(left).expect("Failed to insert left margin");
        }
        if vertical.is_non_empty() {
            self.insert_before(vertical).expect("Failed to insert vertical margin");
        }
        if right.is_non_empty() {
            self.insert_before(right).expect("Failed to insert right margin");
        }
    }
}

#[derive(Debug)]
pub struct VacancySequence {
    vacancies: BTreeSet<Vacancy>,
    // the min and max possible values of this vacancy sequence
    pub duration_bounds: Duration
}

impl VacancySequence {
    pub fn new(vacancy: Vacancy) -> Self {
        VacancySequence {
            vacancies: BTreeSet::from([vacancy]),
            duration_bounds: vacancy.duration
        }
    }

    pub fn upper_bound_mut(&mut self, bound: Bound<&Vacancy>) -> VacanciesCursor<'_> {
        let VacancySequence {
            vacancies,
            duration_bounds: step_bounding_box
        } = self;

        VacanciesCursor {
            cursor: unsafe { vacancies.upper_bound_mut(bound) },
            bounding_box: step_bounding_box,
        }
    }
}


#[test]
fn test_vacancy_margin_no_margin() {
    let vac = Vacancy::new(
        (0..3).into(),
        (0..=5).into()
    );
    
    let pre_alloc = PreAllocation::new(3, (0..=5).into());
    
    let (left, right, vertical) = vac.get_margin_around(&pre_alloc)
        .expect("Vacancy should be able to fit allocation of same size");
    
    assert_matches!(left.is_non_empty(), false);
    assert_matches!(left.width(), 3);
    assert_matches!(left.duration.start, Step(0));
    assert_matches!(left.duration.end, Step(0));
    
    assert_matches!(right.is_non_empty(), false);
    assert_matches!(right.width(), 3);
    assert_matches!(right.duration.start, Step(5));
    assert_matches!(right.duration.end, Step(5));
    
    assert_matches!(vertical.is_non_empty(), false);
    assert_matches!(vertical.width(), 0);
    assert_matches!(vertical.duration.start, Step(0));
    assert_matches!(vertical.duration.end, Step(5));
    
}

#[test]
fn test_vacancy_margin_single_step_margin_is_empty() {
    let vac = Vacancy::new(
        (0..3).into(),
        (0..=5).into()
    );

    let pre_alloc = PreAllocation::new(2, (1..=4).into());

    let (left, right, vertical) = vac.get_margin_around(&pre_alloc)
        .expect("Vacancy should be able to fit allocation of same size");

    assert_matches!(left.is_non_empty(), false);
    assert_matches!(left.width(), 3);
    assert_matches!(left.duration.start, Step(0));
    assert_matches!(left.duration.end, Step(0));

    assert_matches!(right.is_non_empty(), false);
    assert_matches!(right.width(), 3);
    assert_matches!(right.duration.start, Step(5));
    assert_matches!(right.duration.end, Step(5));

    assert_matches!(vertical.is_non_empty(), true);
    assert_matches!(vertical.width(), 1);
    assert_matches!(vertical.duration.start, Step(1));
    assert_matches!(vertical.duration.end, Step(4));

}

#[test]
fn test_vacancy_margin_margin_all_sides() {
    let vac = Vacancy::new(
        (0..3).into(),
        (0..=5).into()
    );

    let pre_alloc = PreAllocation::new(2, (2..=3).into());

    let (left, right, vertical) = vac.get_margin_around(&pre_alloc)
        .expect("Vacancy should be able to fit allocation of same size");

    assert_matches!(left.is_non_empty(), true);
    assert_matches!(left.width(), 3);
    assert_matches!(left.duration.start, Step(0));
    assert_matches!(left.duration.end, Step(1));

    assert_matches!(right.is_non_empty(), true);
    assert_matches!(right.width(), 3);
    assert_matches!(right.duration.start, Step(4));
    assert_matches!(right.duration.end, Step(5));

    assert_matches!(vertical.is_non_empty(), true);
    assert_matches!(vertical.width(), 1);
    assert_matches!(vertical.duration.start, Step(2));
    assert_matches!(vertical.duration.end, Step(3));

}
