use std::ops::{Add, Sub};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub struct Step(pub u32);

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

    pub fn get_and_increment(&mut self) -> Step {
        let step = self.0;
        self.0 += 1;
        Step(step)
    }
}

impl Sub for Step {
    type Output = Step;
    fn sub(self, rhs: Self) -> Self::Output {
        Step(self.0.sub(rhs.0))
    }
}

impl Add for Step {
    type Output = Step;
    fn add(self, rhs: Self) -> Self::Output {
        Step(self.0.add(rhs.0))
    }
}