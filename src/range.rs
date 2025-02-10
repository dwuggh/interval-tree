use std::{
    cmp::Ordering,
    fmt::Debug,
    ops::{Bound, Range, RangeBounds},
};

/// a half-open interval in ℕ, [start, end)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd)]
pub struct TextRange {
    pub start: usize,
    pub end: usize,
}

impl Ord for TextRange {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.start.cmp(&other.start) {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.end.cmp(&other.end),
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl RangeBounds<usize> for TextRange {
    fn start_bound(&self) -> Bound<&usize> {
        Bound::Included(&self.start)
    }

    fn end_bound(&self) -> Bound<&usize> {
        Bound::Excluded(&self.start)
    }
}

impl TextRange {
    /// caller should check that start < end
    pub fn new(start: usize, end: usize) -> Self {
        if start <= end {
            Self { start, end }
        } else {
            Self {
                start: end,
                end: start,
            }
        }
    }

    pub fn as_range(&self) -> Range<usize> {
        self.start..self.end
    }

    pub fn contains(&self, pos: usize) -> bool {
        self.start <= pos && pos < self.end
    }

    pub fn strict_order(&self, other: &Self) -> Option<Ordering> {
        if self.end <= other.start {
            return Some(Ordering::Less);
        }
        if self.start >= other.end {
            return Some(Ordering::Greater);
        }
        None
    }
    /// split self, return the split out interval. 
	/// if `left` is true, the left part is split out and returned.
	/// This function does not check whether `position` is valid.
    pub fn split_at(&mut self, position: usize, left: bool) -> Self {
        if left {
            let start = self.start;
            self.start = position;
            Self::new(start, position)
        } else {
            let end = self.end;
            self.end = position;
            Self::new(position, end)
        }
    }

    pub fn intersects(&self, other: Self) -> bool {
        self.end > other.start && self.start < other.end
    }
    pub fn intersection_uncheck(&self, other: Self) -> Self {
        Self::new(self.start.max(other.start), self.end.min(other.end))
    }
    pub fn intersection(&self, other: Self) -> Option<Self> {
        self.intersects(other)
            .then(|| self.intersection_uncheck(other))
    }

    pub fn advance(&mut self, offset: usize) {
        self.start += offset;
        self.end += offset;
    }
    pub fn move_back(&self, offset: usize) -> Self {
        Self::new(self.start + offset, self.end + offset)
    }
}
