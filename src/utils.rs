
pub trait BitSet: Clone + PartialEq + Eq + PartialOrd + Ord {
    type Iter<'a>: Iterator<Item = u32>
    where
        Self: 'a;

    fn full_with_size(bits: usize) -> Self;
    fn get(&self, index: u32) -> bool;
    fn set_bit(&mut self, index: u32);
    fn clear_bit(&mut self, index: u32);
    fn set(&mut self, index: u32, value: bool) {
        if value {
            self.set_bit(index);
        } else {
            self.clear_bit(index);
        }
    }

    fn contains(&self, index: u32) -> bool {
        self.get(index)
    }
    fn is_subset(&self, other: &Self) -> bool;
    fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }
    fn intersection(&self, other: &Self) -> Self;
    fn union(&self, other: &Self) -> Self;
    fn iter<'a>(&'a self) -> Self::Iter<'a>;
    fn len(&self) -> u32 {
        self.iter().count() as u32
    }
}

pub type BitSet32 = u32;

pub struct BitSet32Iter<'a> {
    set: &'a BitSet32,
    current_index: u32,
}

impl Iterator for BitSet32Iter<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        while self.current_index < 32 {
            if self.set & (1 << self.current_index) != 0 {
                let current_index = self.current_index;
                self.current_index += 1;
                return Some(current_index);
            } else {
                self.current_index += 1;
            }
        }
        None
    }
}

impl BitSet for BitSet32 {
    type Iter<'a> = BitSet32Iter<'a>;

    fn full_with_size(bits: usize) -> Self {
        if bits == 32 {
            Self::MAX
        } else {
            (1 << bits) - 1
        }
    }

    fn get(&self, index: u32) -> bool {
        debug_assert!(index < 32);
        self & (1 << index) != 0
    }

    fn set_bit(&mut self, index: u32) {
        debug_assert!(index < 32);
        *self |= 1 << index;
    }

    fn clear_bit(&mut self, index: u32) {
        debug_assert!(index < 32);
        *self &= !(1 << index);
    }

    fn intersection(&self, other: &Self) -> Self {
        *self & *other
    }

    fn union(&self, other: &Self) -> Self {
        *self | *other
    }

    fn is_subset(&self, other: &Self) -> bool {
        BitSet::intersection(self, other) == *self
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a> {
        Self::Iter {
            set: self,
            current_index: 0,
        }
    }

    fn len(&self) -> u32 {
        self.count_ones()
    }
}
