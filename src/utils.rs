use bimap::BiHashMap;
use fxhash::FxBuildHasher;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::collections::HashSet;
use std::ops::RangeInclusive;

pub type BiMap<L, R> = BiHashMap<L, R, FxBuildHasher, FxBuildHasher>;

pub trait BitSet: Clone + PartialEq + Eq + PartialOrd + Ord {
    type Iter<'a>: Iterator<Item = u32>
    where
        Self: 'a;

    type BitsIter<'a>: Iterator<Item = bool>
        where
            Self: 'a;

    fn full_with_size(bits: usize) -> Self;
    fn power_set(size: usize) -> RangeInclusive<u32>;
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
    fn iter(&self) -> Self::Iter<'_>;
    fn bits(&self, max_index: u32) -> Self::BitsIter<'_>;
    fn len(&self) -> u32 {
        self.iter().count() as u32
    }

    fn into_par_iter(self) -> impl ParallelIterator<Item = u32>;
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

pub struct BitSet32BitsIter<'a> {
    set: &'a BitSet32,
    current_index: u32,
    max_index: u32,
}

impl Iterator for BitSet32BitsIter<'_> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index < self.max_index {
            let bit = self.set & (1 << self.current_index) != 0;
            self.current_index += 1;
            Some(bit)
        } else {
            None
        }
    }
}


impl BitSet for BitSet32 {
    type Iter<'a> = BitSet32Iter<'a>;
    type BitsIter<'a> = BitSet32BitsIter<'a>;
    fn full_with_size(bits: usize) -> Self {
        if bits == 32 {
            Self::MAX
        } else {
            (1 << bits) - 1
        }
    }

    fn power_set(size: usize) -> RangeInclusive<u32> {
        0..=Self::full_with_size(size)
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

    fn iter(&self) -> Self::Iter<'_> {
        Self::Iter {
            set: self,
            current_index: 0,
        }
    }

    fn len(&self) -> u32 {
        self.count_ones()
    }

    fn into_par_iter(self) -> impl ParallelIterator<Item = u32> {
        let mut holder = Vec::with_capacity(32);
        for index in 0..32u32 {
            if self & (1 << index) != 0 {
                holder.push(index);
            }
        }
        holder.into_par_iter()
    }
    
    fn bits(&self, max_index: u32) -> Self::BitsIter<'_> {
        BitSet32BitsIter {
            set: self,
            current_index: 0,
            max_index,
        }
    }
}

pub fn powerset<T: Clone + std::cmp::Eq + std::hash::Hash>(origin: &HashSet<T>) -> Vec<HashSet<T>> {
    let mut result = vec![HashSet::new()];
    for elem in origin.iter() {
        let mut new_subsets = Vec::new();
        for subset in &result {
            let mut new_subset = subset.clone();
            new_subset.insert(elem.clone());
            new_subsets.push(new_subset);
        }
        result.extend(new_subsets);
    }
    result
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn test_powerset() {
        let set = HashSet::from(["a", "b"]);
        let expected = [HashSet::new(),
            HashSet::from(["a"]),
            HashSet::from(["b"]),
            HashSet::from(["a", "b"])];
        let powerset = powerset(&set);
        assert_eq!(powerset.len(), expected.len());
        for set in powerset {
            assert!(expected.contains(&set));
        }
    }
}
