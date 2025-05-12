use bimap::BiHashMap;
use dashmap::DashMap;
use fxhash::FxBuildHasher;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::{
    collections::{HashMap, HashSet},
    ops::RangeInclusive,
};

use crate::automata::hoa::AbstractLabelExpression;

// use crate::automata::hoa::AbstractLabelExpression;

pub type Map<K, V> = HashMap<K, V, FxBuildHasher>;

pub type ConcurrentMap<K, V> = DashMap<K, V, FxBuildHasher>;

pub type Set<T> = HashSet<T, FxBuildHasher>;

pub type BiMap<L, R> = BiHashMap<L, R, FxBuildHasher, FxBuildHasher>;

pub trait BitSet: Clone + PartialEq + Eq + PartialOrd + Ord {
    type Iter<'a>: Iterator<Item = u32>
    where
        Self: 'a;

    type BitsIter<'a>: Iterator<Item = bool>
    where
        Self: 'a;

    fn full_with_size(bits: usize) -> Self;
    fn power_set_of_size(size: usize) -> RangeInclusive<u32>;
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
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn into_par_iter(self) -> impl ParallelIterator<Item = u32>;
    fn sub_sets(&self) -> Vec<Self>;
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

    fn power_set_of_size(size: usize) -> RangeInclusive<u32> {
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

    fn is_empty(&self) -> bool {
        *self == 0
    }

    fn sub_sets(&self) -> Vec<Self> {
        let mut result = Vec::new();
        for i in 0..=*self {
            if i.is_subset(self) {
                result.push(i);
            }
        }
        result
    }
}

pub fn powerset<T: Clone + std::cmp::Eq + std::hash::Hash>(
    origin: impl IntoIterator<Item = T>,
) -> Vec<Set<T>> {
    let mut result = vec![Set::default()];
    for elem in origin {
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

pub fn powerset_vec<T: Clone>(origin: &[T]) -> Vec<Vec<T>> {
    BitSet32::power_set_of_size(origin.len())
        .map(|bits| bits.iter().map(|i| origin[i as usize].clone()).collect())
        .collect()
}

pub fn character_to_label_expression(
    letter: BitSet32,
    atom_count: usize,
) -> Vec<AbstractLabelExpression> {
    letter
        .bits(atom_count as u32)
        .enumerate()
        .map(|(i, it)| {
            if it {
                AbstractLabelExpression::Integer(i as _)
            } else {
                AbstractLabelExpression::Negated(Box::new(AbstractLabelExpression::Integer(i as _)))
            }
        })
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_powerset() {
        let set = Set::from_iter(["a", "b"]);
        let expected = [
            Set::default(),
            Set::from_iter(["a"]),
            Set::from_iter(["b"]),
            Set::from_iter(["a", "b"]),
        ];
        let powerset = powerset(set);
        assert_eq!(powerset.len(), expected.len());
        for set in powerset {
            assert!(expected.contains(&set));
        }
    }

    #[test]
    fn test_sub_power_set() {
        let set = 0b10;
        println!("set: 0b{set:b}");
        // let expected = [
        //     BitSet32::full_with_size(0),
        //     BitSet32::full_with_size(1),
        // ];
        let sub_power_set = set.sub_sets();
        for set in sub_power_set {
            println!("set: 0b{set:b}");
        }
        // assert_eq!(sub_power_set.len(), expected.len());
        // for set in sub_power_set {
        //     assert!(expected.contains(&set));
        // }
    }
}
