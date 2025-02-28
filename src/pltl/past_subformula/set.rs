use std::collections::HashSet;

use crate::{pltl::PLTL, utils::{BitSet, BitSet32}};

use super::{context::PastSubformularSetContext, formula::PastSubformula};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PastSubformulaSet {
    /// psf_id -> whether it exists in this set
    pub(crate) existence: BitSet32,
    /// psf_id -> state (1 for weaken, 0 for strong)
    pub(crate) state: BitSet32,
}

pub struct Iter<'a> {
    set: &'a PastSubformulaSet,
    current_psf_index: u32,
}

impl Iterator for Iter<'_> {
    type Item = PastSubformula;

    fn next(&mut self) -> Option<Self::Item> {
        while self.current_psf_index < 32 {
            if self.set.existence.get(self.current_psf_index) {
                let result = self.current_psf_index;
                self.current_psf_index += 1;
                return Some(PastSubformula {
                    id: result,
                    state: self.set.state.clone(),
                });
            }
            self.current_psf_index += 1;
        }
        None
    }
}

impl PastSubformulaSet {
    pub fn contains(&self, ctx: &PastSubformularSetContext<'_>, s: &PastSubformula) -> bool {
        let same_shape_psfs = ctx.same_shape_formulas[s.id as usize];
        // we move the states to 0
        let mask = ctx.masks[s.id as usize];
        let state = (s.state & mask) >> mask.trailing_zeros();
        for other_psf_id in same_shape_psfs.iter() {
            if self.existence.get(other_psf_id) {
                let other_psf_mask = ctx.masks[other_psf_id as usize];
                let other_psf_state =
                    (self.state & other_psf_mask) >> other_psf_mask.trailing_zeros();
                if state == other_psf_state {
                    return true;
                }
            }
        }
        false
    }

    pub fn is_proper_set(&self, ctx: &PastSubformularSetContext<'_>) -> bool {
        for psf_id in self.existence.iter() {
            let same_shape_psfs = ctx.same_shape_formulas[psf_id as usize];
            for other_psf_id in same_shape_psfs.iter() {
                if self.existence.get(other_psf_id)
                    && self.state.get(other_psf_id) == self.state.get(psf_id)
                {
                    return false;
                }
            }
        }
        true
    }

    pub fn to_proper_set(&self, ctx: &PastSubformularSetContext<'_>) -> PastSubformulaSet {
        let mut result = self.clone();
        for psf_id in self.existence.iter() {
            if !result.existence.get(psf_id) {
                // already removed
                continue;
            }
            let same_shape_psfs = ctx.same_shape_formulas[psf_id as usize];
            for other_psf_id in same_shape_psfs.iter() {
                if psf_id != other_psf_id
                    && self.existence.get(other_psf_id)
                    && self.state.get(other_psf_id) == self.state.get(psf_id)
                {
                    result.existence.set(other_psf_id, false);
                }
            }
        }
        result
    }

    pub fn iter(&self) -> Iter<'_> {
        Iter {
            set: self,
            current_psf_index: 0,
        }
    }

    pub fn next(&self, ctx: &PastSubformularSetContext<'_>) -> Option<Self> {
        let mut result = self.clone();
        'outer: while (result.existence as u64) + 1 < (1u64 << ctx.past_subformulas.len()) {
            result.existence += 1;
            for psf in result.existence.iter() {
                // broadcast initial_state of psf to full width
                let psf_state_mask = (self.state.get(psf) as BitSet32) * BitSet32::MAX;
                let same_state_formulas = !(self.state ^ psf_state_mask);
                let same_shape_formulas = ctx.same_shape_formulas[psf as usize];
                let same_formulas = same_state_formulas & same_shape_formulas;

                if psf != same_formulas.trailing_zeros() {
                    continue 'outer;
                }
            }
            return Some(result);
        }
        None
    }

    pub fn to_pltl_set(&self, ctx: &PastSubformularSetContext<'_>) -> HashSet<PLTL> {
        let mut result = HashSet::new();
        for psf in self.iter() {
            result.insert(psf.to_pltl(ctx));
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pltl::PLTL;

    #[test]
    fn test_set_contains() {
        let pltl: PLTL = "((Y a) S (~Y a)) B ((Y a) ~S (Y a))".parse().unwrap();
        let context = PastSubformularSetContext::new(&pltl);
        // case 1: exists in the same place
        let part = PastSubformula {
            id: 0,
            state: 0b0000000,
        };
        let set = PastSubformulaSet {
            existence: 0b0000001,
            state: 0b0000000,
        };
        assert!(set.contains(&context, &part));
        // case 2: exists in other place
        let part = PastSubformula {
            id: 3,
            state: 0b0000000,
        };
        let set = PastSubformulaSet {
            existence: 0b0001000,
            state: 0b0000000,
        };
        assert!(set.contains(&context, &part));
        // case 3: not exists at all
        let part = PastSubformula {
            id: 0,
            state: 0b0000001,
        };
        let set = PastSubformulaSet {
            existence: 0b0000000,
            state: 0b0000000,
        };
        assert!(!set.contains(&context, &part));
        // case 4: exists in same place but different state
        let part = PastSubformula {
            id: 0,
            state: 0b0000000,
        };
        let set = PastSubformulaSet {
            existence: 0b0000001,
            state: 0b0000001,
        };
        assert!(!set.contains(&context, &part));
        // case 5: exists in different place but different state
        let part = PastSubformula {
            id: 0,
            state: 0b0000000,
        };
        let set = PastSubformulaSet {
            existence: 0b0000010,
            state: 0b0000010,
        };
        assert!(!set.contains(&context, &part));
    }

    #[test]
    fn test_set_next() {
        let pltl: PLTL = "((Y a) S (~Y a)) B ((Y a) ~S (Y a))".parse().unwrap();
        let context = PastSubformularSetContext::new(&pltl);
        let mut current_set = PastSubformulaSet {
            existence: 0b0000000,
            state: context.initial_state,
        };
        let mut all_sets = vec![current_set.clone()];
        while let Some(set) = current_set.next(&context) {
            all_sets.push(set.clone());
            current_set = set;
        }
        assert_eq!(all_sets.len(), 32);
    }

    #[test]
    fn test_set_to_proper_set() {
        let ltl: PLTL = "Ya S ~Ya".parse().unwrap();
        let context = PastSubformularSetContext::new(&ltl);
        let set = PastSubformulaSet {
            existence: 0b011,
            state: 0b0,
        };
        let proper_set = set.to_proper_set(&context);
        assert_eq!(proper_set.iter().count(), 1);
        for psf in proper_set.iter() {
            println!("{}", psf.to_pltl(&context));
        }
    }
}
