use core::fmt;
use std::sync::RwLock;

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::{
    pltl::BinaryOp,
    utils::{BitSet, BitSet32, Map},
};

use super::LabeledPLTL;
#[derive(Clone, Debug)]
pub struct CacheItem {
    // which atoms should be considered when calculating the after function
    // in other words, which atoms are there in the pLTL formula
    atom_mask: BitSet32,
    // which past subformulas should be considered when calculating the after function
    // in other words, which past subformulas are there in the pLTL formula
    past_st_mask: BitSet32,
    // (letter & atom_mask, past_st & past_st_mask) -> result
    cache: Map<(BitSet32, BitSet32), LabeledPLTL>,
}

impl fmt::Display for CacheItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "(0b{:b}, 0b{:b})", self.atom_mask, self.past_st_mask)?;
        for ((letter, past_st), result) in self.cache.iter() {
            writeln!(f, "(0b{letter:b}, 0b{past_st:b}) -> {result}")?;
        }
        Ok(())
    }
}

impl CacheItem {
    pub fn get(&self, letter: BitSet32, past_st: BitSet32) -> Option<&LabeledPLTL> {
        self.cache
            .get(&(letter & self.atom_mask, past_st & self.past_st_mask))
    }
}

pub fn cache_local_past(
    ltl: &LabeledPLTL,
    result: &RwLock<Map<LabeledPLTL, CacheItem>>
) {
    if result.read().unwrap().contains_key(ltl) {
        return;
    }
    match ltl {
        LabeledPLTL::Top | LabeledPLTL::Bottom => {
            let mut cache = Map::default();
            cache.insert((BitSet32::default(), BitSet32::default()), ltl.clone());
            result.write().unwrap().insert(
                ltl.clone(),
                CacheItem {
                    atom_mask: BitSet32::default(),
                    past_st_mask: BitSet32::default(),
                    cache,
                },
            );
        }
        LabeledPLTL::Atom(atom) => {
            let atom_mask = 1u32 << atom;
            let mut cache = Map::default();
            cache.insert(
                (BitSet32::default(), BitSet32::default()),
                LabeledPLTL::Bottom,
            );
            cache.insert((atom_mask, BitSet32::default()), LabeledPLTL::Top);
            result.write().unwrap().insert(
                ltl.clone(),
                CacheItem {
                    atom_mask,
                    past_st_mask: BitSet32::default(),
                    cache: cache.clone(),
                },
            );
        }
        LabeledPLTL::Not(atom) => {
            let atom_mask = 1u32 << atom;
            let mut cache = Map::default();
            cache.insert((BitSet32::default(), BitSet32::default()), LabeledPLTL::Top);
            cache.insert((atom_mask, BitSet32::default()), LabeledPLTL::Bottom);
            result.write().unwrap().insert(
                ltl.clone(),
                CacheItem {
                    atom_mask,
                    past_st_mask: BitSet32::default(),
                    cache,
                },
            );
        }
        LabeledPLTL::Yesterday { id, weak, content } => {
            cache_local_past(content, result);
            let content_entry = result.read().unwrap().get(content).unwrap().clone();
            let mut cache = Map::default();
            cache.insert(
                (content_entry.atom_mask, content_entry.past_st_mask),
                if *weak {
                    LabeledPLTL::Top
                } else {
                    LabeledPLTL::Bottom
                },
            );
            let mut item = CacheItem {
                atom_mask: content_entry.atom_mask,
                past_st_mask: content_entry.past_st_mask | (1u32 << id),
                cache,
            };
            for ((letter, past_st), result) in content_entry.cache.iter() {
                item.cache.insert(
                    (*letter, *past_st | (1u32 << id)),
                    if *weak {
                        LabeledPLTL::Top
                    } else {
                        LabeledPLTL::Bottom
                    },
                );
                item.cache.insert(
                    (*letter, *past_st),
                    if *weak {
                        LabeledPLTL::Top
                    } else {
                        LabeledPLTL::Bottom
                    },
                );
            }
            result.write().unwrap().insert(ltl.clone(), item);
        }
        LabeledPLTL::Next(content) => {
            cache_local_past(content, result);
            let content_entry = result.read().unwrap().get(content).unwrap().clone();
            let mut cache = Map::default();
            for ((letter, past_st), _) in content_entry.cache.iter() {
                let result = do_local_post_update(&content, *letter, *past_st, result);
                cache.insert((*letter, *past_st), result);
            }
            result.write().unwrap().insert(
                ltl.clone(),
                CacheItem {
                    atom_mask: content_entry.atom_mask,
                    past_st_mask: content_entry.past_st_mask,
                    cache,
                },
            );
        }
        LabeledPLTL::Logical(binary_op, contents) => {
            let mut result_atom_mask = BitSet32::default();
            let mut result_past_st_mask = BitSet32::default();
            let mut sub_results = Vec::new();
            contents.par_iter().for_each(|item| {
                cache_local_past(item, result);
            });
            for item in contents.iter() {
                let sub_result = result.read().unwrap().get(item).unwrap().clone();
                result_atom_mask |= sub_result.atom_mask;
                result_past_st_mask |= sub_result.past_st_mask;
                sub_results.push(sub_result);
            }
            let mut result_item = CacheItem {
                atom_mask: result_atom_mask,
                past_st_mask: result_past_st_mask,
                cache: Map::default(),
            };
            for result_atom in result_atom_mask.sub_sets() {
                'calc: for result_past_st in result_past_st_mask.sub_sets() {
                    let mut result_pltls = Vec::with_capacity(sub_results.len());
                    for sub_result in sub_results.iter() {
                        let sub_result_pltl = sub_result.get(result_atom, result_past_st).unwrap();
                        match (binary_op, sub_result_pltl) {
                            (BinaryOp::And, LabeledPLTL::Top) => (),
                            (BinaryOp::And, LabeledPLTL::Bottom) => {
                                result_item
                                    .cache
                                    .insert((result_atom, result_past_st), LabeledPLTL::Bottom);
                                continue 'calc;
                            }
                            (BinaryOp::Or, LabeledPLTL::Top) => {
                                result_item
                                    .cache
                                    .insert((result_atom, result_past_st), LabeledPLTL::Top);
                                continue 'calc;
                            }
                            (BinaryOp::Or, LabeledPLTL::Bottom) => (),
                            (_, sub_result_pltl) => result_pltls.push(sub_result_pltl.clone()),
                        }
                    }
                    let result_pltl = LabeledPLTL::Logical(*binary_op, result_pltls).simplify();
                    result_item
                        .cache
                        .insert((result_atom, result_past_st), result_pltl);
                }
            }
            result.write().unwrap().insert(ltl.clone(), result_item);
        }
        LabeledPLTL::Until { lhs, rhs, .. } => {
            rayon::scope(|s| {
                s.spawn(|_| cache_local_past(lhs, result));
                s.spawn(|_| cache_local_past(rhs, result));
            });
            let read = result.read().unwrap();
            let lhs_entry = read.get(lhs).unwrap();
            let rhs_entry = read.get(rhs).unwrap();

            let mut result_item = CacheItem {
                atom_mask: lhs_entry.atom_mask | rhs_entry.atom_mask,
                past_st_mask: lhs_entry.past_st_mask | rhs_entry.past_st_mask,
                cache: Map::default(),
            };
            for result_atom in result_item.atom_mask.sub_sets() {
                'calc: for result_past_st in result_item.past_st_mask.sub_sets() {
                    let rhs_result = rhs_entry.get(result_atom, result_past_st).unwrap();
                    if matches!(rhs_result, LabeledPLTL::Top) {
                        result_item
                            .cache
                            .insert((result_atom, result_past_st), LabeledPLTL::Top);
                        continue 'calc;
                    }
                    let lhs_result = lhs_entry.get(result_atom, result_past_st).unwrap();
                    if matches!(lhs_result, LabeledPLTL::Bottom) {
                        result_item
                            .cache
                            .insert((result_atom, result_past_st), rhs_result.clone());
                        continue 'calc;
                    }
                    let f_pu =
                        do_local_post_update(ltl, result_atom, result_past_st, result);
                    result_item.cache.insert(
                        (result_atom, result_past_st),
                        (rhs_result.clone() | (lhs_result.clone() & f_pu)).simplify(),
                    );
                }
            }
            drop(read);
            result.write().unwrap().insert(ltl.clone(), result_item);
        }
        LabeledPLTL::Release { lhs, rhs, .. } => {
            rayon::scope(|s| {
                s.spawn(|_| cache_local_past(lhs, result));
                s.spawn(|_| cache_local_past(rhs, result));
            });
            let read = result.read().unwrap();
            let lhs_entry = read.get(lhs).unwrap();
            let rhs_entry = read.get(rhs).unwrap();
            let mut result_item = CacheItem {
                atom_mask: lhs_entry.atom_mask | rhs_entry.atom_mask,
                past_st_mask: lhs_entry.past_st_mask | rhs_entry.past_st_mask,
                cache: Map::default(),
            };
            for result_atom in result_item.atom_mask.sub_sets() {
                'calc: for result_past_st in result_item.past_st_mask.sub_sets() {
                    let rhs_result = rhs_entry.get(result_atom, result_past_st).unwrap();
                    if matches!(rhs_result, LabeledPLTL::Bottom) {
                        result_item
                            .cache
                            .insert((result_atom, result_past_st), LabeledPLTL::Bottom);
                        continue 'calc;
                    }
                    let lhs_result = lhs_entry.get(result_atom, result_past_st).unwrap();
                    if matches!(lhs_result, LabeledPLTL::Top) {
                        result_item
                            .cache
                            .insert((result_atom, result_past_st), rhs_result.clone());
                        continue 'calc;
                    }
                    let f_pu =
                        do_local_post_update(ltl, result_atom, result_past_st, result);
                    result_item.cache.insert(
                        (result_atom, result_past_st),
                        (rhs_result.clone() & (lhs_result.clone() | f_pu)).simplify(),
                    );
                }
            }
            drop(read);
            result.write().unwrap().insert(ltl.clone(), result_item);
        }
        LabeledPLTL::BinaryTemporal { id, lhs, rhs, .. } => {
            rayon::scope(|s| {
                s.spawn(|_| cache_local_past(lhs, result));
                s.spawn(|_| cache_local_past(rhs, result));
            });
            // this one does not need to be parallel with the above two
            // since wc is either one of, or a combination of lhs and rhs
            let wc = ltl.weaken_condition();
            cache_local_past(&wc, result);
            let wc_entry = result.read().unwrap().get(&wc).unwrap().clone();
            let mut result_item = CacheItem {
                atom_mask: wc_entry.atom_mask,
                past_st_mask: wc_entry.past_st_mask | (1u32 << id),
                cache: wc_entry.cache.clone(),
            };
            for ((letter, past_st), result) in wc_entry.cache.iter() {
                result_item
                    .cache
                    .insert((*letter, *past_st | (1u32 << id)), result.clone());
            }
            result.write().unwrap().insert(ltl.clone(), result_item);
        }
    }
}

fn do_local_post_update(
    f: &LabeledPLTL,
    letter: BitSet32,
    past_st: BitSet32,
    new_cache: &RwLock<Map<LabeledPLTL, CacheItem>>,
) -> LabeledPLTL {
    // println!("+ do_local_post_update({f}, 0b{letter:b}, 0b{past_st:b})");
    let mut first_part = f.clone();
    first_part = first_part.c_rewrite(past_st);
    // println!("first_part: {first_part}");
    let psfs = f.past_subformulas();
    let mut result = first_part;
    for psf in psfs.iter() {
        let id = if let LabeledPLTL::Yesterday { id, .. } = psf {
            *id
        } else if let LabeledPLTL::BinaryTemporal { id, .. } = psf {
            *id
        } else {
            unreachable!("not a psf")
        };
        if past_st.contains(id) {
            // println!("contains: {psf}");
            let sub_result = do_local_after(
                &psf.weaken_condition(),
                letter,
                past_st,
                new_cache,
            );
            result = result & sub_result;
        }
    }
    result
}

pub fn do_local_after(
    f: &LabeledPLTL,
    letter: BitSet32,
    past_st: BitSet32,
    new_cache: &RwLock<Map<LabeledPLTL, CacheItem>>,
) -> LabeledPLTL {
    match f {
        LabeledPLTL::Top => LabeledPLTL::Top,
        LabeledPLTL::Bottom => LabeledPLTL::Bottom,
        LabeledPLTL::Atom(atom) => {
            if letter.contains(*atom) {
                LabeledPLTL::Top
            } else {
                LabeledPLTL::Bottom
            }
        }
        LabeledPLTL::Not(atom) => {
            if letter.contains(*atom) {
                LabeledPLTL::Bottom
            } else {
                LabeledPLTL::Top
            }
        }
        LabeledPLTL::Yesterday { weak, .. } => {
            if *weak {
                LabeledPLTL::Top
            } else {
                LabeledPLTL::Bottom
            }
        }
        _ => match f {
            LabeledPLTL::Top
            | LabeledPLTL::Bottom
            | LabeledPLTL::Atom(_)
            | LabeledPLTL::Not(_)
            | LabeledPLTL::Yesterday { .. } => unreachable!("should not cache"),
            LabeledPLTL::Next(labeled_pltl) => {
                do_local_post_update(labeled_pltl, letter, past_st, new_cache)
            }
            LabeledPLTL::Logical(binary_op, content) => LabeledPLTL::Logical(
                *binary_op,
                content
                    .iter()
                    .map(|item| do_local_after(item, letter, past_st, new_cache))
                    .collect(),
            ),
            LabeledPLTL::Until { lhs, rhs, .. } => {
                let rhs_after = do_local_after(rhs, letter, past_st, new_cache);
                if rhs_after == LabeledPLTL::Top {
                    LabeledPLTL::Top
                } else {
                    let lhs_after = do_local_after(lhs, letter, past_st, new_cache);
                    if lhs_after == LabeledPLTL::Bottom {
                        rhs_after
                    } else {
                        let f_pu = do_local_post_update(f, letter, past_st, new_cache);
                        rhs_after | (lhs_after & f_pu)
                    }
                }
            }
            LabeledPLTL::Release { lhs, rhs, .. } => {
                let rhs_after = do_local_after(rhs, letter, past_st, new_cache);
                if rhs_after == LabeledPLTL::Bottom {
                    LabeledPLTL::Bottom
                } else {
                    let lhs_after = do_local_after(lhs, letter, past_st, new_cache);
                    if lhs_after == LabeledPLTL::Top {
                        rhs_after
                    } else {
                        let f_pu = do_local_post_update(f, letter, past_st, new_cache);
                        rhs_after & (lhs_after | f_pu)
                    }
                }
            }
            LabeledPLTL::BinaryTemporal { .. } => do_local_after(
                &f.weaken_condition(),
                letter,
                past_st,
                new_cache,
            ),
        }
        .simplify(),
    }
}

pub fn after_function(
    labeled_pltl: &LabeledPLTL,
    letter: u32,
    cache: &RwLock<Map<LabeledPLTL, CacheItem>>,
) -> LabeledPLTL {
    cache_local_past(labeled_pltl, cache);
    let read = cache.read().unwrap();
    let cache_item = read.get(labeled_pltl).unwrap();
    let mut result = Vec::with_capacity(1 << cache_item.past_st_mask.len());
    for past_st in cache_item.past_st_mask.sub_sets() {
        let sub_result = cache_item.get(letter, past_st).unwrap();
        if matches!(sub_result, LabeledPLTL::Top) {
            return LabeledPLTL::Top;
        } else if !matches!(sub_result, LabeledPLTL::Bottom) {
            result.push(sub_result.clone());
        }
    }
    drop(read);
    if result.is_empty() {
        LabeledPLTL::Bottom
    } else if result.len() == 1 {
        result.pop().unwrap()
    } else {
        LabeledPLTL::Logical(BinaryOp::Or, result.into_iter().collect()).simplify()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pltl::PLTL;

    #[test]
    fn test_after_function() {
        let (ltl, ltl_ctx) = PLTL::from_string("F(Y p)").unwrap();
        // println!("ltl_ctx: {ltl_ctx}");
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        let (labeled_ltl, labeled_ctx) = LabeledPLTL::new(&ltl);
        let new_cache = RwLock::new(Map::default());
        cache_local_past(&labeled_ltl, &new_cache);
        let result = after_function(&labeled_ltl, 0b1, &new_cache);
        assert_eq!(format!("{result}"), r#"(⊤ U Y"0") ∨ (⊤ U ~Y"0")"#);
    }

    #[test]
    fn test_after_function_2() {
        let (ltl, ltl_ctx) = PLTL::from_string("F ( r & (r S p))").unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        let (labeled_ltl, labeled_ctx) = LabeledPLTL::new(&ltl);
        let new_cache = RwLock::new(Map::default());
        cache_local_past(&labeled_ltl, &new_cache);
        let result = after_function(
            &labeled_ltl,
            0b10,
            &new_cache,
        );
        println!("result: {result}");
        let result = after_function(&result, 0b00, &new_cache);
        println!("result: {result}");
    }

    #[test]
    fn test_cache() {
        let (ltl, ltl_ctx) = PLTL::from_string("F ( r & (r S p))").unwrap();
        println!("{}", ltl_ctx);
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        let (labeled_ltl, labeled_ctx) = LabeledPLTL::new(&ltl);
        let cache = RwLock::new(Map::default());
        cache_local_past(&labeled_ltl, &cache);
        for (ltl, item) in cache.read().unwrap().iter() {
            // println!("+ ltl: {ltl} {}", item.cache.len());
            // if item.cache.len() == 8 {
            println!("+{}", ltl);
            for ((letter, past_st), result) in item.cache.iter() {
                println!("  (0b{letter:b}, 0b{past_st:b}) -> {result}");
            }
            // }
        }
        println!("{}", cache.read().unwrap().len());
    }
}
