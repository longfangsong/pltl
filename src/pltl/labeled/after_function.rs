use std::sync::RwLock;

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::utils::{BitSet, BitSet32, Map};

use super::LabeledPLTL;

fn local_post_update(
    f: &LabeledPLTL,
    letter: BitSet32,
    past_st: BitSet32,
    cache: &Vec<Vec<RwLock<Map<LabeledPLTL, LabeledPLTL>>>>,
) -> LabeledPLTL {
    let mut first_part = f.clone();
    first_part = first_part.c_rewrite(past_st);
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
            let sub_result = local_after(&psf.weaken_condition(), letter, past_st, cache);
            result = result & sub_result;
        }
    }
    result
}

pub fn local_after(
    f: &LabeledPLTL,
    letter: BitSet32,
    past_st: BitSet32,
    cache: &Vec<Vec<RwLock<Map<LabeledPLTL, LabeledPLTL>>>>,
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
        _ => {
            let rache_read = cache[letter as usize][past_st as usize].read().unwrap();
            if let Some(result) = rache_read.get(f) {
                return result.clone();
            }
            drop(rache_read);
            let result = match f {
                LabeledPLTL::Top
                | LabeledPLTL::Bottom
                | LabeledPLTL::Atom(_)
                | LabeledPLTL::Not(_)
                | LabeledPLTL::Yesterday { .. } => unreachable!("should not cache"),
                LabeledPLTL::Next(labeled_pltl) => {
                    local_post_update(labeled_pltl, letter, past_st, cache)
                }
                LabeledPLTL::Logical(binary_op, content) => LabeledPLTL::Logical(
                    *binary_op,
                    content
                        .iter()
                        .map(|item| local_after(item, letter, past_st, cache))
                        .collect(),
                ),
                LabeledPLTL::Until { lhs, rhs, .. } => {
                    let rhs_after = local_after(rhs, letter, past_st, cache);
                    if rhs_after == LabeledPLTL::Top {
                        LabeledPLTL::Top
                    } else {
                        let lhs_after = local_after(lhs, letter, past_st, cache);
                        if lhs_after == LabeledPLTL::Bottom {
                            rhs_after
                        } else {
                            let f_pu = local_post_update(f, letter, past_st, cache);
                            rhs_after | (lhs_after & f_pu)
                        }
                    }
                }
                LabeledPLTL::Release { lhs, rhs, .. } => {
                    let rhs_after = local_after(rhs, letter, past_st, cache);
                    if rhs_after == LabeledPLTL::Bottom {
                        LabeledPLTL::Bottom
                    } else {
                        let lhs_after = local_after(lhs, letter, past_st, cache);
                        if lhs_after == LabeledPLTL::Top {
                            rhs_after
                        } else {
                            let f_pu = local_post_update(f, letter, past_st, cache);
                            rhs_after & (lhs_after | f_pu)
                        }
                    }
                }
                LabeledPLTL::BinaryTemporal { .. } => {
                    local_after(&f.weaken_condition(), letter, past_st, cache)
                }
            }
            .simplify();

            // println!("afl({f}, {letter}, {past_st}) = {result}");
            let mut rache_write = cache[letter as usize][past_st as usize].write().unwrap();
            rache_write.insert(f.clone(), result.clone());
            result
        }
    }
}

pub fn after_function(
    labeled_pltl: &LabeledPLTL,
    letter: u32,
    cache: &Vec<Vec<RwLock<Map<LabeledPLTL, LabeledPLTL>>>>,
) -> LabeledPLTL {
    let c_sets = labeled_pltl.past_subformula_ids().sub_sets();
    let results = c_sets
        .par_iter()
        .map(|c_set| local_after(labeled_pltl, letter, *c_set, cache))
        .collect::<Vec<_>>();
    results.into_iter().reduce(|acc, item| acc | item).unwrap()
}
