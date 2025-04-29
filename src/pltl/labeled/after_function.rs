use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::utils::{BitSet, BitSet32};

use super::LabeledPLTL;

fn local_post_update(f: &LabeledPLTL, letter: BitSet32, past_st: BitSet32) -> LabeledPLTL {
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
            result = result & local_after(&psf.weaken_condition(), letter, past_st);
        }
    }
    result
}

pub fn local_after(f: &LabeledPLTL, letter: BitSet32, past_st: BitSet32) -> LabeledPLTL {
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
        LabeledPLTL::Next(labeled_pltl) => local_post_update(labeled_pltl, letter, past_st),
        LabeledPLTL::Yesterday { weak, .. } => {
            if *weak {
                LabeledPLTL::Top
            } else {
                LabeledPLTL::Bottom
            }
        }
        LabeledPLTL::Logical(binary_op, content) => LabeledPLTL::Logical(
            *binary_op,
            content
                .iter()
                .map(|item| local_after(item, letter, past_st))
                .collect(),
        ),
        LabeledPLTL::Until { lhs, rhs, .. } => {
            let rhs_after = local_after(rhs, letter, past_st);
            if rhs_after == LabeledPLTL::Top {
                LabeledPLTL::Top
            } else {
                let lhs_after = local_after(lhs, letter, past_st);
                if lhs_after == LabeledPLTL::Bottom {
                    rhs_after
                } else {
                    let f_pu = local_post_update(f, letter, past_st);
                    rhs_after | (lhs_after & f_pu)
                }
            }
        }
        LabeledPLTL::Release { weak, lhs, rhs } => {
            let rhs_after = local_after(rhs, letter, past_st);
            if rhs_after == LabeledPLTL::Bottom {
                LabeledPLTL::Bottom
            } else {
                let lhs_after = local_after(lhs, letter, past_st);
                if lhs_after == LabeledPLTL::Top {
                    rhs_after
                } else {
                    let f_pu = local_post_update(f, letter, past_st);
                    rhs_after & (lhs_after | f_pu)
                }
            }
        }
        LabeledPLTL::BinaryTemporal { .. } => local_after(&f.weaken_condition(), letter, past_st),
    }
}

pub fn after_function(labeled_pltl: &LabeledPLTL, letter: u32) -> LabeledPLTL {
    let c_sets = labeled_pltl.past_subformula_ids().sub_power_set();
    let results = c_sets
        .par_iter()
        .map(|c_set| local_after(labeled_pltl, letter, *c_set))
        .collect::<Vec<_>>();
    results.into_iter().reduce(|acc, item| acc | item).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::pltl::{labeled::LabeledPLTL, PLTL};

    #[test]
    fn test_after_function() {
        let (pltl, ctx) = PLTL::from_string("G (p | Y q)").unwrap();
        let pltl = pltl.to_no_fgoh().to_negation_normal_form().simplify();
        let (labeled_pltl, context) = LabeledPLTL::new(&pltl);
        let results = (0..4)
            .map(|letter| after_function(&labeled_pltl, letter))
            .collect::<Vec<_>>();
        for result in &results {
            println!("{}", result.clone().simplify());
        }
        println!("===");
        let next_resuslts = (0u32..4)
            .map(|letter| after_function(&results[letter as usize], letter))
            .collect::<Vec<_>>();
        for result in next_resuslts {
            println!("{}", result.simplify());
        }
    }
}
