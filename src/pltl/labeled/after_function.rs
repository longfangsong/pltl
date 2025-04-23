// use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::{
    pltl::{labeled::info::{psf_weaken_condition, weaken_condition}, BinaryOp, UnaryOp},
    utils::{BitSet, BitSet32, Set},
};

use super::{Context, LabeledPLTL};

fn local_post_update(
    ctx: &Context,
    f: &LabeledPLTL,
    letter: BitSet32,
    past_st: BitSet32,
) -> LabeledPLTL {
    let mut first_part = f.clone();
    first_part.rewrite_with_set(past_st);
    let psfs = f.past_subformulas(ctx);
    let past_st_with_state: Set<(u32, BitSet32)> = past_st.iter().map(|id| {
        (id, ctx.initial_weaken_state & ctx.past_subformula_contains[id as usize])
    }).collect();
    let intersection: Vec<(u32, BitSet32)> = psfs.intersection(&past_st_with_state).cloned().collect();
    if intersection.is_empty() {
        first_part
    } else {
        let mut result = first_part;
        for (psf_id, strength) in intersection {
            let psf_in_correct_form_weaken_condition = psf_weaken_condition(ctx, psf_id, strength);
            let inner_result = local_after(
                ctx,
                &psf_in_correct_form_weaken_condition,
                letter,
                past_st,
            );
            result = LabeledPLTL::new_binary(BinaryOp::And, result, inner_result);
        }
        result
    }
}

pub fn local_after(
    ctx: &Context,
    f: &LabeledPLTL,
    letter: BitSet32,
    past_st: BitSet32,
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
        LabeledPLTL::Unary(UnaryOp::Not, box content) => {
            let LabeledPLTL::Atom(atom) = content else {
                unreachable!()
            };
            if letter.contains(*atom) {
                LabeledPLTL::Bottom
            } else {
                LabeledPLTL::Top
            }
        }
        LabeledPLTL::Unary(UnaryOp::Yesterday, _) => LabeledPLTL::Bottom,
        LabeledPLTL::Unary(UnaryOp::WeakYesterday, _) => LabeledPLTL::Top,
        LabeledPLTL::Unary(unary_op, box content) => {
            debug_assert_eq!(unary_op, &UnaryOp::Next);
            local_post_update(ctx, content, letter, past_st)
        }
        LabeledPLTL::Binary(BinaryOp::And, lhs, rhs) => {
            let lhs_after = local_after(ctx, lhs, letter, past_st);
            if lhs_after == LabeledPLTL::Bottom {
                LabeledPLTL::Bottom
            } else {
                let rhs_after = local_after(ctx, rhs, letter, past_st);
                LabeledPLTL::new_binary(BinaryOp::And, lhs_after, rhs_after)
            }
        }
        LabeledPLTL::Binary(BinaryOp::Or, lhs, rhs) => {
            let lhs_after = local_after(ctx, lhs, letter, past_st);
            if lhs_after == LabeledPLTL::Top {
                LabeledPLTL::Top
            } else {
                let rhs_after = local_after(ctx, rhs, letter, past_st);
                LabeledPLTL::new_binary(BinaryOp::Or, lhs_after, rhs_after)
            }
        }
        LabeledPLTL::Binary(BinaryOp::Until | BinaryOp::WeakUntil, lhs, rhs) => {
            let rhs_after = local_after(ctx, rhs, letter, past_st);
            if rhs_after == LabeledPLTL::Top {
                LabeledPLTL::Top
            } else {
                let lhs_after = local_after(ctx, lhs, letter, past_st);
                if lhs_after == LabeledPLTL::Bottom {
                    rhs_after
                } else {
                    LabeledPLTL::new_binary(
                        BinaryOp::Or,
                        rhs_after,
                        LabeledPLTL::new_binary(
                            BinaryOp::And,
                            lhs_after,
                            local_post_update(ctx, f, letter, past_st),
                        ),
                    )
                }
            }
        }
        LabeledPLTL::Binary(BinaryOp::Release | BinaryOp::MightyRelease, lhs, rhs) => {
            let rhs_after = local_after(ctx, rhs, letter, past_st);
            if rhs_after == LabeledPLTL::Bottom {
                LabeledPLTL::Bottom
            } else {
                let lhs_after = local_after(ctx, lhs, letter, past_st);
                if lhs_after == LabeledPLTL::Top {
                    rhs_after
                } else {
                    LabeledPLTL::new_binary(
                        BinaryOp::And,
                        rhs_after,
                        LabeledPLTL::new_binary(
                            BinaryOp::Or,
                            lhs_after,
                            local_post_update(ctx, f, letter, past_st),
                        ),
                    )
                }
            }
        }
        LabeledPLTL::Binary(
            BinaryOp::Since | BinaryOp::WeakSince | BinaryOp::BackTo | BinaryOp::WeakBackTo,
            _,
            _,
        ) => local_after(
            ctx,
            &weaken_condition(ctx, f),
            letter,
            past_st,
        ),
        LabeledPLTL::PastSubformula(psf_id, inner_weaken_state) => {
            let expand_once = &ctx.expand_once[*psf_id as usize];
            match expand_once {
                LabeledPLTL::Unary(UnaryOp::Yesterday, _) => LabeledPLTL::Bottom,
                LabeledPLTL::Unary(UnaryOp::WeakYesterday, _) => LabeledPLTL::Top,
                LabeledPLTL::Binary(
                    BinaryOp::Since | BinaryOp::WeakSince | BinaryOp::BackTo | BinaryOp::WeakBackTo,
                    _,
                    _,
                ) => local_after(
                    ctx,
                    &psf_weaken_condition(ctx, *psf_id, *inner_weaken_state),
                    letter,
                    past_st,
                ),
                _ => unreachable!(),
            }
        }
    }
}

pub fn after_function(ctx: &Context, f: &LabeledPLTL, letter: BitSet32) -> LabeledPLTL {
    let psf_without_state = f.past_subformulas_without_state(ctx);
    let mut psf_powerset = psf_without_state.sub_power_set();
    let psf = psf_powerset.pop().unwrap();
    let mut result = local_after(ctx, f, letter, psf);
    if result == LabeledPLTL::Top {
        return result;
    }
    while let Some(psf) = psf_powerset.pop() {
        let subresult = local_after(ctx, f, letter, psf);
        if subresult == LabeledPLTL::Top {
            return LabeledPLTL::Top;
        } else {
            result = LabeledPLTL::new_binary(BinaryOp::Or, result, subresult);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::pltl::{
        labeled::{after_function::local_after, LabeledPLTL},
        PLTL,
    };

    #[test]
    fn test_after_function() {
        let (pltl, ctx) = PLTL::from_string("G (p | Y q)").unwrap();
        let pltl = pltl.to_no_fgoh().to_negation_normal_form().simplify();
        let (labeled_pltl, context) = LabeledPLTL::new(&pltl);
        // println!("{}", ctx);
        // println!("{}", context);

        // println!("{}", labeled_pltl);
        // println!("===");
        // fixme: 00 and 10, 01 and 11 should give different results
        for letter in 0..4 {
            println!("===");
            let result = after_function(&context, &labeled_pltl, letter);
            println!("ch={:02b},result={}", letter, result.simplify());
            println!("===");
        }
    }
}
