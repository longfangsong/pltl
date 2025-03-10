use std::collections::HashSet;

use super::{
    annotated::Annotated,
    past_subformula::{PastSubformulaSet, PastSubformularSetContext},
    utils::{conjunction, disjunction},
    BinaryOp, UnaryOp, PLTL,
};
use crate::utils::BitSet;
use crate::utils::{powerset, BitSet32};

fn local_post_update(f: &PLTL, letter: BitSet32, past_st: &HashSet<PLTL>) -> PLTL {
    let first_part = f.rewrite_with_set(past_st);
    let psf_set: HashSet<PLTL> = f.past_subformulas().into_iter().cloned().collect();
    let intersection: Vec<_> = psf_set
        .intersection(past_st)
        .map(|psf| local_after(&psf.weaken_condition(), letter, past_st))
        .collect();
    if intersection.is_empty() {
        first_part
    } else {
        let second_part = conjunction(intersection.into_iter());
        PLTL::new_binary(BinaryOp::And, first_part, second_part)
    }
}

fn local_post_update_annotated(
    ctx: &PastSubformularSetContext,
    f: &Annotated,
    letter: BitSet32,
    past_st: &PastSubformulaSet,
) -> Annotated {
    let mut result = f.rewrite_with_set(ctx, past_st);
    let psf_set = f.past_subformula_set(ctx);
    for psf in psf_set {
        if past_st.contains(ctx, &psf) {
            result = Annotated::new_binary(
                BinaryOp::And,
                result,
                local_after_annotated(ctx, &psf.weaken_condition(ctx), letter, past_st),
            )
        }
    }
    result
}

pub fn local_after_annotated(
    ctx: &PastSubformularSetContext,
    f: &Annotated,
    letter: BitSet32,
    past_st: &PastSubformulaSet,
) -> Annotated {
    match f {
        Annotated::Top => Annotated::Top,
        Annotated::Bottom => Annotated::Bottom,
        Annotated::Atom(atom) => {
            if letter.contains(*atom) {
                Annotated::Top
            } else {
                Annotated::Bottom
            }
        }
        Annotated::Unary(UnaryOp::Not, box Annotated::Atom(atom)) => {
            if letter.contains(*atom) {
                Annotated::Bottom
            } else {
                Annotated::Top
            }
        }
        Annotated::Unary(UnaryOp::Not, _) => unreachable!("Needs to push down not"),
        Annotated::Unary(UnaryOp::Next, box annotated) => {
            local_post_update_annotated(ctx, annotated, letter, past_st)
        }
        // Note (Weak) Yesterday may not necessary here since it is a past formula
        Annotated::Unary(UnaryOp::Yesterday, _) => Annotated::Bottom,
        Annotated::Unary(UnaryOp::WeakYesterday, _) => Annotated::Top,
        Annotated::PastSubformula(past_subformula) => {
            let psf_shape = ctx.past_subformulas[past_subformula.id as usize];
            let weaken = past_subformula.state.get(past_subformula.id);
            match (psf_shape, weaken) {
                (PLTL::Unary(UnaryOp::Yesterday | UnaryOp::WeakYesterday, _), true) => {
                    Annotated::Top
                }
                (PLTL::Unary(UnaryOp::Yesterday | UnaryOp::WeakYesterday, _), false) => {
                    Annotated::Bottom
                }
                (
                    PLTL::Binary(
                        BinaryOp::Before
                        | BinaryOp::WeakBefore
                        | BinaryOp::Since
                        | BinaryOp::WeakSince,
                        _,
                        _,
                    ),
                    _,
                ) => local_after_annotated(
                    ctx,
                    &past_subformula.weaken_condition(ctx),
                    letter,
                    past_st,
                ),
                _ => unreachable!("Not a psf"),
            }
        }
        Annotated::Binary(op @ (BinaryOp::And | BinaryOp::Or), box lhs, box rhs) => {
            let lhs_after = local_after_annotated(ctx, lhs, letter, past_st);
            let rhs_after = local_after_annotated(ctx, rhs, letter, past_st);
            Annotated::new_binary(*op, lhs_after, rhs_after)
        }
        Annotated::Binary(BinaryOp::Until | BinaryOp::WeakUntil, box lhs, box rhs) => {
            let lhs_after = local_after_annotated(ctx, lhs, letter, past_st);
            // println!("lhs_after: {}", lhs_after);
            let rhs_after = local_after_annotated(ctx, rhs, letter, past_st);
            // println!("rhs_after: {}", rhs_after);
            Annotated::new_binary(
                BinaryOp::Or,
                rhs_after,
                Annotated::new_binary(
                    BinaryOp::And,
                    lhs_after,
                    local_post_update_annotated(ctx, f, letter, past_st),
                ),
            )
        }
        Annotated::Binary(BinaryOp::Release | BinaryOp::MightyRelease, box lhs, box rhs) => {
            let lhs_after = local_after_annotated(ctx, lhs, letter, past_st);
            let rhs_after = local_after_annotated(ctx, rhs, letter, past_st);
            Annotated::new_binary(
                BinaryOp::And,
                rhs_after,
                Annotated::new_binary(
                    BinaryOp::Or,
                    lhs_after,
                    local_post_update_annotated(ctx, f, letter, past_st),
                ),
            )
        }
        Annotated::Unary(_, _) => unreachable!(),
        Annotated::Binary(_, _, _) => {
            dbg!(f);
            unreachable!()
        }
    }
    .simplify()
}

pub fn local_after(f: &PLTL, letter: BitSet32, past_st: &HashSet<PLTL>) -> PLTL {
    match f {
        PLTL::Top => PLTL::Top,
        PLTL::Bottom => PLTL::Bottom,
        PLTL::Atom(atom) => {
            if letter.contains(*atom) {
                PLTL::Top
            } else {
                PLTL::Bottom
            }
        }
        PLTL::Unary(UnaryOp::Not, box PLTL::Atom(atom)) => {
            if letter.contains(*atom) {
                PLTL::Bottom
            } else {
                PLTL::Top
            }
        }
        PLTL::Unary(UnaryOp::Not, _) => {
            unreachable!("Needs to push down not")
        }
        PLTL::Unary(UnaryOp::Next, box f) => local_post_update(f, letter, past_st),
        PLTL::Unary(UnaryOp::Yesterday, _) => PLTL::Bottom,
        PLTL::Unary(UnaryOp::WeakYesterday, _) => PLTL::Top,
        PLTL::Binary(op @ (BinaryOp::And | BinaryOp::Or), box lhs, box rhs) => {
            let lhs_after = local_after(lhs, letter, past_st);
            let rhs_after = local_after(rhs, letter, past_st);
            PLTL::new_binary(*op, lhs_after, rhs_after)
        }
        PLTL::Binary(BinaryOp::Until | BinaryOp::WeakUntil, box lhs, box rhs) => {
            let lhs_after = local_after(lhs, letter, past_st);
            let rhs_after = local_after(rhs, letter, past_st);
            let local_pu = local_post_update(f, letter, past_st);
            PLTL::new_binary(
                BinaryOp::Or,
                rhs_after,
                PLTL::new_binary(BinaryOp::And, lhs_after, local_pu),
            )
        }
        PLTL::Binary(BinaryOp::Release | BinaryOp::MightyRelease, box lhs, box rhs) => {
            let lhs_after = local_after(lhs, letter, past_st);
            let rhs_after = local_after(rhs, letter, past_st);
            let local_pu = local_post_update(f, letter, past_st);
            PLTL::new_binary(
                BinaryOp::And,
                rhs_after,
                PLTL::new_binary(BinaryOp::Or, lhs_after, local_pu),
            )
        }
        PLTL::Binary(
            BinaryOp::Since | BinaryOp::WeakSince | BinaryOp::Before | BinaryOp::WeakBefore,
            _,
            _,
        ) => local_after(&f.weaken_condition(), letter, past_st),
        _ => unreachable!(),
    }
}

pub fn after_function(f: &PLTL, letter: BitSet32) -> PLTL {
    let psf_set: HashSet<PLTL> = f.past_subformulas().into_iter().cloned().collect();
    let powerset = powerset(&psf_set);
    let result = disjunction(powerset.iter().map(|set| local_after(f, letter, set))).simplify();
    result
}

#[cfg(test)]
mod tests {
    use crate::pltl::rewrite::rewrite_set_with_set;

    use super::*;

    #[test]
    fn test_after_function() {
        let (f, mut dict) = PLTL::from_string("(p U Y q) S (p R q)");
        let ξ = PLTL::from_string_increment("(p U Y q) S (p R q)", &mut dict);
        let psf0 = PLTL::from_string_increment("Y q", &mut dict);
        let psf1 = f.clone();
        let c_j = HashSet::from([psf0.clone()]);
        let c_i = HashSet::from([psf0.clone(), psf1.clone()]);
        let letter = 0b01; // {p}
        let ξ_cj = ξ.rewrite_with_set(&c_j);
        println!("ξ<cj>: {}", ξ_cj);
        let ξ_cj_wc = ξ_cj.weaken_condition();
        println!("wc(ξ<cj>): {}", ξ_cj_wc);
        let c_i_cj = rewrite_set_with_set(&c_i, &c_j);
        println!("ci<cj>: {{{}}}", c_i_cj.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(", "));
        let result = local_after(&ξ_cj_wc, letter, &c_i_cj);
        println!("{}", result);
    }
}
