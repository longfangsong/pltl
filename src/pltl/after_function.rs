use super::{
    utils::{conjunction, disjunction},
    BinaryOp, UnaryOp, PLTL,
};
use crate::utils::{powerset, BitSet, BitSet32, Set};

fn local_post_update(f: &PLTL, letter: BitSet32, past_st: &Set<PLTL>) -> PLTL {
    let mut first_part = f.clone();
    first_part.rewrite_with_set(past_st);
    let psf_set: Set<PLTL> = f.past_subformulas().into_iter().cloned().collect();
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

pub fn local_after(f: &PLTL, letter: BitSet32, past_st: &Set<PLTL>) -> PLTL {
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
            BinaryOp::Since | BinaryOp::WeakSince | BinaryOp::BackTo | BinaryOp::WeakBackTo,
            _,
            _,
        ) => local_after(&f.weaken_condition(), letter, past_st),
        _ => unreachable!("local_after"),
    }
}

pub fn after_function(f: &PLTL, letter: BitSet32) -> PLTL {
    let psf_set: Set<PLTL> = f.past_subformulas().into_iter().cloned().collect();
    let powerset = powerset(psf_set);
    let result = disjunction(powerset.iter().map(|set| local_after(f, letter, set))).simplify();
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pltl::PLTL;

    #[test]
    fn test_after_function() {
        let (pltl, _) = PLTL::from_string("G (p | Y q)").unwrap();
        let pltl = pltl.to_no_fgoh().to_negation_normal_form().simplify();
        let result = after_function(&pltl, 0b01);
        println!("result: {result}");
    }

    #[test]
    fn test_after_function_2() {
        let (pltl, _) = PLTL::from_string("F ( r & (r S p) )").unwrap();
        let pltl = pltl.to_no_fgoh().to_negation_normal_form().simplify();
        let result = after_function(&pltl, 0b10);
        println!("result: {result}");

        let result = after_function(&result, 0b00);
        println!("result: {result}");
    }
}
