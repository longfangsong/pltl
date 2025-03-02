use std::collections::HashSet;

use crate::{
    pltl::{after_function::after_function, utils::disjunction, Annotated, BinaryOp, PLTL},
    utils::{BitSet, BitSet32},
};

use super::Context;

pub fn transition(
    ctx: &Context,
    u_set: BitSet32,
    state: &(PLTL, PLTL),
    bed_next_state: &[Annotated],
    letter: &HashSet<u32>,
) -> (PLTL, PLTL) {
    let after_function_first_part = after_function(&state.0, letter).normal_form();
    let second_part = if matches!(state.1, PLTL::Bottom) {
        let mut result = Vec::with_capacity(ctx.c_sets.len());
        for (c, bed_state) in ctx.c_sets.iter().zip(bed_next_state.iter()) {
            let mut rewrite_u_set_with_c = HashSet::new();
            for u_item in u_set.iter().map(|u| ctx.u_type_subformulas[u as usize]) {
                let annotated = Annotated::from_pltl(u_item, &ctx.psf_context);
                let rewritten = annotated.rewrite_with_set(&ctx.psf_context, c);
                rewrite_u_set_with_c.insert(rewritten.to_pltl(&ctx.psf_context));
            }
            let item = PLTL::new_binary(
                BinaryOp::And,
                after_function_first_part.v_rewrite(&rewrite_u_set_with_c),
                bed_state
                    .to_pltl(&ctx.psf_context)
                    .v_rewrite(&rewrite_u_set_with_c),
            );
            result.push(item);
        }
        disjunction(result.into_iter())
    } else {
        after_function(&state.1, letter)
    };
    (after_function_first_part, second_part.normal_form())
}

// Fin(state)
pub fn is_accepting_state(state: &(PLTL, PLTL)) -> bool {
    matches!(state.1, PLTL::Bottom)
}
