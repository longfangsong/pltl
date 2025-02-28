use std::collections::HashSet;

use super::Context;
use crate::{
    pltl::{
        after_function::after_function, utils::disjunction, Annotated, BinaryOp, UnaryOp, PLTL,
    },
    utils::{BitSet, BitSet32},
};

pub fn transition(
    ctx: &Context,
    v_item_id: u32,
    u_set: BitSet32,
    state: &PLTL,
    bed_next_state: &[Annotated],
    letter: &HashSet<String>,
) -> PLTL {
    if matches!(state, PLTL::Bottom) {
        let mut result = Vec::with_capacity(ctx.c_sets.len());
        for (c, bed_state) in ctx.c_sets.iter().zip(bed_next_state.iter()) {
            let v_item = ctx.v_type_subformulas[v_item_id as usize];
            let rewrite_v_with_c = v_item.v_rewrite(&c.to_pltl_set(&ctx.psf_context));
            let mut rewrite_u_set_with_c = HashSet::new();
            for u_item in u_set.iter().map(|u| ctx.u_type_subformulas[u as usize]) {
                let annotated = Annotated::from_pltl(u_item, &ctx.psf_context);
                let rewritten = annotated.rewrite_with_set(&ctx.psf_context, c);
                rewrite_u_set_with_c.insert(rewritten.to_pltl(&ctx.psf_context));
            }
            let first_part = rewrite_v_with_c.v_rewrite(&rewrite_u_set_with_c);
            let second_part = bed_state
                .to_pltl(&ctx.psf_context)
                .v_rewrite(&rewrite_u_set_with_c);
            let item = PLTL::new_binary(
                BinaryOp::And,
                PLTL::new_unary(UnaryOp::Globally, first_part).normal_form(),
                second_part,
            );
            result.push(item);
        }
        disjunction(result.into_iter()).simplify()
    } else {
        after_function(state, letter).simplify()
    }
}

// Fin(state)
pub fn is_accepting_state(state: &PLTL) -> bool {
    matches!(state, PLTL::Bottom)
}

pub type SafetyStateGivenM = Vec<PLTL>;
