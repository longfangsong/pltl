use std::collections::HashSet;

use super::Context;
use crate::{
    pltl::{after_function::after_function, utils::disjunction, Annotated, BinaryOp, PLTL},
    utils::{BitSet, BitSet32},
};

pub fn transition(
    ctx: &Context,
    u_item_id: u32,
    v_set: BitSet32,
    state: &PLTL,
    bed_next_state: &[Annotated],
    letter: &HashSet<String>,
) -> PLTL {
    let result = if matches!(state, PLTL::Top) {
        let mut result = Vec::with_capacity(ctx.c_sets.len());
        for (c, bed_state) in ctx.c_sets.iter().zip(bed_next_state.iter()) {
            let u_item = ctx.u_type_subformulas[u_item_id as usize];
            let rewrite_u_with_c = u_item.u_rewrite(&c.to_pltl_set(&ctx.psf_context));
            let mut rewrite_v_set_with_c = HashSet::new();
            for v_item in v_set.iter().map(|v| ctx.v_type_subformulas[v as usize]) {
                let annotated = Annotated::from_pltl(v_item, &ctx.psf_context);
                let rewritten = annotated.rewrite_with_set(&ctx.psf_context, c);
                rewrite_v_set_with_c.insert(rewritten.to_pltl(&ctx.psf_context));
            }
            let first_part = rewrite_u_with_c.u_rewrite(&rewrite_v_set_with_c);
            let second_part = bed_state
                .to_pltl(&ctx.psf_context)
                .u_rewrite(&rewrite_v_set_with_c);
            let item = PLTL::new_binary(
                BinaryOp::And,
                PLTL::new_binary(BinaryOp::Until, PLTL::Top, first_part),
                second_part,
            );
            result.push(item);
        }
        disjunction(result.into_iter()).simplify()
    } else {
        after_function(state, letter).simplify()
    };
    // println!("{} ={:?}=> {}", state, letter, result);
    result
}

// Inf(state)
pub fn is_accepting_state(state: &PLTL) -> bool {
    matches!(state, PLTL::Top)
}

pub type GuaranteeyStateGivenN = Vec<PLTL>;
