use std::collections::HashSet;

use crate::pltl::{after_function::local_after_annotated, Annotated, BinaryOp};

use super::Context;
fn is_saturated(ctx: &Context, i: usize, j: usize) -> bool {
    for psf0 in ctx.c_sets[ctx.init_c].iter() {
        for psf1 in ctx.c_sets[ctx.init_c].iter() {
            if psf0.rewrite(&ctx.psf_context, &ctx.c_sets[i]) == psf1.rewrite(&ctx.psf_context, &ctx.c_sets[j])
                && psf0.rewrite(&ctx.psf_context, &ctx.c_sets[i]) != psf1.rewrite(&ctx.psf_context, &ctx.c_sets[j])
            {
                return false;
            }
        }
    }
    true
}

pub fn rewrite_condition_function(
    ctx: &Context,
    current: &[Annotated],
    letter: &HashSet<u32>,
) -> Vec<Annotated> {
    let k = ctx.c_sets.len();
    let mut result = Vec::with_capacity(current.len());

    for (i, _) in current.iter().enumerate() {
        let mut current_result_i = None;
        for j in 0..k {
            if is_saturated(ctx, i, j) {
                let part_1 = local_after_annotated(&ctx.psf_context, &current[j], letter, &ctx.c_rewrite_c_sets[i][j]);
                let result = ctx.c_sets[i]
                    .iter()
                    .map(|ci| {
                        local_after_annotated(
                            &ctx.psf_context,
                            &ci.rewrite(&ctx.psf_context, &ctx.c_sets[j]).weaken_condition(&ctx.psf_context),
                            letter,
                            &ctx.c_rewrite_c_sets[i][j],
                        )
                    })
                    .fold(part_1, |acc, part| {
                        Annotated::new_binary(BinaryOp::And, acc, part)
                    });
                if let Some(current_result_i_content) = current_result_i {
                    current_result_i = Some(Annotated::new_binary(
                        BinaryOp::Or,
                        current_result_i_content,
                        result,
                    ));
                } else {
                    current_result_i = Some(result);
                }
            }
        }
        result.push(current_result_i.unwrap().simplify());
    }
    result
}
