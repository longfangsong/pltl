
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use super::{AutomataDump, Context};
use crate::pltl::labeled::after_function::local_after;
use crate::pltl::labeled::info::psf_weaken_condition;
use crate::pltl::BinaryOp;
use crate::utils::{BitSet, Map};
use crate::{pltl::labeled::LabeledPLTL, utils::BitSet32};

pub fn transition(ctx: &Context, current: &[LabeledPLTL], letter: BitSet32) -> Vec<LabeledPLTL> {
    let result = current
        .par_iter()
        .enumerate()
        .map(|(i, _)| {
            let mut result_i = Vec::new();
            'outer: for &j in &ctx.saturated_c_sets[i] {
                let mut result =
                    local_after(&ctx.psf_context, &current[j as usize], letter, i as u32);
                if result == LabeledPLTL::Bottom {
                    continue;
                }
                for c_i_item in (i as u32).iter() {
                    let wc = psf_weaken_condition(&ctx.psf_context, c_i_item, j);
                    let after_wc = local_after(&ctx.psf_context, &wc, letter, i as u32);
                    if after_wc == LabeledPLTL::Bottom {
                        continue 'outer;
                    }
                    result = LabeledPLTL::new_binary(BinaryOp::And, result, after_wc);
                }
                result_i.push(result);
            }

            result_i
                .into_iter()
                .reduce(|acc, item| LabeledPLTL::new_binary(BinaryOp::Or, acc, item))
                .unwrap_or(LabeledPLTL::Bottom)
                .simplify()
        })
        .collect();
    result
}

pub fn initial_state(ctx: &Context) -> Vec<LabeledPLTL> {
    let mut result: Vec<LabeledPLTL> = std::iter::repeat_n(LabeledPLTL::Bottom, 1 << ctx.psf_context.expand_once.len())
        .collect();
    result[ctx.psf_context.initial_weaken_state as usize] = LabeledPLTL::Top;
    result
}

pub type State = Vec<LabeledPLTL>;

pub fn dump(ctx: &Context) -> AutomataDump<State> {
    let init_state = initial_state(ctx);
    let mut transitions = Map::default();
    let mut pending_states: Vec<State> = Vec::new();
    let mut state_id_map = Map::default();
    let mut id = 0;
    pending_states.push(init_state.to_vec());
    while let Some(state) = pending_states.pop() {
        if transitions.contains_key(&state) {
            continue;
        }
        if !state_id_map.contains_key(&state) {
            state_id_map.insert(state.clone(), id);
            id += 1;
        }
        let letter_power_set = BitSet32::power_set_of_size(ctx.pltl_context.atoms.len());
        let next_states: Vec<_> = letter_power_set
            .into_par_iter()
            .map(|letter| transition(ctx, &state, letter))
            .collect();

        for next_state in &next_states {
            pending_states.push(next_state.clone());
        }
        transitions.insert(state, next_states);
    }
    AutomataDump {
        state_id_map,
        init_state: init_state.to_vec(),
        transitions,
    }
}

#[cfg(test)]
mod tests {
    use crate::pltl::PLTL;

    use super::*;

    #[test]
    fn test_dump() {
        let (ltl, ltl_ctx) = PLTL::from_string("Y (p ~S q)").unwrap();
        let ctx = Context::new(&ltl, ltl_ctx);
        println!("ctx: {}", ctx );
        let dump = dump(&ctx);
        for (state, transitions) in &dump.transitions {
            println!(
                "{}",
                state
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            for (character, transition) in transitions.iter().enumerate() {
                println!(
                    "  0b{:b} -> {}",
                    character,
                    transition
                        .iter()
                        .map(|x| x.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
        }
    }
}
