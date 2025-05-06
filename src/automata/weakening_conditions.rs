use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use super::{hoa::format::AcceptanceName, HoaAutomatonBuilder};
use crate::pltl::labeled::after_function::local_after;
// use crate::pltl::labeled::info::psf_weaken_condition;
use crate::{
    automata::Context,
    pltl::{self, labeled::LabeledPLTL},
    utils::{BitSet, BitSet32},
};

pub fn transition(ctx: &Context, current: &[LabeledPLTL], letter: BitSet32) -> Vec<LabeledPLTL> {
    current
        .par_iter()
        .enumerate()
        .map(|(i, _)| {
            let mut result_i = Vec::new();
            'outer: for &j in &ctx.saturated_c_sets[i] {
                let mut result = local_after(&current[j as usize], letter, i as u32);
                if result == LabeledPLTL::Bottom {
                    continue;
                }
                for c_i_item in (i as u32).iter() {
                    let wc = &ctx.label_context.past_subformulas[c_i_item as usize]
                        .clone()
                        .c_rewrite(j)
                        .weaken_condition();
                    let after_wc = local_after(wc, letter, i as u32);
                    if after_wc == LabeledPLTL::Bottom {
                        continue 'outer;
                    }
                    result = result & after_wc;
                }
                result_i.push(result);
            }

            result_i
                .into_iter()
                .reduce(|acc, item| acc | item)
                .unwrap_or(LabeledPLTL::Bottom)
                .simplify()
        })
        .collect()
}

pub fn initial_state(ctx: &Context) -> Vec<LabeledPLTL> {
    let mut result: Vec<LabeledPLTL> = std::iter::repeat_n(
        LabeledPLTL::Bottom,
        1 << ctx.label_context.past_subformulas.len(),
    )
    .collect();
    result[ctx.initial.weaken_state() as usize] = LabeledPLTL::Top;
    result
}

pub type State = Vec<LabeledPLTL>;

pub fn format_state(state: &State, pltl_ctx: &pltl::Context) -> String {
    format!(
        "<{}>",
        state
            .iter()
            .map(|x| x.format(pltl_ctx))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub fn dump(
    ctx: &Context,
    pltl_ctx: &pltl::Context,
) -> HoaAutomatonBuilder<State, impl Fn(&State, &pltl::Context) -> String> {
    let init_state = initial_state(ctx);
    let mut result = HoaAutomatonBuilder::new(
        "weakening_conditions".to_string(),
        AcceptanceName::None,
        init_state.clone(),
        |_| false,
        Some(format_state),
    );
    let mut pending_states: Vec<State> = Vec::new();
    let mut id = 0;
    pending_states.push(init_state.to_vec());
    while let Some(state) = pending_states.pop() {
        if result.transitions.contains_key(&state) {
            continue;
        }
        if !result.state_id_map.contains_key(&state) {
            result.state_id_map.insert(state.clone(), id);
            id += 1;
        }
        let letter_power_set = BitSet32::power_set_of_size(pltl_ctx.atoms.len());
        let next_states: Vec<_> = letter_power_set
            .into_par_iter()
            .map(|letter| transition(ctx, &state, letter))
            .collect();

        for next_state in &next_states {
            pending_states.push(next_state.clone());
        }
        result.transitions.insert(state, next_states);
    }
    result
}

#[cfg(test)]
mod tests {
    use crate::pltl::PLTL;

    use super::*;

    #[test]
    fn test_dump() {
        let (ltl, ltl_ctx) = PLTL::from_string(
            "G(p U q)",
        )
        .unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        println!("ltl: {ltl}");
        let ctx = Context::new(&ltl);
        println!("ctx: {ctx}");
        let dump = dump(&ctx, &ltl_ctx);
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
