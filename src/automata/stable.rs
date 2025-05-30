use super::{hoa::format::AcceptanceName, weakening_conditions, Context, HoaAutomatonBuilder};
use crate::{
    pltl::{
        self,
        labeled::{after_function::after_function, LabeledPLTL},
        BinaryOp,
    },
    utils::{BitSet, BitSet32},
};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};

pub fn transition(
    ctx: &Context,
    m_set: BitSet32,
    state: &(LabeledPLTL, LabeledPLTL),
    bed_next_state: &[LabeledPLTL],
    letter: BitSet32,
) -> (LabeledPLTL, LabeledPLTL) {
    let after_function_first_part = after_function(&state.0, letter, &ctx.local_after_cache);
    let second_part = if matches!(state.1, LabeledPLTL::Bottom) {
        let result: Vec<_> = bed_next_state
            .into_par_iter()
            .enumerate()
            .map(|(i, bed_state)| {
                let first_part_in_second = after_function_first_part.clone();
                let first_part_in_second =
                    ctx.cached_m_set_under_c_rewrite(m_set, i as u32, &first_part_in_second);
                let second_part_in_second = bed_state.clone();
                let second_part_in_second =
                    ctx.cached_m_set_under_c_rewrite(m_set, i as u32, &second_part_in_second);
                first_part_in_second & second_part_in_second
            })
            .collect();
        LabeledPLTL::Logical(BinaryOp::Or, result).simplify()
    } else {
        after_function(&state.1, letter, &ctx.local_after_cache)
    };
    (after_function_first_part, second_part)
}

pub fn initial_state(ctx: &Context, m_set: BitSet32) -> (LabeledPLTL, LabeledPLTL) {
    let second_part = ctx.initial.clone();
    let second_part = ctx.cached_v_rewrite(&second_part, m_set);
    (ctx.initial.clone(), second_part.simplify())
}

pub type State = (LabeledPLTL, LabeledPLTL, Vec<LabeledPLTL>);

// Fin(state)
pub fn is_accepting_state(state: &State) -> bool {
    matches!(state.1, LabeledPLTL::Bottom)
}

pub fn format_state(state: &State, pltl_ctx: &pltl::Context) -> String {
    format!(
        "<{}, {}>, <{}>",
        state.0.format(pltl_ctx),
        state.1.format(pltl_ctx),
        state
            .2
            .iter()
            .map(|x| x.format(pltl_ctx))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub fn dump(
    ctx: &Context,
    pltl_ctx: &pltl::Context,
    m_set: BitSet32,
    weakening_condition_automata: &HoaAutomatonBuilder<
        weakening_conditions::State,
        impl Fn(&weakening_conditions::State, &pltl::Context) -> String,
    >,
) -> HoaAutomatonBuilder<State, impl Fn(&State, &pltl::Context) -> String + Clone> {
    let init_state = initial_state(ctx, m_set);
    let init_state = (
        init_state.0,
        init_state.1,
        weakening_condition_automata.init_state.clone(),
    );
    let mut result = HoaAutomatonBuilder::new(
        format!("stable_0b{m_set:b}"),
        AcceptanceName::CoBuchi,
        init_state.clone(),
        is_accepting_state,
        Some(format_state),
    );
    let mut pending_states: Vec<State> = vec![init_state];
    let mut id = 0;
    while let Some((state_0, state_1, weakening_condition_state)) = pending_states.pop() {
        if result.transitions.contains_key(&(
            state_0.clone(),
            state_1.clone(),
            weakening_condition_state.clone(),
        )) {
            continue;
        }
        if let std::collections::hash_map::Entry::Vacant(e) = result.state_id_map.entry((
            state_0.clone(),
            state_1.clone(),
            weakening_condition_state.clone(),
        )) {
            e.insert(id);
            id += 1;
        }
        let letter_power_set = BitSet32::power_set_of_size(pltl_ctx.atoms.len());
        let wc_transitions = &weakening_condition_automata.transitions;
        let next_states: Vec<_> = letter_power_set
            .into_par_iter()
            .map(|letter| {
                if weakening_condition_state.is_empty() {
                    return (state_0.clone(), state_1.clone(), Vec::new());
                }
                let weakening_condition_next_state =
                    &wc_transitions[&weakening_condition_state][letter as usize];
                let next_state = transition(
                    ctx,
                    m_set,
                    &(state_0.clone(), state_1.clone()),
                    weakening_condition_next_state,
                    letter,
                );
                // for T, T and F, F, we don't need to check the weakening condition
                let weakening_condition_next_state = if (next_state.0 == LabeledPLTL::Bottom
                    || next_state.0 == LabeledPLTL::Top)
                    && next_state.0 == next_state.1
                {
                    Vec::new()
                } else {
                    weakening_condition_next_state.clone()
                };
                (next_state.0, next_state.1, weakening_condition_next_state)
            })
            .collect();
        for (next_state_0, next_state_1, weakening_condition_next_state) in &next_states {
            pending_states.push((
                next_state_0.clone(),
                next_state_1.clone(),
                weakening_condition_next_state.clone(),
            ));
        }
        result
            .transitions
            .insert((state_0, state_1, weakening_condition_state), next_states);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{automata::Context, pltl::PLTL};
    use std::time::Instant;

    #[test]
    fn test_dump_hoa() {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build_global()
            .unwrap();
        let (ltl, ltl_ctx) = PLTL::from_string(r#"Y(Y(Y p))"#).unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        let start = Instant::now();
        let ctx = Context::new(&ltl, &ltl_ctx);
        let ctx_time = start.elapsed().as_nanos() as usize;
        println!("ctx_time: {}ms", ctx_time / (1000 * 1000));
        println!("ctx: {ctx}");
        let weakening_condition_automata = weakening_conditions::dump(&ctx, &ltl_ctx);
        let wc_time = start.elapsed().as_nanos() as usize;
        println!("wc_time: {}ms", wc_time / (1000 * 1000));
        let init_state = initial_state(&ctx, 0b0);
        println!(
            "init: {}",
            format_state(
                &(
                    init_state.0,
                    init_state.1,
                    weakening_condition_automata.init_state.clone()
                ),
                &ltl_ctx
            )
        );
        for m in 0u32..(1 << ctx.u_items.len()) {
            let dump = dump(&ctx, &ltl_ctx, m, &weakening_condition_automata);
            println!("m_set: 0b{:b}, dump: {}", m, dump.transitions.len());
        }
        for (c_set, cache) in ctx.m_set_under_c_rewrite_cache.iter().enumerate() {
            println!("m_set: 0b{c_set:b}");
            for (item, map) in cache.iter() {
                println!("  c_set: 0b{item:b}");
                for kv in map.iter() {
                    println!("    {} -> {}", kv.key(), kv.value());
                }
            }
        }
    }
}
