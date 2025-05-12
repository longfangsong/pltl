use std::time::Instant;

use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{
    pltl::{
        self,
        labeled::{after_function::after_function, LabeledPLTL},
        BinaryOp,
    },
    utils::BitSet32,
};

use super::{hoa::format::AcceptanceName, weakening_conditions, Context, HoaAutomatonBuilder};
use crate::utils::BitSet;

pub fn transition(
    ctx: &Context,
    m_set: BitSet32,
    state: &(LabeledPLTL, LabeledPLTL),
    bed_next_state: &[LabeledPLTL],
    letter: BitSet32,
) -> (LabeledPLTL, LabeledPLTL) {
    let start = Instant::now();
    let after_function_first_part = after_function(&state.0, letter, &ctx.local_after_cache);
    let second_part = if matches!(state.1, LabeledPLTL::Bottom) {
        let result: Vec<_> = bed_next_state
            .into_par_iter()
            .map(|bed_state| {
                let first_part_in_second = after_function_first_part.clone();
                let first_part_in_second = ctx.cached_v_rewrite(&first_part_in_second, m_set);
                let second_part_in_second = bed_state.clone();
                let second_part_in_second = ctx.cached_v_rewrite(&second_part_in_second, m_set);
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
        let transitions = &weakening_condition_automata.transitions;
        let next_states: Vec<_> = letter_power_set
            .into_par_iter()
            .map(|letter| {
                let weakening_condition_next_state =
                    &transitions[&weakening_condition_state][letter as usize];
                let next_state = transition(
                    ctx,
                    m_set,
                    &(state_0.clone(), state_1.clone()),
                    weakening_condition_next_state,
                    letter,
                );
                (
                    next_state.0,
                    next_state.1,
                    weakening_condition_next_state.clone(),
                )
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

    #[test]
    fn test_dump_aaa_hoa() {
        let (ltl, ltl_ctx) = PLTL::from_string(            "¬(g0 & g1) & ¬(g0 & g2) & ¬(g1 & g0) & ¬(g1 & g2) & ¬(g2 & g0) & ¬(g2 & g1) & G(F(¬r0 ~S g0)) & G(F(¬r1 ~S g1)) & G(F(¬r2 ~S g2)) & G(g0 -> (r0 | Y(r0 B ¬g0))) & G(g1 -> (r1 | Y(r1 B ¬g1))) & G(g2 -> (r2 | Y(r2 B ¬g2)))",
    ).unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        println!("ltl: {ltl}");
        let ctx = Context::new(&ltl, &ltl_ctx);
        println!("ctx: {ctx}");
        let weakening_condition_automata = weakening_conditions::dump(&ctx, &ltl_ctx);
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
        let start = Instant::now();
        let dump = dump(&ctx, &ltl_ctx, 0b0, &weakening_condition_automata);
        // println!("dump: {}", dump.transitions.len());
        // println!("time: {}s", start.elapsed().as_secs_f32());
        // println!("transition time: {}s", TRANSITION_TIME.load(Ordering::Relaxed) as f32 / 1e9);
        // println!("af time: {}s", AF_TIME.load(Ordering::Relaxed) as f32 / 1e9);
        // println!("v write count: {}", V_WRITE_COUNT.load(Ordering::Relaxed));
        // println!(
        //     "v write time: {}s",
        //     V_REWRITE_CPU_TIME.load(Ordering::Relaxed) as f32 / 1e9
        // );
        // println!("cached count: {}", CACHED_COUNT.load(Ordering::Relaxed));
        // println!(
        //     "cached time: {}s",
        //     CACHED_CPU_TIME.load(Ordering::Relaxed) as f32 / 1e9
        // );
        // println!(
        //     "get time: {}s",
        //     GET_TIME.load(Ordering::Relaxed) as f32 / 1e9
        // );
        // println!(
        //     "af1 time: {}s",
        //     AF1_TIME.load(Ordering::Relaxed) as f32 / 1e9
        // );
        // println!(
        //     "af2 time: {}s",
        //     AF2_TIME.load(Ordering::Relaxed) as f32 / 1e9
        // );

        // println!(
        //     "af_cache read time: {}s",
        //     CACHE_READ_TIME.load(Ordering::Relaxed) as f32 / 1e9
        // );
        // println!(
        //     "af_cache write time: {}s",
        //     CACHE_WRITE_TIME.load(Ordering::Relaxed) as f32 / 1e9
        // );
        // println!(
        //     "af_calculation time: {}s",
        //     CALCULATION_TIME.load(Ordering::Relaxed) as f32 / 1e9
        // );
        // println!("first part in second time: {}s", FIRST_PART_IN_SECOND_TIME.load(Ordering::Relaxed) as f32 / 1e9);
        // println!("cached v rewrite time: {}s", CACHED_V_REWRITE_TIME.load(Ordering::Relaxed) as f32 / 1e9);
        // println!("clone time: {}s", CLONE_TIME.load(Ordering::Relaxed) as f32 / 1e9);
        println!("{}", dump.transitions.len());
        // for (state, transitions) in &dump.transitions {
        // println!("{}", format_state(state, &ltl_ctx));
        // for (character, transition_to) in transitions.iter().enumerate() {
        // println!(
        //     "  0b{:b} -> {}",
        //     character,
        //     format_state(transition_to, &ltl_ctx)
        // );
        //     }
        // }
    }
}
