use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{
    pltl::{
        self,
        labeled::{after_function::after_function, LabeledPLTL},
        BinaryOp, PLTL,
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
    let after_function_first_part = after_function(&state.0, letter).simplify();
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
        LabeledPLTL::Logical(BinaryOp::Or, result)
    } else {
        after_function(&state.1, letter)
    };
    (after_function_first_part, second_part.simplify())
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

pub fn to_bench() {
    let (ltl, ltl_ctx) = PLTL::from_string(
        "G (F (p ->  X (X q) | (r & (p S (r S (Y p)))) | ( ((p S q) -> (r U t)) ) ))",
    )
    .unwrap();
    let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
    // println!("ltl: {ltl}");
    let ctx = Context::new(&ltl);
    // println!("ctx: {ctx}");
    let weakening_condition_automata = weakening_conditions::dump(&ctx, &ltl_ctx);
    let dump = dump(&ctx, &ltl_ctx, 0, &weakening_condition_automata);
    for (state, transitions) in &dump.transitions {
        // println!("{}", format_state(state, &ltl_ctx));
        for (character, transition_to) in transitions.iter().enumerate() {
            // println!(
            //     "  0b{:b} -> {}",
            //     character,
            //     format_state(transition_to, &ltl_ctx)
            // );
        }
    }
    println!("done");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{automata::Context, pltl::PLTL};

    #[test]
    fn test_dump_hoa() {
        // G (F (p ->  X (X q) | (r & (p S (r S (Y p)))) ))
        let (ltl, ltl_ctx) = PLTL::from_string(
            "G (F (p ->  X (X q) | (r & (p S (r S (Y p)))) | ( ((p S q) -> (r U t)) ) ))",
        )
        .unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        // println!("ltl: {ltl}");
        let ctx = Context::new(&ltl);
        // println!("ctx: {ctx}");
        let weakening_condition_automata = weakening_conditions::dump(&ctx, &ltl_ctx);
        let dump = dump(&ctx, &ltl_ctx, 0, &weakening_condition_automata);
        for (state, transitions) in &dump.transitions {
            // println!("{}", format_state(state, &ltl_ctx));
            for (character, transition_to) in transitions.iter().enumerate() {
                println!(
                    "  0b{:b} -> {}",
                    character,
                    format_state(transition_to, &ltl_ctx)
                );
            }
        }
    }
}
