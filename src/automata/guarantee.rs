use super::{weakening_conditions, Context, HoaAutomatonBuilder};
use crate::{
    automata::hoa::format::AcceptanceName,
    pltl::{
        self,
        labeled::{after_function::after_function, LabeledPLTL},
        BinaryOp,
    },
    utils::{BitSet, BitSet32},
};
use rayon::iter::{IntoParallelIterator, ParallelIterator};

pub fn transition(
    ctx: &Context,
    u_item_id: u32,
    n_set: BitSet32,
    state: &LabeledPLTL,
    bed_next_state: &[LabeledPLTL],
    letter: BitSet32,
) -> LabeledPLTL {
    if matches!(state, LabeledPLTL::Top) {
        let mut result = Vec::with_capacity(1 << ctx.label_context.past_subformulas.len());
        for (c, bed_state) in bed_next_state.iter().enumerate() {
            let c = c as BitSet32;
            let first_part = ctx.u_items[u_item_id as usize].clone();
            let first_part = first_part.c_rewrite(c);
            let first_part = first_part.u_rewrite(&ctx.n_sets[n_set as usize]);
            let first_part = LabeledPLTL::Until {
                weak: false,
                lhs: Box::new(LabeledPLTL::Top),
                rhs: Box::new(first_part),
            };
            let second_part = bed_state.clone();
            let second_part = second_part.u_rewrite(&ctx.n_sets[n_set as usize]);
            result.push(first_part & second_part);
        }
        LabeledPLTL::Logical(BinaryOp::Or, result).simplify()
    } else {
        after_function(state, letter).simplify()
    }
}

pub fn initial_state(ctx: &Context, u_item_id: u32, n_set: BitSet32) -> LabeledPLTL {
    let u_item = ctx.u_items[u_item_id as usize].clone();
    let u_item = u_item.u_rewrite(&ctx.n_sets[n_set as usize]);
    LabeledPLTL::Until {
        weak: false,
        lhs: Box::new(LabeledPLTL::Top),
        rhs: Box::new(u_item),
    }
    .simplify()
}

pub type State = (LabeledPLTL, Vec<LabeledPLTL>);

// Inf(state)
pub fn is_accepting_state(state: &State) -> bool {
    matches!(state.0, LabeledPLTL::Top)
}

pub fn format_state(state: &State, pltl_ctx: &pltl::Context) -> String {
    format!(
        "{}, <{}>",
        state.0.format(pltl_ctx),
        state
            .1
            .iter()
            .map(|x| x.format(pltl_ctx))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub fn dump<'ctx, 'state: 'ctx>(
    ctx: &'ctx Context,
    pltl_ctx: &pltl::Context,
    u_item_id: u32,
    v_set: BitSet32,
    weakening_condition_automata: &HoaAutomatonBuilder<
        weakening_conditions::State,
        impl Fn(&weakening_conditions::State, &pltl::Context) -> String,
    >,
) -> HoaAutomatonBuilder<State, impl Fn(&State, &pltl::Context) -> String + Clone> {
    let init_state = initial_state(ctx, u_item_id, v_set);
    let init_state = (init_state, weakening_condition_automata.init_state.clone());
    let mut result = HoaAutomatonBuilder::new(
        format!("guarantee_{u_item_id}_0b{v_set:b}"),
        AcceptanceName::Buchi,
        init_state.clone(),
        is_accepting_state,
        Some(format_state),
    );
    let mut pending_states: Vec<State> = vec![init_state];
    let mut id = 0;
    while let Some((state, weakening_condition_state)) = pending_states.pop() {
        if result
            .transitions
            .contains_key(&(state.clone(), weakening_condition_state.clone()))
        {
            continue;
        }
        if let std::collections::hash_map::Entry::Vacant(e) = result
            .state_id_map
            .entry((state.clone(), weakening_condition_state.clone()))
        {
            e.insert(id);
            id += 1;
        }
        let letter_power_set = BitSet32::power_set_of_size(pltl_ctx.atoms.len());
        let wc_automata_transitions = &weakening_condition_automata.transitions;
        let next_states: Vec<_> = letter_power_set
            .into_par_iter()
            .map(|letter| {
                let weakening_condition_next_state =
                    &wc_automata_transitions[&weakening_condition_state][letter as usize];
                let next_state = transition(
                    ctx,
                    u_item_id,
                    v_set,
                    &state,
                    weakening_condition_next_state,
                    letter,
                );
                (next_state, weakening_condition_next_state.clone())
            })
            .collect();
        for (next_state, weakening_condition_next_state) in &next_states {
            pending_states.push((next_state.clone(), weakening_condition_next_state.clone()));
        }
        result
            .transitions
            .insert((state, weakening_condition_state), next_states);
    }
    result
}

// pub fn dump_hoa(
//     ctx: &Context,
//     u_item_id: u32,
//     n_set: BitSet32,
//     weakening_condition_automata: &AutomataDump<weakening_conditions::State>,
// ) -> HoaAutomaton {
//     let init_state = initial_state(ctx, u_item_id, n_set);
//     let dump = dump(
//         ctx,
//         u_item_id,
//         n_set,
//         &init_state,
//         weakening_condition_automata,
//     );
//     let mut states = Vec::with_capacity(dump.state_id_map.len());
//     for (from, targets) in &dump.transitions {

//     }
//     HoaAutomaton::from_parts(
//         Header::from_vec(vec![
//             HeaderItem::v1(),
//             HeaderItem::Name(format!("guarantee_{}_0b{:b}", u_item_id, n_set)),
//             HeaderItem::Start(StateConjunction::singleton(
//                 dump.state_id_map[&(
//                     init_state.clone(),
//                     weakening_condition_automata.init_state.clone(),
//                 )] as _,
//             )),
//             HeaderItem::AcceptanceName(AcceptanceName::Buchi, vec![AcceptanceInfo::Int(1)]),
//             HeaderItem::Acceptance(1, AcceptanceCondition::Inf(AcceptanceAtom::Positive(0))),
//             HeaderItem::Properties(vec![
//                 Property::Deterministic,
//                 Property::Complete,
//                 Property::StateAcceptance,
//             ]),
//             HeaderItem::AP(ctx.pltl_context.atoms.clone()),
//         ]),
//         states.into(),
//     )
// }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{automata::Context, pltl::PLTL};

    #[test]
    fn test_dump_hoa() {
        let (ltl, ltl_ctx) = PLTL::from_string("F (Y p)").unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        println!("ltl: {ltl}");
        let ctx = Context::new(&ltl);
        println!("ctx: {ctx}");
        let weakening_condition_automata = weakening_conditions::dump(&ctx, &ltl_ctx);
        let dump = dump(&ctx, &ltl_ctx, 0, 0, &weakening_condition_automata);
        for (state, transitions) in &dump.transitions {
            println!("{}", format_state(state, &ltl_ctx));
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
