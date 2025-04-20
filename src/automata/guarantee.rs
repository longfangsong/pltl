use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{
    pltl::{
        labeled::{after_function::after_function, LabeledPLTL},
        utils::disjunction_labeled,
        BinaryOp,
    },
    utils::{character_to_label_expression, BitSet, BitSet32, Map, Set},
};

use super::{
    hoa::{
        self,
        body::{Edge, Label},
        format::{
            AcceptanceAtom, AcceptanceCondition, AcceptanceInfo, AcceptanceName,
            AcceptanceSignature, Property, StateConjunction,
        },
        header::{Header, HeaderItem},
        AbstractLabelExpression, HoaAutomaton,
    },
    weakening_conditions, AutomataDump, Context,
};

pub fn transition(
    ctx: &Context,
    u_item_id: u32,
    n_set: BitSet32,
    state: &LabeledPLTL,
    bed_next_state: &[LabeledPLTL],
    letter: BitSet32,
) -> LabeledPLTL {
    if matches!(state, LabeledPLTL::Top) {
        let mut result = Vec::with_capacity(1 << ctx.psf_context.expand_once.len());
        for (c, bed_state) in bed_next_state.iter().enumerate() {
            let c = c as BitSet32;
            let mut first_part = ctx.u_items[u_item_id as usize].clone();
            first_part.rewrite_with_set(c);
            first_part.u_rewrite(&ctx.n_sets[n_set as usize], &ctx.psf_context);
            let mut second_part = bed_state.clone();
            second_part.u_rewrite(&ctx.n_sets[n_set as usize], &ctx.psf_context);
            let item = LabeledPLTL::new_binary(
                BinaryOp::And,
                LabeledPLTL::new_binary(BinaryOp::Until, LabeledPLTL::Top, first_part),
                second_part,
            );
            result.push(item);
        }
        disjunction_labeled(result.into_iter()).simplify()
    } else {
        after_function(&ctx.psf_context, state, letter).simplify()
    }
}

pub fn initial_state(ctx: &Context, u_item_id: u32, n_set: BitSet32) -> LabeledPLTL {
    let mut u_item = ctx.u_items[u_item_id as usize].clone();
    // todo: use pre-computed n_set_items?
    let n_set_items: Set<_> = n_set
        .iter()
        .map(|v| ctx.v_items[v as usize].clone())
        .collect();
    u_item.u_rewrite(&n_set_items, &ctx.psf_context);
    LabeledPLTL::new_binary(BinaryOp::Until, LabeledPLTL::Top, u_item).simplify()
}

// Inf(state)
pub fn is_accepting_state(state: &LabeledPLTL) -> bool {
    matches!(state, LabeledPLTL::Top)
}

pub type State = (LabeledPLTL, Vec<LabeledPLTL>);

fn dump(
    ctx: &Context,
    u_item_id: u32,
    v_set: BitSet32,
    init_state: &LabeledPLTL,
    weakening_condition_automata: &AutomataDump<weakening_conditions::State>,
) -> AutomataDump<State> {
    let mut transitions = Map::default();
    let mut pending_states: Vec<State> = Vec::new();
    let mut state_id_map = Map::default();
    let mut id = 0;
    pending_states.push((
        init_state.clone(),
        weakening_condition_automata.init_state.clone(),
    ));
    while let Some((state, weakening_condition_state)) = pending_states.pop() {
        if transitions.contains_key(&(state.clone(), weakening_condition_state.clone())) {
            continue;
        }
        if let std::collections::hash_map::Entry::Vacant(e) = state_id_map.entry((state.clone(), weakening_condition_state.clone())) {
            e.insert(id);
            id += 1;
        }
        let letter_power_set = BitSet32::power_set_of_size(ctx.pltl_context.atoms.len());
        let next_states: Vec<_> = letter_power_set
            .into_par_iter()
            .map(|letter| {
                let weakening_condition_next_state = &weakening_condition_automata.transitions
                    [&weakening_condition_state][letter as usize];
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
        transitions.insert((state, weakening_condition_state), next_states);
    }
    AutomataDump {
        state_id_map,
        init_state: (
            init_state.clone(),
            weakening_condition_automata.init_state.clone(),
        ),
        transitions,
    }
}

pub fn dump_hoa(
    ctx: &Context,
    u_item_id: u32,
    n_set: BitSet32,
    weakening_condition_automata: &AutomataDump<weakening_conditions::State>,
) -> HoaAutomaton {
    let init_state = initial_state(ctx, u_item_id, n_set);
    let dump = dump(
        ctx,
        u_item_id,
        n_set,
        &init_state,
        weakening_condition_automata,
    );
    let mut states = Vec::with_capacity(dump.state_id_map.len());
    for (from, targets) in &dump.transitions {
        let from_id = dump.state_id_map[from];
        let edges = targets.iter().enumerate().map(|(letter, to)| {
            let to_id = dump.state_id_map[to];
            Edge::from_parts(
                Label(AbstractLabelExpression::Conjunction(
                    character_to_label_expression(letter as _, ctx.pltl_context.atoms.len()),
                )),
                StateConjunction::singleton(to_id as _),
                AcceptanceSignature::empty(),
            )
        });
        states.push(hoa::State::from_parts(
            from_id as _,
            Some(format!(
                "{}, <{}>",
                from.0.format(&ctx.psf_context, &ctx.pltl_context),
                from.1
                    .iter()
                    .map(|a| a.format(&ctx.psf_context, &ctx.pltl_context))
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
            if is_accepting_state(&from.0) {
                AcceptanceSignature(vec![0])
            } else {
                AcceptanceSignature::empty()
            },
            edges.collect(),
        ));
    }
    HoaAutomaton::from_parts(
        Header::from_vec(vec![
            HeaderItem::v1(),
            HeaderItem::Name(format!("guarantee_{}_0b{:b}", u_item_id, n_set)),
            HeaderItem::Start(StateConjunction::singleton(
                dump.state_id_map[&(
                    init_state.clone(),
                    weakening_condition_automata.init_state.clone(),
                )] as _,
            )),
            HeaderItem::AcceptanceName(AcceptanceName::Buchi, vec![AcceptanceInfo::Int(1)]),
            HeaderItem::Acceptance(1, AcceptanceCondition::Inf(AcceptanceAtom::Positive(0))),
            HeaderItem::Properties(vec![
                Property::Deterministic,
                Property::Complete,
                Property::StateAcceptance,
            ]),
            HeaderItem::AP(ctx.pltl_context.atoms.clone()),
        ]),
        states.into(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        automata::{hoa::output::to_hoa, Context},
        pltl::PLTL,
    };

    #[test]
    fn test_dump_hoa() {
        let (ltl, ltl_ctx) = PLTL::from_string("G p | F q").unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        println!("ltl: {}", ltl);
        let ctx = Context::new(&ltl, ltl_ctx);
        println!("ctx: {}", ctx);
        let init_state = initial_state(&ctx, 0, 0);
        let weakening_condition_automata = weakening_conditions::dump(&ctx);
        let dump = dump(&ctx, 0, 0, &init_state, &weakening_condition_automata);
        for ((state, wc_state), transitions) in &dump.transitions {
            println!(
                "{}, <{}>",
                state,
                wc_state
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            for (letter, (target_state, wc_target_state)) in transitions.iter().enumerate() {
                println!(
                    "  0b{:b} -> {}, <{}>",
                    letter,
                    target_state,
                    wc_target_state
                        .iter()
                        .map(|x| x.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
        }
        let hoa = dump_hoa(&ctx, 0, 0,&weakening_condition_automata);
        println!("{}", to_hoa(&hoa));
    }
}
