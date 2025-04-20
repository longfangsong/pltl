use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{pltl::{labeled::{after_function::after_function, LabeledPLTL}, utils::disjunction_labeled, BinaryOp}, utils::{character_to_label_expression, BitSet32, Map}};

use super::{hoa::{self, body::{Edge, Label}, format::{AcceptanceAtom, AcceptanceCondition, AcceptanceInfo, AcceptanceName, AcceptanceSignature, Property, StateConjunction}, header::{Header, HeaderItem}, AbstractLabelExpression, HoaAutomaton}, weakening_conditions, AutomataDump, Context};
use crate::utils::BitSet;


pub fn transition(
    ctx: &Context,
    m_set: BitSet32,
    state: &(LabeledPLTL, LabeledPLTL),
    bed_next_state: &[LabeledPLTL],
    letter: BitSet32,
) -> (LabeledPLTL, LabeledPLTL) {
    let after_function_first_part = after_function(&ctx.psf_context,&state.0, letter);
    let second_part = if matches!(state.1, LabeledPLTL::Bottom) {
        let mut result = Vec::with_capacity(1 << ctx.psf_context.expand_once.len());
        for bed_state in bed_next_state {
            let mut first_part_in_second = after_function_first_part.clone();
            first_part_in_second.v_rewrite(&ctx.m_sets[m_set as usize], &ctx.psf_context);
            let mut second_part_in_second = bed_state.clone();
            second_part_in_second.v_rewrite(&ctx.m_sets[m_set as usize], &ctx.psf_context);

            let item = LabeledPLTL::new_binary(
                BinaryOp::And,
                first_part_in_second,
                second_part_in_second,
            );
            result.push(item);
        }
        disjunction_labeled(result.into_iter())
    } else {
        after_function(&ctx.psf_context, &state.1, letter)
    };
    (after_function_first_part.simplify(), second_part.simplify())
}

pub fn initial_state(ctx: &Context, m_set: BitSet32) -> (LabeledPLTL, LabeledPLTL) {
    let mut second_part = ctx.labeled_pltl.clone();
    second_part.v_rewrite(&ctx.m_sets[m_set as usize], &ctx.psf_context);
    (ctx.labeled_pltl.clone(), second_part.simplify())
}

// Fin(state)
pub fn is_accepting_state(state: &(LabeledPLTL, LabeledPLTL)) -> bool {
    matches!(state.1, LabeledPLTL::Bottom)
}

pub type State = (LabeledPLTL, LabeledPLTL, Vec<LabeledPLTL>);

fn dump(
    ctx: &Context,
    m_set: BitSet32,
    init_state: &(LabeledPLTL, LabeledPLTL),
    weakening_condition_automata: &AutomataDump<weakening_conditions::State>,
) -> AutomataDump<State> {
    let mut state_id_map = Map::default();
    let mut id = 0;
    let mut transitions = Map::default();
    let mut pending_states: Vec<State> = Vec::new();
    pending_states.push((
        init_state.0.clone(),
        init_state.1.clone(),
        weakening_condition_automata.init_state.clone(),
    ));
    while let Some((state_0, state_1, weakening_condition_state)) = pending_states.pop() {
        if transitions.contains_key(&(state_0.clone(), state_1.clone(), weakening_condition_state.clone())) {
            continue;
        }
        if let std::collections::hash_map::Entry::Vacant(e) = state_id_map.entry((state_0.clone(), state_1.clone(), weakening_condition_state.clone())) {
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
                    m_set,
                    &(state_0.clone(), state_1.clone()),
                    weakening_condition_next_state,
                    letter,
                );
                (next_state.0, next_state.1, weakening_condition_next_state.clone())
            })
            .collect();
        for (next_state_0, next_state_1, weakening_condition_next_state) in &next_states {
            pending_states.push((next_state_0.clone(), next_state_1.clone(), weakening_condition_next_state.clone()));
        }
        transitions.insert((state_0, state_1, weakening_condition_state), next_states);
    }
    AutomataDump {
        state_id_map,
        init_state: (
            init_state.0.clone(),
            init_state.1.clone(),
            weakening_condition_automata.init_state.clone(),
        ),
        transitions,
    }
}

pub fn dump_hoa(
    ctx: &Context,
    m_set: BitSet32,
    weakening_condition_automata: &AutomataDump<weakening_conditions::State>,
) -> HoaAutomaton {
    let init_state = initial_state(ctx, m_set);
    let dump = dump(ctx, m_set, &init_state, weakening_condition_automata);
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
            Some(format!("<{}, {}>, <{}>", from.0.format(&ctx.psf_context, &ctx.pltl_context), from.1.format(&ctx.psf_context, &ctx.pltl_context), from.2.iter().map(|a| a.format(&ctx.psf_context, &ctx.pltl_context)).collect::<Vec<_>>().join(", ")),
            ),
            if is_accepting_state(&(from.0.clone(), from.1.clone())) {
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
            HeaderItem::Name(format!("stable_0b{:b}", m_set)),
            HeaderItem::Start(StateConjunction::singleton(dump.state_id_map[&(init_state.0.clone(), init_state.1.clone(), weakening_condition_automata.init_state.clone())] as _)),
            HeaderItem::AcceptanceName(AcceptanceName::CoBuchi, vec![AcceptanceInfo::Int(1)]),
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
    use crate::{automata::{hoa::output::to_hoa, Context}, pltl::PLTL};
    use super::*;

    #[test]
    fn test_dump_hoa() {
        let (ltl, ltl_ctx) = PLTL::from_string("G p | F q").unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        println!("ltl: {}", ltl);
        let ctx = Context::new(&ltl, ltl_ctx);
        println!("ctx: {}", ctx);
        let init_state = initial_state(&ctx, 0);
        let weakening_condition_init_state = weakening_conditions::initial_state(&ctx);
        let weakening_condition_automata = weakening_conditions::dump(&ctx);
        let dump = dump(&ctx, 0, &init_state, &weakening_condition_automata);
        for ((state_0, state_1, wc_state), transitions) in &dump.transitions {
            println!("{}, {}, <{}>", state_0, state_1, wc_state.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
            for (letter, (target_state_0, target_state_1, wc_target_state)) in transitions.iter().enumerate() {
                println!("  0b{:b} -> {}, {}, <{}>", letter, target_state_0, target_state_1, wc_target_state.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
            }
        }
        let hoa = dump_hoa(&ctx, 0, &weakening_condition_automata);
        println!("{}", to_hoa(&hoa));
    }
}


