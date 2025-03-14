use std::collections::HashSet;


use super::{hoa::{self, body::{Edge, Label}, format::{AcceptanceAtom, AcceptanceCondition, AcceptanceInfo, AcceptanceName, AcceptanceSignature, Property, StateConjunction}, header::{Header, HeaderItem}, AbstractLabelExpression, HoaAutomaton}, AutomataDump, Context};
use crate::{
    automata::weakening_conditions,
    pltl::{
        after_function::after_function, utils::disjunction, Annotated, BinaryOp, UnaryOp, PLTL,
    },
    utils::{character_to_label_expression, BitSet, BitSet32, Map, Set},
};

pub fn transition(
    ctx: &Context,
    u_item_id: u32,
    v_set: BitSet32,
    state: &PLTL,
    bed_next_state: &[Annotated],
    letter: BitSet32,
) -> PLTL {
    if matches!(state, PLTL::Top) {
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
    }
}

// Inf(state)
pub fn is_accepting_state(state: &PLTL) -> bool {
    matches!(state, PLTL::Top)
}

pub type GuaranteeyStateGivenN = Vec<PLTL>;

type State = (PLTL, Vec<Annotated>);

fn dump(
    ctx: &Context,
    u_item_id: u32,
    v_set: BitSet32,
    init_state: &PLTL,
    weakening_conditions_init_state: &[Annotated],
    letter_count: usize,
) -> AutomataDump<State> {
    let mut transitions = Vec::new();

    let mut pending_states: Vec<_> = Vec::new();
    pending_states.push((init_state.clone(), weakening_conditions_init_state.to_vec()));
    let mut seen_states = Set::default();
    while let Some((state, weakening_conditions_state)) = pending_states.pop() {
        if seen_states.contains(&(state.clone(), weakening_conditions_state.clone())) {
            continue;
        }
        seen_states.insert((state.clone(), weakening_conditions_state.clone()));
        let letter_power_set = BitSet32::power_set(letter_count);
        transitions.extend(letter_power_set.map(|letter| {
            let weakening_conditions_next_state =
                weakening_conditions::transition(ctx, &weakening_conditions_state, letter);
            let next_state = transition(
                ctx,
                u_item_id,
                v_set,
                &state,
                &weakening_conditions_next_state,
                letter,
            );
            pending_states.push((next_state.clone(), weakening_conditions_next_state.clone()));
            (
                (state.clone(), weakening_conditions_state.clone()),
                letter,
                (next_state, weakening_conditions_next_state),
            )
        }));
    }

    AutomataDump {
        init_state: (init_state.clone(), weakening_conditions_init_state.to_vec()),
        transitions,
    }
}

pub fn dump_hoa(
    ctx: &Context,
    u_item_id: u32,
    v_set: BitSet32,
    init_state: &PLTL,
    weakening_conditions_init_state: &[Annotated],
) -> HoaAutomaton {
    let letter_count = ctx.atom_map.len();
    let dump = dump(
        ctx,
        u_item_id,
        v_set,
        init_state,
        weakening_conditions_init_state,
        letter_count,
    );
    let mut state_id_map = Map::default();
    let mut states = Vec::new();
    for same_from in dump.transitions.chunks(1 << ctx.atom_map.len()) {
        let from = same_from[0].0.clone();
        let next_id = state_id_map.len() as u32;
        let from_id = *state_id_map.entry(from.clone()).or_insert_with(|| next_id);
        let edges = same_from.iter().map(|(_, letter, to)| {
            let next_id = state_id_map.len() as u32;
            let to_id = *state_id_map.entry(to.clone()).or_insert_with(|| next_id);
            Edge::from_parts(
                Label(AbstractLabelExpression::Conjunction(
                    character_to_label_expression(*letter, ctx.atom_map.len()),
                )),
                StateConjunction::singleton(to_id),
                AcceptanceSignature::empty(),
            )
        });
        states.push(hoa::State::from_parts(
            from_id,
            Some(format!("{}, <{}>", from.0.format_with_atom_names(&ctx.atom_map), from.1.iter().map(|a| a.to_pltl(&ctx.psf_context).format_with_atom_names(&ctx.atom_map)).collect::<Vec<_>>().join(", "))),
            if from.0 == PLTL::Top {
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
            HeaderItem::Name(format!("\"guarantee_{}_{:b}\"", u_item_id, v_set)),
            HeaderItem::Start(StateConjunction::singleton(0)),
            HeaderItem::AcceptanceName(AcceptanceName::Buchi, vec![AcceptanceInfo::Int(1)]),
            HeaderItem::Acceptance(1, AcceptanceCondition::Inf(AcceptanceAtom::Positive(0))),
            HeaderItem::Properties(vec![
                Property::Deterministic,
                Property::Complete,
                Property::StateAcceptance,
            ]),
            HeaderItem::AP(ctx.atom_map.clone()),
        ]),
        states.into(),
    )
}

pub fn initial_state(ctx: &Context, u_item_id: u32, v_set: u32) -> PLTL {
    PLTL::new_unary(
        UnaryOp::Eventually,
        ctx.u_type_subformulas[u_item_id as usize].u_rewrite(&ctx.v_set(v_set)),
    )
    .normal_form()
}

#[cfg(test)]
mod tests {
    // use hoars::output::to_hoa;

    // use crate::pltl::UnaryOp;

    // use super::*;

    // #[test]
    // fn test_dump_hoa() {
    //     let (ltl, atom_map) = PLTL::from_string("G p | F q");
    //     let ltl = ltl.normal_form();
    //     let ctx = Context::new(&ltl, atom_map);
    //     println!("{}", ctx);
    //     let u_item_id = 0;
    //     let v_set = 0;
    //     let init_state = initial_state(&ctx, u_item_id, v_set);
    //     let weakening_conditions_init_state = vec![Annotated::Top];
    //     let hoa = dump_hoa(
    //         &ctx,
    //         u_item_id,
    //         v_set,
    //         &init_state,
    //         &weakening_conditions_init_state,
    //     );
    //     println!("{}", to_hoa(&hoa));
    // }

    use crate::{automata::Context, pltl::PLTL};

    #[test]
    fn test_dump_hoa_2() {
        let (ltl, atom_map) = PLTL::from_string("X p");
        let ltl = ltl.normal_form();
        let ctx = Context::new(&ltl, atom_map);
        println!("{}", ctx);
        // let u_item_id = 0;
        // let v_set = 0;
        // let init_state = initial_state(&ctx, u_item_id, v_set);
        // let weakening_conditions_init_state = vec![Annotated::Top];
        // let hoa = dump_hoa(
        //     &ctx,
        //     u_item_id,
        //     v_set,
        //     &init_state,
        //     &weakening_conditions_init_state,
        // );
        // println!("{}", to_hoa(&hoa));
    }
}
