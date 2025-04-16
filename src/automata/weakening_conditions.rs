use super::{
    hoa::{
        self,
        body::{Edge, Label},
        format::{AcceptanceName, AcceptanceSignature, Property, StateConjunction},
        header::{Header, HeaderItem},
        AbstractLabelExpression, HoaAutomaton,
    },
    AutomataDump, Context,
};
use crate::utils::BitSet;
use crate::{
    pltl::{after_function::local_after_annotated, Annotated, BinaryOp},
    utils::{character_to_label_expression, BitSet32, Map, Set},
};
fn is_saturated(ctx: &Context, i: usize, j: usize) -> bool {
    for psf0 in ctx.c_sets[ctx.init_c].iter() {
        for psf1 in ctx.c_sets[ctx.init_c].iter() {
            if psf0.rewrite(&ctx.psf_context, &ctx.c_sets[i])
                == psf1.rewrite(&ctx.psf_context, &ctx.c_sets[j])
                && psf0.rewrite(&ctx.psf_context, &ctx.c_sets[i])
                    != psf1.rewrite(&ctx.psf_context, &ctx.c_sets[j])
            {
                return false;
            }
        }
    }
    true
}

pub fn transition(ctx: &Context, current: &[Annotated], letter: BitSet32) -> Vec<Annotated> {
    let k = ctx.c_sets.len();
    let mut result = Vec::with_capacity(current.len());
    if current
        == &[
            Annotated::Top,
            Annotated::Bottom,
            Annotated::Bottom,
            Annotated::Bottom,
        ]
    {
        println!("current: {:?}, letter: 0b{:b}", current, letter);
    }
    for (i, _) in current.iter().enumerate() {
        let mut current_result_i = None;
        for j in 0..k {
            if is_saturated(ctx, i, j) {
                let part_1 = local_after_annotated(
                    &ctx.psf_context,
                    &current[j],
                    letter,
                    &ctx.c_rewrite_c_sets[i][j],
                );
                let result = ctx.c_sets[i]
                    .iter()
                    .map(|ci_item| {
                        let ci_item_cj = ci_item
                        .rewrite(&ctx.psf_context, &ctx.c_sets[j]);
                        let wc = ci_item_cj
                            .weaken_condition(&ctx.psf_context);
                        let past_st_set = &ctx.c_rewrite_c_sets[i][j];
                        if current
                            == &[
                                Annotated::Top,
                                Annotated::Bottom,
                                Annotated::Bottom,
                                Annotated::Bottom,
                            ]
                            && j == 0
                        {
                            println!(
                                "ξ: ({}, 0b{:b}), cj: (0b{:b}, 0b{:b}), ξ<cj>: ({}, 0b{:b}), wc: {}, past_st_set: (0b{:b}, 0b{:b})",
                                ci_item.id, ci_item.state, &ctx.c_sets[j].existence, &ctx.c_sets[j].state, ci_item_cj.id, ci_item_cj.state, wc, past_st_set.existence, past_st_set.state
                            );
                        }
                        local_after_annotated(&ctx.psf_context, &wc, letter, past_st_set)
                    })
                    .fold(part_1, |acc, part| {
                        Annotated::new_binary(BinaryOp::And, acc, part)
                    });

                if current
                    == &[
                        Annotated::Top,
                        Annotated::Bottom,
                        Annotated::Bottom,
                        Annotated::Bottom,
                    ]
                    && j == 0
                {
                    println!("{i} {j}: {}", result);
                }
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
    if current
        == &[
            Annotated::Top,
            Annotated::Bottom,
            Annotated::Bottom,
            Annotated::Bottom,
        ]
    {
        println!("===");
    }
    result
}

type State = Vec<Annotated>;

fn dump(ctx: &Context, init_state: &Vec<Annotated>, letter_count: usize) -> AutomataDump<State> {
    let mut transitions = Vec::new();

    let mut pending_states: Vec<_> = Vec::new();
    pending_states.push(init_state.clone());
    let mut seen_states = Set::default();
    while let Some(state) = pending_states.pop() {
        if seen_states.contains(&state) {
            continue;
        }
        seen_states.insert(state.clone());
        let letter_power_set = BitSet32::power_set(letter_count);
        transitions.extend(letter_power_set.map(|letter| {
            let next_state = transition(ctx, &state, letter);
            pending_states.push(next_state.clone());
            (state.clone(), letter, next_state)
        }));
    }

    AutomataDump {
        init_state: init_state.clone(),
        transitions,
    }
}

pub fn dump_hoa(ctx: &Context, init_state: &Vec<Annotated>) -> HoaAutomaton {
    let letter_count = ctx.atom_map.len();
    let dump = dump(ctx, init_state, letter_count);
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
            Some(format!(
                "{}",
                from.iter()
                    .map(|a| a
                        .to_pltl(&ctx.psf_context)
                        .format_with_atom_names(&ctx.atom_map))
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
            AcceptanceSignature::empty(),
            edges.collect(),
        ));
    }
    HoaAutomaton::from_parts(
        Header::from_vec(vec![
            HeaderItem::v1(),
            HeaderItem::Name("\"wc\"".to_string()),
            HeaderItem::Start(StateConjunction::singleton(0)),
            HeaderItem::AcceptanceName(AcceptanceName::None, Vec::new()),
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

#[cfg(test)]
mod tests {
    use crate::{automata::hoa::output::to_hoa, pltl::PLTL};

    use super::*;

    #[test]
    fn test_dump_hoa() {
        let (ltl, atom_map) = PLTL::from_string("Y (a ~S b)");
        let ltl = ltl.normal_form();
        let ctx = Context::new(&ltl, atom_map);
        println!("{}", ctx);
        let init_state = vec![
            Annotated::Bottom,
            Annotated::Top,
            Annotated::Bottom,
            Annotated::Bottom,
        ];
        let hoa = dump_hoa(&ctx, &init_state);
        println!("{}", to_hoa(&hoa));
    }
}
