mod guarantee;
mod safety;
mod stable;
mod weakening_conditions;

use crate::utils::Map;
use crate::{
    pltl::{Annotated, PastSubformulaSet, PastSubformularSetContext, UnaryOp, PLTL},
    utils::{BitSet, BitSet32},
};
use guarantee::GuaranteeyStateGivenN;
use hoars::output::to_hoa;
use hoars::{
    AbstractLabelExpression, AcceptanceCondition, AcceptanceInfo, AcceptanceName,
    AcceptanceSignature, Edge, Header, HeaderItem, HoaAutomaton, Property, StateConjunction,
};
use itertools::Itertools;
use safety::SafetyStateGivenM;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

type AutomataRecord<S> = (S, BitSet32, S);

struct AutomataDump<S> {
    init_state: S,
    transitions: Vec<AutomataRecord<S>>,
}

#[derive(Debug, Clone)]
pub struct Context<'a> {
    pub atom_map: Vec<String>,
    after_function_cache: HashMap<&'a PLTL, Vec<(&'a HashSet<String>, PLTL)>>,
    psf_context: PastSubformularSetContext<'a>,
    c_sets: Vec<PastSubformulaSet>,
    c_rewrite_c_sets: Vec<Vec<PastSubformulaSet>>,
    init_c: usize,
    u_type_subformulas: Vec<&'a PLTL>,
    v_type_subformulas: Vec<&'a PLTL>,
}

impl fmt::Display for Context<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.psf_context)?;
        for (i, c) in self.c_sets.iter().enumerate() {
            writeln!(
                f,
                "c{}: {{{}}}",
                i,
                c.iter()
                    .map(|psf| psf.to_pltl(&self.psf_context))
                    .map(|pltl| format!("{pltl}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        for (i, c) in self.c_rewrite_c_sets.iter().enumerate() {
            for (j, s) in c.iter().enumerate() {
                writeln!(
                    f,
                    "c{}<c{}>: {{{}}}",
                    i,
                    j,
                    s.iter()
                        .map(|psf| psf.to_pltl(&self.psf_context))
                        .map(|pltl| format!("{pltl}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
            }
        }
        write!(f, "u: ")?;
        for u_subformula in &self.u_type_subformulas {
            write!(f, "{}; ", u_subformula)?;
        }
        write!(f, "\nv: ")?;
        for v_subformula in &self.v_type_subformulas {
            write!(f, "{}; ", v_subformula)?;
        }
        Ok(())
    }
}

impl<'a> Context<'a> {
    pub fn new(ltl: &'a PLTL, atom_map: Vec<String>) -> Self {
        let psf_context = PastSubformularSetContext::new(ltl);
        let mut c_sets = Vec::with_capacity(1 << psf_context.past_subformulas.len());
        let mut c = PastSubformulaSet {
            existence: 0,
            state: psf_context.initial_state,
        };
        c_sets.push(c.clone());
        while let Some(next) = c.next(&psf_context) {
            c = next;
            c_sets.push(c.clone());
        }
        let mut c_rewrite_c_sets = Vec::with_capacity(c_sets.len());
        for ci in &c_sets {
            let mut rewrite_c_sets = Vec::with_capacity(c_sets.len());
            for cj in &c_sets {
                let mut set = PastSubformulaSet {
                    existence: 0,
                    state: 0,
                };
                for psf in ci.iter() {
                    let rewrite_result = psf.rewrite(&psf_context, cj);
                    set.existence.set_bit(rewrite_result.id);
                    set.state |= rewrite_result.state;
                }
                set = set.to_proper_set(&psf_context);
                rewrite_c_sets.push(set);
            }
            c_rewrite_c_sets.push(rewrite_c_sets);
        }
        let init_c = Self::calculate_init_c(&psf_context, &c_sets);
        let u_type_subformulas = psf_context
            .origin
            .u_type_subformulas()
            .into_iter()
            .dedup()
            .collect();
        let v_type_subformulas = psf_context
            .origin
            .v_type_subformulas()
            .into_iter()
            .dedup()
            .collect();
        Self {
            atom_map,
            after_function_cache: HashMap::new(),
            psf_context,
            c_sets,
            c_rewrite_c_sets,
            init_c,
            u_type_subformulas,
            v_type_subformulas,
        }
    }

    pub fn calculate_init_c(
        psf_context: &PastSubformularSetContext,
        c_sets: &[PastSubformulaSet],
    ) -> usize {
        let init_c = PastSubformulaSet {
            existence: psf_context.initial_state,
            state: psf_context.initial_state,
        }
        .to_proper_set(psf_context);
        for (i, c) in c_sets.iter().enumerate() {
            if c == &init_c {
                return i;
            }
        }
        unreachable!()
    }

    pub fn u_set(&self, set: BitSet32) -> HashSet<PLTL> {
        let mut result = HashSet::new();
        for i in set.iter() {
            result.insert(self.u_type_subformulas[i as usize].clone());
        }
        result
    }

    pub fn v_set(&self, set: BitSet32) -> HashSet<PLTL> {
        let mut result = HashSet::new();
        for i in set.iter() {
            result.insert(self.v_type_subformulas[i as usize].clone());
        }
        result
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EventuallyGloballyStateGivenMN {
    // u-id -> Eventually Automata State
    guarantee_state: GuaranteeyStateGivenN,
    // v-id -> Globally Automata State
    safety_state: SafetyStateGivenM,

    stable_state: (PLTL, PLTL),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State {
    weakening_condition: Vec<Annotated>,
    // M-id -> N-id -> State
    states: Vec<Vec<EventuallyGloballyStateGivenMN>>,
}

pub struct DumpedAutomata {
    init_state: State,
    atom_map: Vec<String>,
    transitions: HashMap<State, Vec<(BitSet32, State)>>,
    state_id_map: HashMap<State, usize>,
}

impl DumpedAutomata {
    pub fn new(
        init_state: State,
        atom_map: Vec<String>,
        transitions: HashMap<State, Vec<(BitSet32, State)>>,
    ) -> Self {
        let mut state_id_map = HashMap::new();
        transitions.keys().enumerate().for_each(|(i, state)| {
            state_id_map.insert(state.clone(), i);
        });
        Self {
            init_state,
            atom_map,
            transitions,
            state_id_map,
        }
    }

    pub fn stable_at_m_n(&self, m_id: BitSet32, n_id: BitSet32) -> Vec<(PLTL, PLTL)> {
        let mut result: Vec<_> = (0..self.state_id_map.len())
            .map(|_| (PLTL::Bottom, PLTL::Bottom))
            .collect();
        for (state, i) in &self.state_id_map {
            result[*i] = state.states[m_id as usize][n_id as usize]
                .stable_state
                .clone();
        }
        result
    }

    pub fn guarantee_at_m_n(&self, m_id: BitSet32, n_id: BitSet32) -> Vec<Vec<PLTL>> {
        let mut result: Vec<_> = (0..self.state_id_map.len()).map(|_| Vec::new()).collect();
        for (state, i) in &self.state_id_map {
            result[*i] = state.states[m_id as usize][n_id as usize]
                .guarantee_state
                .clone();
        }
        result
    }

    pub fn safety_at_m_n(&self, m_id: BitSet32, n_id: BitSet32) -> Vec<Vec<PLTL>> {
        let mut result: Vec<_> = (0..self.state_id_map.len()).map(|_| Vec::new()).collect();
        for (state, i) in &self.state_id_map {
            result[*i] = state.states[m_id as usize][n_id as usize]
                .safety_state
                .clone();
        }
        result
    }

    pub fn dump_hoa(&self, name: &str) -> HoaAutomaton {
        let max_m = self.state_id_map.iter().next().unwrap().0.states.len();
        let max_n = self.state_id_map.iter().next().unwrap().0.states[0].len();
        let mut rabin_pairs = Vec::new();
        for m in 0..max_m {
            for n in 0..max_n {
                let mut inf_visit = HashSet::new();
                for (s_id, g) in self
                    .guarantee_at_m_n(m as u32, n as u32)
                    .into_iter()
                    .enumerate()
                {
                    if !g.is_empty() && g.iter().all(|it| it == &PLTL::Top) {
                        inf_visit.insert(s_id);
                    }
                }
                let mut safety_visit = HashSet::new();
                for (s_id, g) in self
                    .safety_at_m_n(m as u32, n as u32)
                    .into_iter()
                    .enumerate()
                {
                    if !g.is_empty() && g.iter().all(|it| it == &PLTL::Bottom) {
                        safety_visit.insert(s_id);
                    }
                }
                let mut stable_visit = HashSet::new();
                for (s_id, (_, snd)) in self
                    .stable_at_m_n(m as u32, n as u32)
                    .into_iter()
                    .enumerate()
                {
                    if snd == PLTL::Bottom {
                        stable_visit.insert(s_id);
                    }
                }
                let fin_visit: HashSet<usize> =
                    safety_visit.union(&stable_visit).cloned().collect();
                rabin_pairs.push((fin_visit, inf_visit));
            }
        }
        let init_state_id = self.state_id_map[&self.init_state];
        let acceptance_condition = (0..rabin_pairs.len())
            .map(|i| {
                AcceptanceCondition::and(
                    &AcceptanceCondition::id_fin(i as u32 * 2),
                    AcceptanceCondition::id_inf(i as u32 * 2 + 1),
                )
            })
            .reduce(|acc, elem| acc.or(elem))
            .unwrap();

        let result = HoaAutomaton::from_parts(
            Header::from_vec(vec![
                HeaderItem::v1(),
                HeaderItem::Name(name.to_string()),
                HeaderItem::Start(StateConjunction::singleton(init_state_id as _)),
                HeaderItem::AcceptanceName(
                    AcceptanceName::Rabin,
                    vec![AcceptanceInfo::Int(rabin_pairs.len() as _)],
                ),
                HeaderItem::Acceptance(rabin_pairs.len() as u32 * 2, acceptance_condition),
                HeaderItem::Properties(vec![
                    Property::Deterministic,
                    Property::Complete,
                    Property::StateAcceptance,
                ]),
                HeaderItem::AP(self.atom_map.clone()),
            ]),
            self.state_id_map
                .iter()
                .map(|(state, state_id)| {
                    let edges = self.transitions[state]
                        .iter()
                        .map(|(letter, next_state)| {
                            let label_characters = letter
                                .bits(self.atom_map.len() as u32)
                                .enumerate()
                                .map(|(i, it)| {
                                    if it {
                                        AbstractLabelExpression::Integer(i as _)
                                    } else {
                                        AbstractLabelExpression::Negated(Box::new(
                                            AbstractLabelExpression::Integer(i as _),
                                        ))
                                    }
                                })
                                .collect::<Vec<_>>();
                            Edge::from_parts(
                                hoars::Label(hoars::AbstractLabelExpression::Conjunction(
                                    label_characters,
                                )),
                                StateConjunction::singleton(self.state_id_map[next_state] as _),
                                AcceptanceSignature::empty(),
                            )
                        })
                        .collect_vec();
                    let state_label = rabin_pairs
                        .iter()
                        .enumerate()
                        .map(|(i, (fin, inf))| {
                            let mut result = "".to_string();
                            if fin.contains(state_id) {
                                result += &(i * 2).to_string();
                            };
                            result += " ";
                            if inf.contains(state_id) {
                                result += &(i * 2 + 1).to_string();
                            };
                            result
                        })
                        .filter(|it| !it.is_empty())
                        .collect::<Vec<_>>()
                        .join(" ");
                    hoars::State::from_parts(
                        *state_id as _,
                        if state_label.is_empty() {
                            None
                        } else {
                            Some(state_label)
                        },
                        edges,
                    )
                })
                .collect::<Vec<hoars::State>>()
                .into(),
        );
        result
    }
}

impl fmt::Display for DumpedAutomata {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (state, transitions) in &self.transitions {
            for (letter, next_state) in transitions {
                write!(f, "{} ", self.state_id_map[state])?;
                writeln!(
                    f,
                    "{{{}}} {}",
                    letter
                        .iter()
                        .map(|id| self.atom_map[id as usize].clone())
                        .collect::<Vec<_>>()
                        .join(","),
                    self.state_id_map[next_state]
                )?;
            }
        }
        Ok(())
    }
}

impl fmt::Debug for DumpedAutomata {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let max_m = self.state_id_map.iter().next().unwrap().0.states.len();
        let max_n = self.state_id_map.iter().next().unwrap().0.states[0].len();
        for m in 0..max_m {
            for n in 0..max_n {
                writeln!(f, "M={m}, N={n}\n  guarantee:")?;
                for (s_id, g) in self
                    .guarantee_at_m_n(m as u32, n as u32)
                    .into_iter()
                    .enumerate()
                {
                    writeln!(
                        f,
                        "    {s_id}: {}",
                        g.iter().map(|it| format!("{it}")).join(", ")
                    )?;
                }
                writeln!(f, "  safety:")?;
                for (s_id, g) in self
                    .safety_at_m_n(m as u32, n as u32)
                    .into_iter()
                    .enumerate()
                {
                    writeln!(
                        f,
                        "    {s_id}: {}",
                        g.iter().map(|it| format!("{it}")).join(", ")
                    )?;
                }
                writeln!(f, "  stable:")?;
                for (s_id, (fst, snd)) in self
                    .stable_at_m_n(m as u32, n as u32)
                    .into_iter()
                    .enumerate()
                {
                    writeln!(f, "    {s_id}: {fst}, {snd}")?;
                }
            }
        }
        Ok(())
    }
}

impl State {
    pub fn new(ctx: &Context) -> Self {
        let mut result =
            Vec::with_capacity(ctx.u_type_subformulas.len() * ctx.v_type_subformulas.len());
        for m_id in 0u32..(1 << ctx.u_type_subformulas.len()) {
            let mut n_result = Vec::with_capacity(ctx.c_sets.len());
            for n_id in 0u32..(1 << ctx.v_type_subformulas.len()) {
                let mut eventually_state = Vec::with_capacity(m_id.count_ones() as usize);
                let mut globally_state = Vec::with_capacity(n_id.count_ones() as usize);
                for u in m_id.iter() {
                    eventually_state.push(
                        PLTL::new_unary(
                            UnaryOp::Eventually,
                            ctx.u_type_subformulas[u as usize].u_rewrite(&ctx.v_set(n_id)),
                        )
                        .normal_form(),
                    );
                }
                for v in n_id.iter() {
                    globally_state.push(
                        PLTL::new_unary(
                            UnaryOp::Globally,
                            ctx.v_type_subformulas[v as usize].v_rewrite(&ctx.u_set(m_id)),
                        )
                        .normal_form(),
                    );
                }
                n_result.push(EventuallyGloballyStateGivenMN {
                    guarantee_state: eventually_state,
                    safety_state: globally_state,
                    stable_state: (
                        ctx.psf_context.origin.normal_form(),
                        ctx.psf_context
                            .origin
                            .v_rewrite(&ctx.u_set(m_id))
                            .normal_form(),
                    ),
                });
            }
            result.push(n_result);
        }
        let mut weakening_condition: Vec<_> =
            (0..ctx.c_sets.len()).map(|_| Annotated::Bottom).collect();
        weakening_condition[ctx.init_c] = Annotated::Top;
        Self {
            weakening_condition,
            states: result,
        }
    }

    pub fn transition(&self, ctx: &Context, letter: BitSet32) -> State {
        let next_weakening_condition =
            weakening_conditions::transition(ctx, &self.weakening_condition, letter);
        let mut new_states =
            Vec::with_capacity(ctx.u_type_subformulas.len() * ctx.v_type_subformulas.len());
        for m_id in 0u32..(1 << ctx.u_type_subformulas.len()) {
            let mut new_n_result = Vec::with_capacity(ctx.c_sets.len());
            for n_id in 0u32..(1 << ctx.v_type_subformulas.len()) {
                let mut new_eventually_states = Vec::with_capacity(ctx.c_sets.len());
                let mut new_globally_states = Vec::with_capacity(ctx.c_sets.len());
                for (u_id, u) in m_id.iter().enumerate() {
                    let current = &self.states[m_id as usize][n_id as usize].guarantee_state[u_id];
                    let new_eventually_state = guarantee::transition(
                        ctx,
                        u,
                        n_id,
                        current,
                        &next_weakening_condition,
                        letter,
                    );
                    new_eventually_states.push(new_eventually_state);
                }
                for (v_id, v) in n_id.iter().enumerate() {
                    let current = &self.states[m_id as usize][n_id as usize].safety_state[v_id];
                    let new_globally_state = safety::transition(
                        ctx,
                        v,
                        m_id,
                        current,
                        &next_weakening_condition,
                        letter,
                    );
                    new_globally_states.push(new_globally_state);
                }
                let old_stable_state = &self.states[m_id as usize][n_id as usize].stable_state;
                let stable_state = stable::transition(
                    ctx,
                    m_id,
                    old_stable_state,
                    &next_weakening_condition,
                    letter,
                );
                // println!("{m_id} {n_id}: {}", stable_state.1);
                new_n_result.push(EventuallyGloballyStateGivenMN {
                    guarantee_state: new_eventually_states,
                    safety_state: new_globally_states,
                    stable_state,
                });
            }
            new_states.push(new_n_result);
        }
        State {
            weakening_condition: next_weakening_condition,
            states: new_states,
        }
    }

    pub fn dump_automata(&self, ctx: &Context, letters_count: usize) -> DumpedAutomata {
        let mut result = HashMap::new();
        let mut pending_states: Vec<_> = Vec::new();
        pending_states.push(self.clone());
        while let Some(current_state) = pending_states.pop() {
            if result.contains_key(&current_state) {
                continue;
            }
            let letter_power_set = BitSet32::power_set(letters_count);
            let transition = letter_power_set
                .map(|letter| {
                    let next_state = current_state.transition(ctx, letter);
                    pending_states.push(next_state.clone());
                    (letter, next_state)
                })
                .collect();
            result.insert(current_state.clone(), transition);
        }
        DumpedAutomata::new(self.clone(), ctx.atom_map.clone(), result)
    }
}

#[derive(Debug, Clone)]
pub struct AllSubAutomatas {
    // u_item_id, v_set -> automata
    guarantee_automatas: Map<(u32, BitSet32), HoaAutomaton>,
    // v_item_id, u_set -> automata
    safety_automatas: Map<(u32, BitSet32), HoaAutomaton>,
    // u_set -> automata
    stable_automatas: Vec<HoaAutomaton>,
}

impl AllSubAutomatas {
    pub fn new(ctx: &Context) -> Self {
        let mut weakening_condition_init_state: Vec<_> =
            (0..ctx.c_sets.len()).map(|_| Annotated::Bottom).collect();
        weakening_condition_init_state[ctx.init_c] = Annotated::Top;
        let mut guarantee_automatas = Map::default();
        let mut safety_automatas = Map::default();
        let mut stable_automatas = Vec::new();
        for m_id in 0u32..(1 << ctx.u_type_subformulas.len()) {
            for n_id in 0u32..(1 << ctx.v_type_subformulas.len()) {
                for u_item in m_id.iter() {
                    let guarantee_init_state = guarantee::initial_state(&ctx, u_item, n_id);
                    let guarantee_automata = guarantee::dump_hoa(
                        ctx,
                        u_item,
                        n_id,
                        &guarantee_init_state,
                        &weakening_condition_init_state,
                    );
                    guarantee_automatas.insert((u_item, n_id), guarantee_automata);
                }
                for v_item in n_id.iter() {
                    let safety_init_state = safety::initial_state(&ctx, v_item, m_id);
                    let safety_automata = safety::dump_hoa(
                        ctx,
                        v_item,
                        m_id,
                        &safety_init_state,
                        &weakening_condition_init_state,
                    );
                    safety_automatas.insert((v_item, m_id), safety_automata);
                }
            }
            let stable_init_state = stable::initial_state(&ctx, m_id);
            stable_automatas.push(stable::dump_hoa(
                ctx,
                m_id,
                &stable_init_state,
                &weakening_condition_init_state,
            ));
        }
        Self {
            guarantee_automatas,
            safety_automatas,
            stable_automatas,
        }
    }

    pub fn to_files(&self, ctx: &Context, path: &str) {
        for ((u_item_id, v_set), automata) in &self.guarantee_automatas {
            let file_name = format!("guarantee_{u_item_id}_0b{:b}.hoa", v_set);
            let file_path = Path::new(path).join(&file_name);
            let mut file = File::create(file_path).unwrap();
            write!(file, "{}", to_hoa(&automata)).unwrap();
        }
        for ((v_item_id, u_set), automata) in &self.safety_automatas {
            let file_name = format!("safety_0b{:b}_{v_item_id}.hoa", u_set);
            let file_path = Path::new(path).join(&file_name);
            let mut file = File::create(file_path).unwrap();
            write!(file, "{}", to_hoa(&automata)).unwrap();
        }
        for (u_set, automata) in self.stable_automatas.iter().enumerate() {
            let file_name = format!("stable_0b{:b}.hoa", u_set);
            let file_path = Path::new(path).join(&file_name);
            let mut file = File::create(file_path).unwrap();
            write!(file, "{}", to_hoa(&automata)).unwrap();
        }
        let mut makefile_content = String::new();
        for m_id in 0u32..(1 << ctx.u_type_subformulas.len()) {
            for n_id in 0u32..(1 << ctx.v_type_subformulas.len()) {
                if m_id != 0 {
                    let file_name = format!("b2_0b{:b}_0b{:b}.hoa", m_id, n_id);
                    makefile_content += &format!("{}: ", file_name);
                    makefile_content += &m_id
                        .iter()
                        .map(|u_item_id| format!("guarantee_{u_item_id}_0b{:b}.hoa ", n_id))
                        .join(" ");
                    makefile_content += &format!("\n\tautfilt --Buchi -o {} ", file_name);
                    makefile_content += &m_id
                        .iter()
                        .enumerate()
                        .map(|(id, u_item_id)| {
                            if id == 0 {
                                format!("-F guarantee_{u_item_id}_0b{:b}.hoa ", n_id)
                            } else {
                                format!("--product=guarantee_{u_item_id}_0b{:b}.hoa ", n_id)
                            }
                        })
                        .join(" ");
                    makefile_content += "\n";
                }
                if n_id != 0 {
                    let file_name = format!("c3_0b{:b}_0b{:b}.hoa", m_id, n_id);
                    makefile_content += &format!("{}: ", file_name);
                    makefile_content += &n_id
                        .iter()
                        .map(|v_item_id| format!("safety_0b{:b}_{v_item_id}.hoa ", m_id))
                        .join(" ");
                    makefile_content += &format!("\n\tautfilt --coBuchi -o {} ", file_name);
                    makefile_content += &n_id
                        .iter()
                        .enumerate()
                        .map(|(i, v_item_id)| {
                            if i == 0 {
                                format!("-F safety_0b{:b}_{v_item_id}.hoa ", m_id)
                            } else {
                                format!("--product=safety_0b{:b}_{v_item_id}.hoa ", m_id)
                            }
                        })
                        .join(" ");
                    makefile_content += "\n";
                }

                let file_name = format!("rabin_0b{:b}_0b{:b}.hoa", m_id, n_id);
                makefile_content += &format!("{}: ", file_name);
                makefile_content += &format!("stable_0b{:b}.hoa ", m_id);
                if m_id != 0 {
                    makefile_content += &format!("b2_0b{:b}_0b{:b}.hoa ", m_id, n_id);
                }
                if n_id != 0 {
                    makefile_content += &format!("c3_0b{:b}_0b{:b}.hoa ", m_id, n_id);
                }
                makefile_content += &format!("\n\tautfilt --gra -o {} ", file_name);
                makefile_content += &format!("-F stable_0b{:b}.hoa ", m_id);
                if m_id != 0 {
                    makefile_content += &format!("--product=b2_0b{:b}_0b{:b}.hoa ", m_id, n_id);
                }
                if n_id != 0 {
                    makefile_content += &format!("--product=c3_0b{:b}_0b{:b}.hoa", m_id, n_id);
                }
                makefile_content += "\n";
            }
        }
        let file_name = format!("result.hoa");
        makefile_content += &format!("{}: ", file_name);
        for m_id in 0u32..(1 << ctx.u_type_subformulas.len()) {
            for n_id in 0u32..(1 << ctx.v_type_subformulas.len()) {
                makefile_content += &format!("rabin_0b{:b}_0b{:b}.hoa ", m_id, n_id);
            }
        }
        makefile_content += &format!("\n\tautfilt --gra --generic --complete -D -o {} ", file_name);
        for m_id in 0u32..(1 << ctx.u_type_subformulas.len()) {
            for n_id in 0u32..(1 << ctx.v_type_subformulas.len()) {
                if m_id == 0 && n_id == 0 {
                    makefile_content += &format!("-F rabin_0b{:b}_0b{:b}.hoa ", m_id, n_id);
                } else {
                    makefile_content += &format!("--product-or=rabin_0b{:b}_0b{:b}.hoa ", m_id, n_id);
                }
            }
        }
        makefile_content += "\n";
        let makefile_path = Path::new(path).join("Makefile");
        let mut file = File::create(makefile_path).unwrap();
        write!(file, "{}", makefile_content).unwrap();
    }
}
