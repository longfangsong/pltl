use crate::{
    pltl::{
        self,
        labeled::{self, LabeledPLTL},
        PLTL,
    },
    utils::{character_to_label_expression, powerset, BitSet, Map, Set},
};
use hoa::{
    body::{Edge, Label},
    format::{
        AcceptanceAtom, AcceptanceCondition, AcceptanceInfo, AcceptanceName, AcceptanceSignature,
        HoaBool, Property, StateConjunction,
    },
    header::{Header, HeaderItem},
    output::{to_dot, to_hoa},
    AbstractLabelExpression, HoaAutomaton,
};
use itertools::Itertools;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};
use std::{fmt, hash::Hash};

mod guarantee;
pub mod hoa;
mod safety;
mod stable;
mod weakening_conditions;

#[derive(Debug, Clone)]
pub struct Context {
    pub initial: LabeledPLTL,
    // pub pltl_context: pltl::Context,
    pub label_context: labeled::Context,
    // ci => cj
    pub saturated_c_sets: Vec<Vec<u32>>,
    pub u_items: Vec<LabeledPLTL>,
    pub v_items: Vec<LabeledPLTL>,
    pub n_sets: Vec<Set<LabeledPLTL>>,
    pub m_sets: Vec<Set<LabeledPLTL>>,
}

impl Context {
    fn compute_saturated_c_set(label_context: &labeled::Context) -> Vec<Vec<u32>> {
        (0..(1 << label_context.past_subformulas.len()))
            .into_par_iter()
            .map(|ci| {
                let mut result = Vec::new();
                'check_cj: for cj in 0..(1 << label_context.past_subformulas.len()) {
                    'check_psf: for (psf0_id, psf0) in
                        label_context.past_subformulas.iter().enumerate()
                    {
                        for psf1 in &label_context.past_subformulas[psf0_id + 1..] {
                            let psf0_rewrite_cj = psf0.clone();
                            let psf0_rewrite_cj = psf0_rewrite_cj.c_rewrite(cj);
                            let psf0_rewrite_cj = psf0_rewrite_cj.simplify();
                            let psf1_rewrite_cj = psf1.clone();
                            let psf1_rewrite_cj = psf1_rewrite_cj.c_rewrite(cj);
                            let psf1_rewrite_cj = psf1_rewrite_cj.simplify();
                            if psf0_rewrite_cj == psf1_rewrite_cj {
                                continue 'check_psf;
                            }

                            let psf0_rewrite_ci = psf0.clone();
                            let psf0_rewrite_ci = psf0_rewrite_ci.c_rewrite(ci);
                            let psf0_rewrite_ci = psf0_rewrite_ci.simplify();
                            let psf1_rewrite_ci = psf1.clone();
                            let psf1_rewrite_ci = psf1_rewrite_ci.c_rewrite(ci);
                            let psf1_rewrite_ci = psf1_rewrite_ci.simplify();
                            if psf0_rewrite_ci == psf1_rewrite_ci {
                                continue 'check_cj;
                            }
                        }
                    }
                    result.push(cj);
                }
                result
            })
            .collect()
    }

    pub fn new(ltl: &PLTL) -> Self {
        let (labeled_pltl, psf_context) = LabeledPLTL::new(ltl);
        let saturated_c_sets = Self::compute_saturated_c_set(&psf_context);
        // let mut m_n_sets = (Vec::new(), Vec::new());
        // collect_u_v_items(&psf_context, ltl, &mut m_n_sets);
        let (u_items, v_items) = labeled_pltl.u_v_subformulas();
        let mut u_items: Vec<_> = u_items.into_iter().collect();
        u_items.sort();
        let mut v_items: Vec<_> = v_items.into_iter().collect();
        v_items.sort();
        let m_sets = powerset(u_items.iter().cloned());
        let n_sets = powerset(v_items.iter().cloned());
        Self {
            initial: labeled_pltl,
            label_context: psf_context,
            saturated_c_sets,
            u_items,
            v_items,
            n_sets,
            m_sets,
        }
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.label_context)?;
        for (i, s) in self.saturated_c_sets.iter().enumerate() {
            writeln!(
                f,
                "J{}: {{{}}}",
                i,
                s.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        for (i, u) in self.u_items.iter().enumerate() {
            writeln!(f, "u{}: {}", i, u)?;
        }
        for (i, v) in self.v_items.iter().enumerate() {
            writeln!(f, "v{}: {}", i, v)?;
        }
        for (i, n) in self.n_sets.iter().enumerate() {
            writeln!(
                f,
                "N{}: {{{}}}",
                i,
                n.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        for (i, m) in self.m_sets.iter().enumerate() {
            writeln!(
                f,
                "M{}: {{{}}}",
                i,
                m.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct HoaAutomatonBuilder<S, SF: Fn(&S, &pltl::Context) -> String> {
    init_state: S,
    name: String,
    is_accepting: fn(&S) -> bool,
    state_formatter: Option<SF>,
    accepting_name: AcceptanceName,
    accepting_infos: Vec<AcceptanceInfo>,
    state_id_map: Map<S, usize>,
    transitions: Map<S, Vec<S>>,
}

impl<S: Hash + Eq, F: Fn(&S, &pltl::Context) -> String + Clone> HoaAutomatonBuilder<S, F> {
    pub fn new(
        name: String,
        accepting_name: AcceptanceName,
        init_state: S,
        is_accepting: fn(&S) -> bool,
        state_formatter: Option<F>,
    ) -> Self {
        Self {
            init_state,
            name,
            is_accepting,
            state_formatter,
            accepting_infos: match accepting_name {
                AcceptanceName::Buchi => vec![AcceptanceInfo::Int(1)],
                AcceptanceName::CoBuchi => vec![AcceptanceInfo::Int(1)],
                AcceptanceName::None => Vec::new(),
                _ => unreachable!(),
            },
            accepting_name,
            state_id_map: Map::default(),
            transitions: Map::default(),
        }
    }

    pub fn build(self, ctx: &pltl::Context) -> HoaAutomaton {
        let mut states = Vec::with_capacity(self.state_id_map.len());
        for (from, targets) in &self.transitions {
            let from_id = self.state_id_map[from];
            let edges = targets.iter().enumerate().map(|(letter, to)| {
                let to_id = self.state_id_map[to];
                Edge::from_parts(
                    Label(AbstractLabelExpression::Conjunction(
                        character_to_label_expression(letter as _, ctx.atoms.len()),
                    )),
                    StateConjunction::singleton(to_id as _),
                    AcceptanceSignature::empty(),
                )
            });
            states.push(hoa::State::from_parts(
                from_id as _,
                self.state_formatter.clone().map(|f| f(from, ctx)),
                if (self.is_accepting)(from) {
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
                HeaderItem::Name(self.name),
                HeaderItem::Start(StateConjunction::singleton(
                    self.state_id_map[&self.init_state] as _,
                )),
                HeaderItem::Acceptance(
                    1,
                    match &self.accepting_name {
                        AcceptanceName::Buchi => {
                            AcceptanceCondition::Inf(AcceptanceAtom::Positive(0))
                        }
                        AcceptanceName::CoBuchi => {
                            AcceptanceCondition::Fin(AcceptanceAtom::Positive(0))
                        }
                        AcceptanceName::None => AcceptanceCondition::Boolean(HoaBool(false)),
                        _ => unreachable!(),
                    },
                ),
                HeaderItem::AcceptanceName(self.accepting_name, self.accepting_infos),
                HeaderItem::Properties(vec![
                    Property::Deterministic,
                    Property::Complete,
                    Property::StateAcceptance,
                ]),
                HeaderItem::AP(ctx.atoms.clone()),
            ]),
            states.into(),
        )
    }
}

#[derive(Debug, Clone)]
pub struct AllSubAutomatas {
    // u_item_id -> n_set -> automata
    pub guarantee_automatas: Vec<Vec<HoaAutomaton>>,
    // v_item_id -> m_set -> automata
    pub safety_automatas: Vec<Vec<HoaAutomaton>>,
    // m_set -> automata
    pub stable_automatas: Vec<HoaAutomaton>,
}

impl AllSubAutomatas {
    pub fn new(ctx: &Context, pltl_ctx: &pltl::Context) -> Self {
        let weakening_conditions_automata = weakening_conditions::dump(ctx, pltl_ctx);
        let (guarantee_automatas, (safety_automatas, stable_automatas)) = rayon::join(
            || {
                ctx.u_items
                    .par_iter()
                    .enumerate()
                    .map(|(u_item, _)| {
                        let mut guarantee_automatas_for_u_item: Vec<_> =
                            Vec::with_capacity(ctx.n_sets.len());
                        for (n_set, _) in ctx.n_sets.iter().enumerate() {
                            let guarantee_automata = guarantee::dump(
                                ctx,
                                pltl_ctx,
                                u_item as u32,
                                n_set as u32,
                                &weakening_conditions_automata,
                            );
                            guarantee_automatas_for_u_item.push(guarantee_automata.build(pltl_ctx));
                        }
                        guarantee_automatas_for_u_item
                    })
                    .collect()
            },
            || {
                rayon::join(
                    || {
                        ctx.v_items
                            .par_iter()
                            .enumerate()
                            .map(|(v_item, _)| {
                                let mut safety_automatas_for_v_item: Vec<_> =
                                    Vec::with_capacity(ctx.m_sets.len());
                                for (m_set, _) in ctx.m_sets.iter().enumerate() {
                                    let safety_automata = safety::dump(
                                        ctx,
                                        pltl_ctx,
                                        v_item as u32,
                                        m_set as u32,
                                        &weakening_conditions_automata,
                                    );
                                    safety_automatas_for_v_item
                                        .push(safety_automata.build(pltl_ctx));
                                }
                                safety_automatas_for_v_item
                            })
                            .collect()
                    },
                    || {
                        ctx.m_sets
                            .par_iter()
                            .enumerate()
                            .map(|(m_set, _)| {
                                let stable_automata = stable::dump(
                                    ctx,
                                    pltl_ctx,
                                    m_set as u32,
                                    &weakening_conditions_automata,
                                );
                                stable_automata.build(pltl_ctx)
                            })
                            .collect()
                    },
                )
            },
        );
        Self {
            guarantee_automatas,
            safety_automatas,
            stable_automatas,
        }
    }

    fn makefile_content(&self) -> String {
        let mut makefile_content = "default: result.hoa\n".to_string();
        for m_id in 0u32..(1 << self.guarantee_automatas.len()) {
            for n_id in 0u32..(1 << self.safety_automatas.len()) {
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
        let file_name = "result.hoa".to_string();
        makefile_content += &format!("{}: ", file_name);
        for m_id in 0u32..(1 << self.guarantee_automatas.len()) {
            for n_id in 0u32..(1 << self.safety_automatas.len()) {
                makefile_content += &format!("rabin_0b{:b}_0b{:b}.hoa ", m_id, n_id);
            }
        }
        makefile_content += &format!(
            "\n\tautfilt --gra --generic --complete -D -o {} ",
            file_name
        );
        for m_id in 0u32..(1 << self.guarantee_automatas.len()) {
            for n_id in 0u32..(1 << self.safety_automatas.len()) {
                if m_id == 0 && n_id == 0 {
                    makefile_content += &format!("-F rabin_0b{:b}_0b{:b}.hoa ", m_id, n_id);
                } else {
                    makefile_content +=
                        &format!("--product-or=rabin_0b{:b}_0b{:b}.hoa ", m_id, n_id);
                }
            }
        }
        makefile_content += "\n";
        makefile_content
    }

    pub fn to_files(&self) -> Vec<(String, String)> {
        let mut result = Vec::new();
        for (u_item_id, automatas_for_n_set) in self.guarantee_automatas.iter().enumerate() {
            for (n_set, automata) in automatas_for_n_set.iter().enumerate() {
                let file_name = format!("guarantee_{u_item_id}_0b{:b}.hoa", n_set);
                result.push((file_name, to_hoa(automata)));
            }
        }
        for (v_item_id, automatas_for_m_set) in self.safety_automatas.iter().enumerate() {
            for (m_set, automata) in automatas_for_m_set.iter().enumerate() {
                let file_name = format!("safety_0b{:b}_{v_item_id}.hoa", m_set);
                result.push((file_name, to_hoa(automata)));
            }
        }
        for (m_set, automata) in self.stable_automatas.iter().enumerate() {
            let file_name = format!("stable_0b{:b}.hoa", m_set);
            result.push((file_name, to_hoa(automata)));
        }
        let makefile_content = self.makefile_content();
        result.push(("Makefile".to_string(), makefile_content));
        result
    }

    pub fn to_dots(
        &self,
        ctx: &Context,
        pltl_ctx: &pltl::Context,
    ) -> (
        Vec<(String, String)>,
        Vec<(String, String)>,
        Vec<(String, String)>,
    ) {
        let mut guarantee_dots = Vec::new();
        let mut safety_dots = Vec::new();
        let mut stable_dots = Vec::new();
        for (u_item_id, automatas_for_n_set) in self.guarantee_automatas.iter().enumerate() {
            for (n_set, automata) in automatas_for_n_set.iter().enumerate() {
                let psi = ctx.u_items[u_item_id].format(pltl_ctx);
                let n_items = ctx.n_sets[n_set]
                    .iter()
                    .map(|pltl| pltl.format(pltl_ctx))
                    .collect::<Vec<_>>()
                    .join(", ");
                guarantee_dots.push((
                    format!("\\psi={psi}, N=\\{{{n_items}\\}}"),
                    to_dot(automata),
                ));
            }
        }
        for (v_item_id, automatas_for_m_set) in self.safety_automatas.iter().enumerate() {
            for (m_set, automata) in automatas_for_m_set.iter().enumerate() {
                let psi = ctx.v_items[v_item_id].format(pltl_ctx);
                let m_items = ctx.m_sets[m_set]
                    .iter()
                    .map(|pltl| pltl.format(pltl_ctx))
                    .collect::<Vec<_>>()
                    .join(", ");
                safety_dots.push((
                    format!("\\psi={psi}, M=\\{{{m_items}\\}}"),
                    to_dot(automata),
                ));
            }
        }
        for (m_set, automata) in self.stable_automatas.iter().enumerate() {
            let m_items = ctx.m_sets[m_set]
                .iter()
                .map(|pltl| pltl.format(pltl_ctx))
                .collect::<Vec<_>>()
                .join(", ");
            stable_dots.push((format!("M=\\{{{m_items}\\}}"), to_dot(automata)));
        }
        (guarantee_dots, safety_dots, stable_dots)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_files() {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build_global()
            .unwrap();
        let (ltl, ltl_ctx) = PLTL::from_string("G p | F (p S q) & (r B s)").unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        println!("ltl: {}", ltl);
        let ctx = Context::new(&ltl);
        println!("ctx: {}", ctx);
        let automatas = AllSubAutomatas::new(&ctx, &ltl_ctx);
        println!("{:?}", automatas.to_dots(&ctx, &ltl_ctx));
    }
}
