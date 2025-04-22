use std::fmt::{self, Display};

use hoa::{
    output::{to_dot, to_hoa},
    HoaAutomaton,
};
use itertools::Itertools;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{
    pltl::{
        self,
        labeled::{Context as PsfContext, LabeledPLTL},
        BinaryOp, PLTL,
    },
    utils::{powerset, BitSet, Map, Set},
};

mod guarantee;
pub mod hoa;
mod safety;
mod stable;
mod weakening_conditions;

#[derive(Debug, Clone)]
pub struct Context<'a> {
    pub labeled_pltl: LabeledPLTL,
    pub pltl_context: pltl::Context,
    pub psf_context: PsfContext<'a>,
    // ci => cj
    pub saturated_c_sets: Vec<Vec<u32>>,
    pub u_items: Vec<LabeledPLTL>,
    pub v_items: Vec<LabeledPLTL>,
    pub n_sets: Vec<Set<LabeledPLTL>>,
    pub m_sets: Vec<Set<LabeledPLTL>>,
}

fn compute_saturated_c_set(psf_context: &PsfContext<'_>) -> Vec<Vec<u32>> {
    (0..(1 << psf_context.expand_once.len()))
        .into_par_iter()
        .map(|ci| {
            let mut result = Vec::new();
            'check_cj: for cj in 0..(1 << psf_context.expand_once.len()) {
                'check_psf: for (psf0_id, psf0) in psf_context.expand_once.iter().enumerate() {
                    for psf1 in &psf_context.expand_once[psf0_id + 1..] {
                        let mut psf0_rewrite_cj = psf0.clone();
                        let mut psf1_rewrite_cj = psf1.clone();
                        psf0_rewrite_cj.rewrite_with_set(cj);
                        psf0_rewrite_cj.normalize(psf_context);
                        psf0_rewrite_cj = psf0_rewrite_cj.simplify();
                        psf1_rewrite_cj.rewrite_with_set(cj);
                        psf1_rewrite_cj.normalize(psf_context);
                        psf1_rewrite_cj = psf1_rewrite_cj.simplify();

                        if !LabeledPLTL::eq_under_ctx(
                            &psf0_rewrite_cj,
                            &psf1_rewrite_cj,
                            psf_context,
                        ) {
                            continue 'check_psf;
                        }

                        let mut psf0_rewrite_ci = psf0.clone();
                        let mut psf1_rewrite_ci = psf1.clone();
                        psf0_rewrite_ci.rewrite_with_set(ci);
                        psf0_rewrite_ci.normalize(psf_context);
                        psf0_rewrite_ci = psf0_rewrite_ci.simplify();
                        psf1_rewrite_ci.rewrite_with_set(ci);
                        psf1_rewrite_ci.normalize(psf_context);
                        if !LabeledPLTL::eq_under_ctx(
                            &psf0_rewrite_ci,
                            &psf1_rewrite_ci,
                            psf_context,
                        ) {
                            continue 'check_cj;
                        }
                    }
                }
                // all psf pairs are checked, j is saturated for i
                result.push(cj);
            }
            result
        })
        .collect()
}

// M/u, N/v
fn collect_u_v_items(
    psf_context: &PsfContext<'_>,
    pltl: &PLTL,
    result: &mut (Vec<LabeledPLTL>, Vec<LabeledPLTL>),
) {
    match pltl {
        PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => (),
        PLTL::Unary(_, content) => {
            collect_u_v_items(psf_context, content, result);
        }
        PLTL::Binary(BinaryOp::Until | BinaryOp::MightyRelease, lhs, rhs) => {
            result.0.push(psf_context.to_labeled(pltl));
            collect_u_v_items(psf_context, lhs, result);
            collect_u_v_items(psf_context, rhs, result);
        }
        PLTL::Binary(BinaryOp::WeakUntil | BinaryOp::Release, lhs, rhs) => {
            result.1.push(psf_context.to_labeled(pltl));
            collect_u_v_items(psf_context, lhs, result);
            collect_u_v_items(psf_context, rhs, result);
        }
        PLTL::Binary(_, lhs, rhs) => {
            collect_u_v_items(psf_context, lhs, result);
            collect_u_v_items(psf_context, rhs, result);
        }
    }
}

impl<'a> Context<'a> {
    pub fn new(ltl: &'a PLTL, pltl_context: pltl::Context) -> Self {
        let (labeled_pltl, psf_context) = LabeledPLTL::new(ltl);
        let saturated_c_sets = compute_saturated_c_set(&psf_context);
        let mut m_n_sets = (Vec::new(), Vec::new());
        collect_u_v_items(&psf_context, ltl, &mut m_n_sets);
        let (mut u_items, mut v_items) = m_n_sets;
        u_items.sort();
        v_items.sort();
        u_items.dedup();
        v_items.dedup();
        let m_sets = powerset(u_items.iter().cloned());
        let n_sets = powerset(v_items.iter().cloned());
        Self {
            labeled_pltl,
            pltl_context,
            psf_context,
            saturated_c_sets,
            u_items,
            v_items,
            n_sets,
            m_sets,
        }
    }
}

impl Display for Context<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.psf_context)?;
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

// todo: make it HoaAutomaton Builder
#[derive(Debug, Clone)]
struct AutomataDump<S> {
    init_state: S,
    state_id_map: Map<S, usize>,
    transitions: Map<S, Vec<S>>,
}

impl<S: Display> Display for AutomataDump<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (state, transitions) in &self.transitions {
            writeln!(f, "{}", state)?;
            for (character, transition) in transitions.iter().enumerate() {
                writeln!(f, "  {:b} -> {}", character, transition)?;
            }
        }
        Ok(())
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
    pub fn new(ctx: &Context) -> Self {
        let mut guarantee_automatas: Vec<_> = Vec::with_capacity(ctx.u_items.len());
        let mut safety_automatas: Vec<_> = Vec::with_capacity(ctx.v_items.len());
        let mut stable_automatas: Vec<_> = Vec::with_capacity(ctx.m_sets.len());
        let weakening_conditions_automata = weakening_conditions::dump(ctx);
        for (u_item, _) in ctx.u_items.iter().enumerate() {
            let mut guarantee_automatas_for_u_item: Vec<_> = Vec::with_capacity(ctx.n_sets.len());
            for (n_set, _) in ctx.n_sets.iter().enumerate() {
                let guarantee_automata = guarantee::dump_hoa(
                    ctx,
                    u_item as u32,
                    n_set as u32,
                    &weakening_conditions_automata,
                );
                guarantee_automatas_for_u_item.push(guarantee_automata);
            }
            guarantee_automatas.push(guarantee_automatas_for_u_item);
        }
        for (v_item, _) in ctx.v_items.iter().enumerate() {
            let mut safety_automatas_for_v_item: Vec<_> = Vec::with_capacity(ctx.m_sets.len());
            for (m_set, _) in ctx.m_sets.iter().enumerate() {
                let safety_automata = safety::dump_hoa(
                    ctx,
                    v_item as u32,
                    m_set as u32,
                    &weakening_conditions_automata,
                );
                safety_automatas_for_v_item.push(safety_automata);
            }
            safety_automatas.push(safety_automatas_for_v_item);
        }
        for (m_set, _) in ctx.m_sets.iter().enumerate() {
            let stable_automata =
                stable::dump_hoa(ctx, m_set as u32, &weakening_conditions_automata);
            stable_automatas.push(stable_automata);
        }
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
                let psi = ctx.u_items[u_item_id].format(&ctx.psf_context, &ctx.pltl_context);
                let n_items = ctx.n_sets[n_set]
                    .iter()
                    .map(|pltl| pltl.format(&ctx.psf_context, &ctx.pltl_context))
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
                let psi = ctx.v_items[v_item_id].format(&ctx.psf_context, &ctx.pltl_context);
                let m_items = ctx.m_sets[m_set]
                    .iter()
                    .map(|pltl| pltl.format(&ctx.psf_context, &ctx.pltl_context))
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
                .map(|pltl| pltl.format(&ctx.psf_context, &ctx.pltl_context))
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
        let ctx = Context::new(&ltl, ltl_ctx);
        println!("ctx: {}", ctx);
        let automatas = AllSubAutomatas::new(&ctx);
        println!("{:?}", automatas.to_dots(&ctx));
    }
}
