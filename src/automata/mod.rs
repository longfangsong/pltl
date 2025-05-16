use crate::{
    pltl::{
        self,
        labeled::{self, after_function::CacheItem, LabeledPLTL},
        PLTL,
    },
    utils::{character_to_label_expression, powerset_vec, BitSet, BitSet32, ConcurrentMap, Map},
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
use std::{collections::HashMap, fmt, hash::Hash, mem, sync::RwLock, time::Instant};

mod guarantee;
pub mod hoa;
mod safety;
pub mod stable;
mod weakening_conditions;

// cache for a certain m_set under a certain c_set
#[derive(Debug, Clone)]
pub struct MSetUnderCCache {
    mask: BitSet32,
    // c_set & mask -> m_set<c_set>
    cache: Map<BitSet32, Vec<LabeledPLTL>>,
}

impl MSetUnderCCache {
    fn append_one(&self, other: &MSetUnderCCache) -> MSetUnderCCache {
        debug_assert_eq!(other.mask.len(), 1);
        debug_assert_eq!(other.mask & self.mask, 0b0);
        let mask = self.mask | other.mask;
        let mut cache = Map::default();
        let other_u_item = other.mask.trailing_zeros();
        // let other_entry = &current_result[other_u_item as usize];
        for (c_set, m_set) in self.cache.iter() {
            // other is 0b0
            let mut new_result = m_set.clone();
            let other_content = other.get(0b0).unwrap();
            new_result.extend(other_content.iter().cloned());
            let new_c_set: u32 = *c_set;
            cache.insert(new_c_set, new_result);
            // other is mask
            let mut new_result = m_set.clone();
            let other_content = other.get(other.mask).unwrap();
            new_result.extend(other_content.iter().cloned());
            let new_c_set: u32 = *c_set | (1 << other_u_item);
            cache.insert(new_c_set, new_result);
        }
        MSetUnderCCache { mask, cache }
    }
    // build cache
    // Return m_set_id -> m_set<c_set>
    pub fn build(u_items: &[LabeledPLTL]) -> Vec<MSetUnderCCache> {
        let mut result: Vec<_> = (0..(1 << u_items.len()))
            .map(|_| MSetUnderCCache {
                mask: BitSet32::default(),
                cache: Map::default(),
            })
            .collect();
        result[0].cache.insert(0b0, Vec::new());
        for (u_item_id, u_item) in u_items.iter().enumerate() {
            let mask = u_item.past_subformula_ids();
            let cache = mask
                .sub_sets()
                .into_par_iter()
                .map(|c_set| {
                    let single_result = u_item.clone().c_rewrite(c_set);
                    (c_set, vec![single_result])
                })
                .collect();
            result[1 << u_item_id] = MSetUnderCCache { mask, cache };
        }
        let mut current_considering = (0..u_items.len()).map(|i| 1u32 << i).collect::<Vec<_>>();
        for _sub_part_length in 1..u_items.len() as u32 {
            let mut new_considering = Vec::with_capacity(1 << u_items.len());
            for from in current_considering.iter() {
                let start_index = 32 - from.leading_zeros();
                for to_append_index in start_index..(u_items.len() as u32) {
                    new_considering.push(from | (1u32 << to_append_index));
                    result[(from | (1u32 << to_append_index)) as usize] = result[*from as usize]
                        .append_one(&result[(1u32 << to_append_index) as usize]);
                }
            }
            mem::swap(&mut current_considering, &mut new_considering);
        }
        result
    }

    pub fn get(&self, c_set: u32) -> Option<&Vec<LabeledPLTL>> {
        self.cache.get(&(c_set & self.mask))
    }
}

#[derive(Debug)]
pub struct Context {
    pub initial: LabeledPLTL,
    pub pltl_context: pltl::Context,
    pub label_context: labeled::Context,
    // ci => cj
    pub saturated_c_sets: Vec<Vec<u32>>,
    pub u_items: Vec<LabeledPLTL>,
    pub v_items: Vec<LabeledPLTL>,
    pub m_sets_items_under_c_sets: Vec<MSetUnderCCache>,

    pub n_sets: Vec<Vec<LabeledPLTL>>,
    pub m_sets: Vec<Vec<LabeledPLTL>>,

    pub v_rewrite_cache: Vec<ConcurrentMap<LabeledPLTL, LabeledPLTL>>,
    pub u_rewrite_cache: Vec<ConcurrentMap<LabeledPLTL, LabeledPLTL>>,
    // m_set -> c_set_with_mask -> f -> f[M<c_i>]
    pub m_set_under_c_rewrite_cache:
        Vec<Map<BitSet32, ConcurrentMap<LabeledPLTL, LabeledPLTL>>>,

    pub local_after_cache: RwLock<Map<LabeledPLTL, CacheItem>>,
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

    pub fn new(ltl: &PLTL, pltl_context: &pltl::Context) -> Self {
        let (labeled_pltl, psf_context) = LabeledPLTL::new(ltl);
        let saturated_c_sets = Self::compute_saturated_c_set(&psf_context);
        let (u_items, v_items) = labeled_pltl.u_v_subformulas();
        let mut u_items: Vec<_> = u_items.into_iter().collect();
        u_items.sort();
        let mut v_items: Vec<_> = v_items.into_iter().collect();
        v_items.sort();
        let m_sets = powerset_vec(&u_items);
        let n_sets = powerset_vec(&v_items);
        let v_rewrite_cache = m_sets.iter().map(|_| ConcurrentMap::default()).collect();
        let u_rewrite_cache = n_sets.iter().map(|_| ConcurrentMap::default()).collect();
        let m_sets_items_under_c_sets = MSetUnderCCache::build(&u_items);
        let m_set_under_c_rewrite_cache = m_sets_items_under_c_sets.iter().map(|m_under_c_cache| {
            m_under_c_cache.cache.iter().map(|(c_set, _)| {
                (*c_set, ConcurrentMap::default())
            }).collect()
        }).collect();
        Self {
            initial: labeled_pltl,
            pltl_context: pltl_context.clone(),
            label_context: psf_context,
            saturated_c_sets,
            u_items,
            v_items,
            n_sets,
            m_sets,
            v_rewrite_cache,
            u_rewrite_cache,
            local_after_cache: RwLock::new(Map::default()),
            m_sets_items_under_c_sets,
            m_set_under_c_rewrite_cache,
        }
    }

    pub fn cached_v_rewrite(&self, item: &LabeledPLTL, m_set: u32) -> LabeledPLTL {
        if matches!(
            item,
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_)
        ) {
            return item.clone();
        }

        let got_item = self.v_rewrite_cache[m_set as usize].get(item);
        if let Some(result) = got_item {
            return result.clone();
        }
        let v_item = item.clone();
        let result = v_item.clone().v_rewrite(&self.m_sets[m_set as usize]);

        self.v_rewrite_cache[m_set as usize].insert(v_item, result.clone());

        result
    }

    pub fn cached_m_set_under_c_rewrite(
        &self,
        m_set: u32,
        c_set: u32,
        item: &LabeledPLTL,
    ) -> LabeledPLTL {
        let masked_c_set = self.m_sets_items_under_c_sets[m_set as usize].mask & c_set;
        let entry = &self.m_set_under_c_rewrite_cache[m_set as usize][&masked_c_set];
        if let Some(result) = entry.get(item) {
            return result.clone();
        } else {
            let result = item.clone().v_rewrite(
                &self.m_sets_items_under_c_sets[m_set as usize]
                    .get(c_set as u32)
                    .unwrap(),
            ).simplify();
            entry.insert(item.clone(), result.clone());
            return result;
        }
    }

    pub fn cached_u_rewrite(&self, iten: &LabeledPLTL, n_set: u32) -> LabeledPLTL {
        if matches!(
            iten,
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_)
        ) {
            return iten.clone();
        }
        let got_item = self.u_rewrite_cache[n_set as usize].get(iten);
        if let Some(result) = got_item {
            return result.clone();
        }
        let u_item = iten.clone();
        let result = u_item
            .clone()
            .u_rewrite(&self.n_sets[n_set as usize])
            .simplify();
        self.u_rewrite_cache[n_set as usize].insert(u_item, result.clone());
        result
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.label_context)?;
        if self.saturated_c_sets.len() < 16 {
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
        } else {
            writeln!(f, "J: <{}> Js", self.saturated_c_sets.len())?;
        }
        for (i, u) in self.u_items.iter().enumerate() {
            writeln!(f, "u{i}: {u}")?;
        }
        for (i, v) in self.v_items.iter().enumerate() {
            writeln!(f, "v{i}: {v}")?;
        }
        if self.n_sets.len() < 16 {
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
        } else {
            writeln!(f, "N: <{}> Ns", self.n_sets.len())?;
        }
        if self.m_sets.len() < 16 {
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
        } else {
            writeln!(f, "M: <{}> Ms", self.m_sets.len())?;
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
                    let file_name = format!("b2_0b{m_id:b}_0b{n_id:b}.hoa");
                    makefile_content += &format!("{file_name}: ");
                    makefile_content += &m_id
                        .iter()
                        .map(|u_item_id| format!("guarantee_{u_item_id}_0b{n_id:b}.hoa "))
                        .join(" ");
                    makefile_content += &format!("\n\tautfilt --Buchi -o {file_name} ");
                    makefile_content += &m_id
                        .iter()
                        .enumerate()
                        .map(|(id, u_item_id)| {
                            if id == 0 {
                                format!("-F guarantee_{u_item_id}_0b{n_id:b}.hoa ")
                            } else {
                                format!("--product=guarantee_{u_item_id}_0b{n_id:b}.hoa ")
                            }
                        })
                        .join(" ");
                    makefile_content += "\n";
                }
                if n_id != 0 {
                    let file_name = format!("c3_0b{m_id:b}_0b{n_id:b}.hoa");
                    makefile_content += &format!("{file_name}: ");
                    makefile_content += &n_id
                        .iter()
                        .map(|v_item_id| format!("safety_0b{m_id:b}_{v_item_id}.hoa "))
                        .join(" ");
                    makefile_content += &format!("\n\tautfilt --coBuchi -o {file_name} ");
                    makefile_content += &n_id
                        .iter()
                        .enumerate()
                        .map(|(i, v_item_id)| {
                            if i == 0 {
                                format!("-F safety_0b{m_id:b}_{v_item_id}.hoa ")
                            } else {
                                format!("--product=safety_0b{m_id:b}_{v_item_id}.hoa ")
                            }
                        })
                        .join(" ");
                    makefile_content += "\n";
                }

                let file_name = format!("rabin_0b{m_id:b}_0b{n_id:b}.hoa");
                makefile_content += &format!("{file_name}: ");
                makefile_content += &format!("stable_0b{m_id:b}.hoa ");
                if m_id != 0 {
                    makefile_content += &format!("b2_0b{m_id:b}_0b{n_id:b}.hoa ");
                }
                if n_id != 0 {
                    makefile_content += &format!("c3_0b{m_id:b}_0b{n_id:b}.hoa ");
                }
                makefile_content += &format!("\n\tautfilt --gra -o {file_name} ");
                makefile_content += &format!("-F stable_0b{m_id:b}.hoa ");
                if m_id != 0 {
                    makefile_content += &format!("--product=b2_0b{m_id:b}_0b{n_id:b}.hoa ");
                }
                if n_id != 0 {
                    makefile_content += &format!("--product=c3_0b{m_id:b}_0b{n_id:b}.hoa");
                }
                makefile_content += "\n";
            }
        }
        let file_name = "result.hoa".to_string();
        makefile_content += &format!("{file_name}: ");
        for m_id in 0u32..(1 << self.guarantee_automatas.len()) {
            for n_id in 0u32..(1 << self.safety_automatas.len()) {
                makefile_content += &format!("rabin_0b{m_id:b}_0b{n_id:b}.hoa ");
            }
        }
        makefile_content +=
            &format!("\n\tautfilt --gra --generic --complete -D -S -o {file_name} ");
        for m_id in 0u32..(1 << self.guarantee_automatas.len()) {
            for n_id in 0u32..(1 << self.safety_automatas.len()) {
                if m_id == 0 && n_id == 0 {
                    makefile_content += &format!("-F rabin_0b{m_id:b}_0b{n_id:b}.hoa ");
                } else {
                    makefile_content += &format!("--product-or=rabin_0b{m_id:b}_0b{n_id:b}.hoa ");
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
                let file_name = format!("guarantee_{u_item_id}_0b{n_set:b}.hoa");
                result.push((file_name, to_hoa(automata)));
            }
        }
        for (v_item_id, automatas_for_m_set) in self.safety_automatas.iter().enumerate() {
            for (m_set, automata) in automatas_for_m_set.iter().enumerate() {
                let file_name = format!("safety_0b{m_set:b}_{v_item_id}.hoa");
                result.push((file_name, to_hoa(automata)));
            }
        }
        for (m_set, automata) in self.stable_automatas.iter().enumerate() {
            let file_name = format!("stable_0b{m_set:b}.hoa");
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
        println!("ltl: {ltl}");
        let ctx = Context::new(&ltl, &ltl_ctx);
        println!("ctx: {ctx}");
        let automatas = AllSubAutomatas::new(&ctx, &ltl_ctx);
        println!("{:?}", automatas.to_dots(&ctx, &ltl_ctx));
    }

    #[test]
    fn test_compute_m_sets_items_under_c_sets() {
        let (ltl, ltl_ctx) = PLTL::from_string("F ( r & (r S p))").unwrap();
        let ltl = ltl.to_no_fgoh().to_negation_normal_form().simplify();
        let ctx = Context::new(&ltl, &ltl_ctx);
        println!("ctx: {ctx}");
        let result = MSetUnderCCache::build(&ctx.u_items);
        for (m_set, result_at_m) in result.iter().enumerate() {
            println!("m_set: 0b{m_set:03b}");
            println!("    mask: 0b{:09b}", result_at_m.mask);
            for (c_set, items) in result_at_m.cache.iter() {
                println!(
                    "    c_set: 0b{:03b}, items: {}",
                    c_set,
                    items
                        .iter()
                        .map(|item| item.format(&ltl_ctx))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
        }
        // println!("ctx: {:?}", ctx.m_sets_items_under_c_sets);
        // for (c_set, m_rewrite_results) in ctx.m_sets_items_under_c_sets.iter().enumerate() {
        //     for (m_set, items) in m_rewrite_results.iter().enumerate() {
        //         println!(
        //             "m_set: 0b{m_set:02b}, c_set: 0b{c_set:02b}, items: {}",
        //             items
        //                 .iter()
        //                 .map(|item| item.format(&ltl_ctx))
        //                 .collect::<Vec<_>>()
        //                 .join(", ")
        //         );
        //     }
        // }
    }
}
