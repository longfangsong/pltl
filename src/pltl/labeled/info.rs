use crate::{
    pltl::BinaryOp,
    utils::{BitSet, BitSet32, Set},
};

use super::LabeledPLTL;

impl LabeledPLTL {
    pub fn past_subformulas(&self) -> Set<Self> {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                Set::default()
            }
            LabeledPLTL::Yesterday { content, .. } => {
                let mut result = content.past_subformulas();
                result.insert(self.clone());
                result
            }
            LabeledPLTL::Next(content) => content.past_subformulas(),
            LabeledPLTL::Logical(_, content) => {
                let mut result = Set::default();
                for item in content {
                    result.extend(item.past_subformulas());
                }
                result
            }
            LabeledPLTL::Until { lhs, rhs, .. } => {
                let lhs_result = lhs.past_subformulas();
                let rhs_result = rhs.past_subformulas();
                &lhs_result | &rhs_result
            }
            LabeledPLTL::Release { lhs, rhs, .. } => {
                let lhs_result = lhs.past_subformulas();
                let rhs_result = rhs.past_subformulas();
                &lhs_result | &rhs_result
            }
            LabeledPLTL::BinaryTemporal { lhs, rhs, .. } => {
                let lhs_result = lhs.past_subformulas();
                let rhs_result = rhs.past_subformulas();
                let mut result = &lhs_result | &rhs_result;
                result.insert(self.clone());
                result
            }
        }
    }

    pub fn past_subformula_ids(&self) -> BitSet32 {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                BitSet32::default()
            }
            LabeledPLTL::Yesterday { id, content, .. } => {
                let mut result = content.past_subformula_ids();
                result.set_bit(*id);
                result
            }
            LabeledPLTL::Next(content) => content.past_subformula_ids(),
            LabeledPLTL::Logical(_, content) => {
                let mut result = BitSet32::default();
                for item in content {
                    result |= item.past_subformula_ids();
                }
                result
            }
            LabeledPLTL::Until { lhs, rhs, .. } => {
                let lhs_result = lhs.past_subformula_ids();
                let rhs_result = rhs.past_subformula_ids();
                lhs_result | rhs_result
            }
            LabeledPLTL::Release { lhs, rhs, .. } => {
                let lhs_result = lhs.past_subformula_ids();
                let rhs_result = rhs.past_subformula_ids();
                lhs_result | rhs_result
            }
            LabeledPLTL::BinaryTemporal { lhs, rhs, id, .. } => {
                let lhs_result = lhs.past_subformula_ids();
                let rhs_result = rhs.past_subformula_ids();
                let mut result = lhs_result | rhs_result;
                result.set_bit(*id);
                result
            }
        }
    }

    pub fn weaken_condition(&self) -> Self {
        match self {
            LabeledPLTL::Yesterday {
                content: box content,
                ..
            } => content.clone(),
            LabeledPLTL::BinaryTemporal {
                id,
                op,
                weak,
                lhs: box lhs,
                rhs: box rhs,
            } => match (op, weak) {
                (BinaryOp::Since | BinaryOp::WeakSince, true) => lhs.clone() | rhs.clone(),
                (BinaryOp::Since | BinaryOp::WeakSince, false) => rhs.clone(),
                (BinaryOp::BackTo | BinaryOp::WeakBackTo, true) => rhs.clone(),
                (BinaryOp::BackTo | BinaryOp::WeakBackTo, false) => lhs.clone() & rhs.clone(),
                _ => unreachable!("invalid function"),
            },
            _ => unreachable!("weaken_condition is only defined for past subformulas"),
        }
    }

    pub fn weaken_state(&self) -> BitSet32 {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                BitSet32::default()
            }
            LabeledPLTL::Yesterday { id, content, weak } => {
                let mut result = content.weaken_state();
                result.set(*id, *weak);
                result
            }
            LabeledPLTL::Next(content) => content.weaken_state(),
            LabeledPLTL::Logical(_, content) => {
                let mut result = BitSet32::default();
                for item in content {
                    result |= item.weaken_state();
                }
                result
            }
            LabeledPLTL::Until { lhs, rhs, .. } => lhs.weaken_state() | rhs.weaken_state(),
            LabeledPLTL::Release { lhs, rhs, .. } => lhs.weaken_state() | rhs.weaken_state(),
            LabeledPLTL::BinaryTemporal {
                id, weak, lhs, rhs, ..
            } => {
                let mut result = lhs.weaken_state() | rhs.weaken_state();
                result.set(*id, *weak);
                result
            }
        }
    }

    pub fn v_subformulas(&self) -> Set<Self> {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                Set::default()
            }
            LabeledPLTL::Yesterday { content, .. } => content.v_subformulas(),
            LabeledPLTL::Next(content) => content.v_subformulas(),
            LabeledPLTL::Logical(_, content) => {
                let mut result = Set::default();
                for item in content {
                    result.extend(item.v_subformulas());
                }
                result
            }
            LabeledPLTL::Until {
                weak: false,
                lhs,
                rhs,
            }
            | LabeledPLTL::Release {
                weak: false,
                lhs,
                rhs,
            } => {
                let mut result = lhs.v_subformulas();
                result.extend(rhs.v_subformulas());
                result.insert(self.clone());
                result
            }
            LabeledPLTL::Until {
                weak: true,
                lhs,
                rhs,
            }
            | LabeledPLTL::Release {
                weak: true,
                lhs,
                rhs,
            } => {
                let mut result: std::collections::HashSet<
                    LabeledPLTL,
                    std::hash::BuildHasherDefault<fxhash::FxHasher>,
                > = lhs.v_subformulas();
                result.extend(rhs.v_subformulas());
                result
            }
            LabeledPLTL::BinaryTemporal { lhs, rhs, .. } => {
                let mut result = lhs.v_subformulas();
                result.extend(rhs.v_subformulas());
                result
            }
        }
    }

    pub fn u_subformulas(&self) -> Set<Self> {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                Set::default()
            }
            LabeledPLTL::Yesterday { content, .. } => content.u_subformulas(),
            LabeledPLTL::Next(content) => content.u_subformulas(),
            LabeledPLTL::Logical(_, content) => {
                let mut result = Set::default();
                for item in content {
                    result.extend(item.u_subformulas());
                }
                result
            }
            LabeledPLTL::Until {
                weak: true,
                lhs,
                rhs,
            }
            | LabeledPLTL::Release {
                weak: true,
                lhs,
                rhs,
            } => {
                let mut result = lhs.u_subformulas();
                result.extend(rhs.u_subformulas());
                result.insert(self.clone());
                result
            }
            LabeledPLTL::Until {
                weak: false,
                lhs,
                rhs,
            }
            | LabeledPLTL::Release {
                weak: false,
                lhs,
                rhs,
            } => {
                let mut result: std::collections::HashSet<
                    LabeledPLTL,
                    std::hash::BuildHasherDefault<fxhash::FxHasher>,
                > = lhs.u_subformulas();
                result.extend(rhs.u_subformulas());
                result
            }
            LabeledPLTL::BinaryTemporal { lhs, rhs, .. } => {
                let mut result = lhs.u_subformulas();
                result.extend(rhs.u_subformulas());
                result
            }
        }
    }

    pub fn u_v_subformulas(&self) -> (Set<Self>, Set<Self>) {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                (Set::default(), Set::default())
            }
            LabeledPLTL::Yesterday { content, .. } => content.u_v_subformulas(),
            LabeledPLTL::Next(content) => content.u_v_subformulas(),
            LabeledPLTL::Logical(_, content) => {
                let mut result = (Set::default(), Set::default());
                for item in content {
                    let (u, v) = item.u_v_subformulas();
                    result.0.extend(u);
                    result.1.extend(v);
                }
                result
            }
            LabeledPLTL::Until { weak, lhs, rhs } => {
                let (mut u_lhs, mut v_lhs) = lhs.u_v_subformulas();
                let (u_rhs, v_rhs) = rhs.u_v_subformulas();
                u_lhs.extend(u_rhs);
                v_lhs.extend(v_rhs);
                if *weak {
                    v_lhs.insert(self.clone());
                } else {
                    u_lhs.insert(self.clone());
                }
                (u_lhs, v_lhs)
            }
            LabeledPLTL::Release { weak, lhs, rhs } => {
                let (mut u_lhs, mut v_lhs) = lhs.u_v_subformulas();
                let (u_rhs, v_rhs) = rhs.u_v_subformulas();
                u_lhs.extend(u_rhs);
                v_lhs.extend(v_rhs);
                if *weak {
                    v_lhs.insert(self.clone());
                } else {
                    u_lhs.insert(self.clone());
                }
                (u_lhs, v_lhs)
            }
            LabeledPLTL::BinaryTemporal { lhs, rhs, .. } => {
                let (mut u_lhs, mut v_lhs) = lhs.u_v_subformulas();
                let (u_rhs, v_rhs) = rhs.u_v_subformulas();
                u_lhs.extend(u_rhs);
                v_lhs.extend(v_rhs);
                (u_lhs, v_lhs)
            }
        }
    }
}
