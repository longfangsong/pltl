use crate::utils::{BitSet, BitSet32};

use super::LabeledPLTL;

impl LabeledPLTL {
    pub fn c_rewrite(self, set: BitSet32) -> Self {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                self
            }
            LabeledPLTL::Yesterday { id, weak, content } => LabeledPLTL::Yesterday {
                id,
                weak: set.get(id),
                content: Box::new(content.c_rewrite(set)),
            },
            LabeledPLTL::Next(labeled_pltl) => {
                LabeledPLTL::Next(Box::new(labeled_pltl.c_rewrite(set)))
            }
            LabeledPLTL::Logical(binary_op, content) => LabeledPLTL::Logical(
                binary_op,
                content
                    .into_iter()
                    .map(|item| item.c_rewrite(set))
                    .collect(),
            ),
            LabeledPLTL::Until { weak, lhs, rhs } => LabeledPLTL::Until {
                weak,
                lhs: Box::new(lhs.c_rewrite(set)),
                rhs: Box::new(rhs.c_rewrite(set)),
            },
            LabeledPLTL::Release { weak, lhs, rhs } => LabeledPLTL::Release {
                weak,
                lhs: Box::new(lhs.c_rewrite(set)),
                rhs: Box::new(rhs.c_rewrite(set)),
            },
            LabeledPLTL::BinaryTemporal {
                id,
                op,
                weak,
                lhs,
                rhs,
            } => LabeledPLTL::BinaryTemporal {
                id,
                op,
                weak: set.get(id),
                lhs: Box::new(lhs.c_rewrite(set)),
                rhs: Box::new(rhs.c_rewrite(set)),
            },
        }
    }

    pub fn v_rewrite(self, m: &[LabeledPLTL]) -> Self {
        let contains = matches!(
            self,
            LabeledPLTL::Until { .. } | LabeledPLTL::Release { .. }
        ) && m.contains(&self);
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                self
            }
            LabeledPLTL::Yesterday { id, weak, content } => LabeledPLTL::Yesterday {
                id,
                weak,
                content: Box::new(content.v_rewrite(m)),
            },
            LabeledPLTL::Next(labeled_pltl) => {
                LabeledPLTL::Next(Box::new(labeled_pltl.v_rewrite(m)))
            }
            LabeledPLTL::Logical(op, content) => LabeledPLTL::Logical(
                op,
                content.into_iter().map(|item| item.v_rewrite(m)).collect(),
            ),
            LabeledPLTL::Until { weak, lhs, rhs } => {
                if contains || weak {
                    LabeledPLTL::Until {
                        weak: true,
                        lhs: Box::new(lhs.v_rewrite(m)),
                        rhs: Box::new(rhs.v_rewrite(m)),
                    }
                } else {
                    LabeledPLTL::Bottom
                }
            }
            LabeledPLTL::Release { weak, lhs, rhs } => {
                if contains || weak {
                    LabeledPLTL::Release {
                        weak: true,
                        lhs: Box::new(lhs.v_rewrite(m)),
                        rhs: Box::new(rhs.v_rewrite(m)),
                    }
                } else {
                    LabeledPLTL::Bottom
                }
            }
            LabeledPLTL::BinaryTemporal {
                lhs,
                rhs,
                id,
                op,
                weak,
            } => LabeledPLTL::BinaryTemporal {
                id,
                lhs: Box::new(lhs.v_rewrite(m)),
                rhs: Box::new(rhs.v_rewrite(m)),
                op,
                weak,
            },
        }
    }

    pub fn u_rewrite(self, n: &[LabeledPLTL]) -> Self {
        let contains = matches!(
            self,
            LabeledPLTL::Until { .. } | LabeledPLTL::Release { .. }
        ) && n.contains(&self);
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                self
            }
            LabeledPLTL::Yesterday { id, weak, content } => LabeledPLTL::Yesterday {
                id,
                weak,
                content: Box::new(content.u_rewrite(n)),
            },
            LabeledPLTL::Next(labeled_pltl) => {
                LabeledPLTL::Next(Box::new(labeled_pltl.u_rewrite(n)))
            }
            LabeledPLTL::Logical(op, content) => LabeledPLTL::Logical(
                op,
                content.into_iter().map(|item| item.u_rewrite(n)).collect(),
            ),
            LabeledPLTL::Until { lhs, rhs, .. } => {
                if contains {
                    LabeledPLTL::Top
                } else {
                    LabeledPLTL::Until {
                        weak: false,
                        lhs: Box::new(lhs.u_rewrite(n)),
                        rhs: Box::new(rhs.u_rewrite(n)),
                    }
                }
            }
            LabeledPLTL::Release { lhs, rhs, .. } => {
                if contains {
                    LabeledPLTL::Top
                } else {
                    LabeledPLTL::Release {
                        weak: false,
                        lhs: Box::new(lhs.u_rewrite(n)),
                        rhs: Box::new(rhs.u_rewrite(n)),
                    }
                }
            }
            LabeledPLTL::BinaryTemporal {
                id,
                op,
                weak,
                lhs,
                rhs,
            } => LabeledPLTL::BinaryTemporal {
                id,
                op,
                weak,
                lhs: Box::new(lhs.u_rewrite(n)),
                rhs: Box::new(rhs.u_rewrite(n)),
            },
        }
    }
}
