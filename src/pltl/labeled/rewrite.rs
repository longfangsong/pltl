use crate::utils::{BitSet, BitSet32, Set};

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

    pub fn v_rewrite(self, m: &Set<LabeledPLTL>) -> Self {
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
            LabeledPLTL::Until { weak, lhs, rhs } | LabeledPLTL::Release { weak, lhs, rhs } => {
                if contains {
                    LabeledPLTL::Until {
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

    pub fn u_rewrite(self, n: &Set<LabeledPLTL>) -> Self {
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
            LabeledPLTL::Until { weak, lhs, rhs } | LabeledPLTL::Release { weak, lhs, rhs } => {
                if contains {
                    LabeledPLTL::Top
                } else {
                    LabeledPLTL::Until {
                        weak,
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

#[cfg(test)]
mod tests {

    #[test]
    fn test_rewrite() {
        // let (pltl, pltl_ctx) = PLTL::from_string("a U (b S (c U d))").unwrap();
        // let pltl = pltl.to_no_fgoh().to_negation_normal_form().simplify();
        // let (labeled_pltl, context) = LabeledPLTL::new(&pltl);
        // let mut m = Set::default();
        // m.insert(labeled_pltl.clone());
        // let inner = if let LabeledPLTL::Binary(_, _, rhs) = &labeled_pltl {
        //     if let LabeledPLTL::LabeledPastSubformula { id, weaken_state, content } = rhs.as_ref() {
        //         if let LabeledPLTL::Binary(_, _, rhs) = content.as_ref() {
        //             rhs.deref().clone()
        //         } else {
        //             unreachable!()
        //         }
        //     } else {
        //         unreachable!()
        //     }
        // } else {
        //     unreachable!()
        // };
        // m.insert(inner);

        // let mut labeled_pltl = labeled_pltl;
        // labeled_pltl.v_rewrite(&m);
        // assert_eq!(labeled_pltl.format(&context, &pltl_ctx), "(a W <0, 0b0, (b S (c W d))>)");

        // labeled_pltl.c_rewrite(0b1);
        // assert_eq!(labeled_pltl.format(&context, &pltl_ctx), "(a W <0, 0b1, (b S (c W d))>)");

        // let (pltl, pltl_ctx) = PLTL::from_string("a U (b S (c U (Y d)))").unwrap();
        // let pltl = pltl.to_no_fgoh().to_negation_normal_form().simplify();
        // let (labeled_pltl, context) = LabeledPLTL::new(&pltl);
        // println!("{}", labeled_pltl);
        // println!("{}", context);

        // let mut m = Set::default();
        // m.insert(labeled_pltl.clone());

        // let mut labeled_pltl = labeled_pltl;
        // labeled_pltl.c_rewrite(0b01);
        // labeled_pltl.push_down_weaken_state();
        // labeled_pltl.normalize(&context);
        // println!("{}", labeled_pltl);
        // println!("{}", labeled_pltl.format(&context, &pltl_ctx));
        // println!(
        //     "{}",
        //     if let LabeledPLTL::Binary(_, _, rhs) = &labeled_pltl {
        //         if let LabeledPLTL::LabeledPastSubformula { content, .. } = rhs.as_ref() {
        //             if let LabeledPLTL::Binary(_, _, rhs) = content.as_ref() {
        //                 rhs
        //             } else {
        //                 unreachable!()
        //             }
        //         } else {
        //             unreachable!()
        //         }
        //     } else {
        //         unreachable!()
        //     }
        // );
        // let inner = if let LabeledPLTL::Binary(_, _, rhs) = &labeled_pltl {
        //     if let LabeledPLTL::LabeledPastSubformula {
        //         id,
        //         weaken_state,
        //         content,
        //     } = rhs.as_ref()
        //     {
        //         if let LabeledPLTL::Binary(_, _, rhs) = content.as_ref() {
        //             if let LabeledPLTL::Binary(_, _, rhs) = rhs.as_ref() {
        //                 rhs.deref().clone()
        //             } else {
        //                 unreachable!()
        //             }
        //         } else {
        //             unreachable!()
        //         }
        //     } else {
        //         unreachable!()
        //     }
        // } else {
        //     unreachable!()
        // };
        // println!("{}", inner);
        // println!("{}", inner.format(&context, &pltl_ctx));
        // // m.insert(inner);
    }
}
