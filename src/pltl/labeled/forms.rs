use std::mem;

use crate::pltl::BinaryOp;

use super::LabeledPLTL;

// impl LabeledPLTL {
//     pub fn to_no_fgoh(self) -> Self {
//         match self {
//             LabeledPLTL::Top => LabeledPLTL::Top,
//             LabeledPLTL::Bottom => LabeledPLTL::Bottom,
//             LabeledPLTL::Atom(_) => self,
//             LabeledPLTL::Unary(UnaryOp::Eventually, content) => {
//                 LabeledPLTL::new_binary(BinaryOp::Until, LabeledPLTL::Top, content.to_no_fgoh())
//             }
//             LabeledPLTL::Unary(UnaryOp::Globally, box content) => LabeledPLTL::new_binary(
//                 BinaryOp::WeakUntil,
//                 content.to_no_fgoh(),
//                 LabeledPLTL::Bottom,
//             ),
//             LabeledPLTL::Unary(UnaryOp::Once, content) => {
//                 LabeledPLTL::new_binary(BinaryOp::Since, LabeledPLTL::Top, content.to_no_fgoh())
//             }
//             LabeledPLTL::Unary(UnaryOp::Historically, box content) => LabeledPLTL::new_unary(
//                 UnaryOp::Not,
//                 LabeledPLTL::new_unary(
//                     UnaryOp::Once,
//                     LabeledPLTL::new_unary(UnaryOp::Not, content.clone()),
//                 )
//                 .to_no_fgoh(),
//             ),
//             LabeledPLTL::Unary(op, content) => LabeledPLTL::new_unary(op, content.to_no_fgoh()),
//             LabeledPLTL::Binary(op, l, r) => {
//                 LabeledPLTL::new_binary(op, l.to_no_fgoh(), r.to_no_fgoh())
//             }
//             LabeledPLTL::PastSubformula(_, _) => self,
//         }
//     }

//     fn push_negation(self) -> Self {
//         match self {
//             LabeledPLTL::Top => LabeledPLTL::Bottom,
//             LabeledPLTL::Bottom => LabeledPLTL::Top,
//             LabeledPLTL::Atom(_) => LabeledPLTL::new_unary(UnaryOp::Not, self),
//             LabeledPLTL::Unary(UnaryOp::Not, box content) => content,
//             LabeledPLTL::Unary(UnaryOp::Eventually, content) => {
//                 LabeledPLTL::new_unary(UnaryOp::Globally, content.push_negation())
//             }
//             LabeledPLTL::Unary(UnaryOp::Globally, content) => {
//                 LabeledPLTL::new_unary(UnaryOp::Eventually, content.push_negation())
//             }
//             LabeledPLTL::Unary(UnaryOp::Once, content) => {
//                 LabeledPLTL::new_unary(UnaryOp::Historically, content.push_negation())
//             }
//             LabeledPLTL::Unary(UnaryOp::Historically, content) => {
//                 LabeledPLTL::new_unary(UnaryOp::Once, content.push_negation())
//             }
//             LabeledPLTL::Unary(UnaryOp::Yesterday, content) => {
//                 LabeledPLTL::new_unary(UnaryOp::WeakYesterday, content.push_negation())
//             }
//             LabeledPLTL::Unary(UnaryOp::WeakYesterday, content) => {
//                 LabeledPLTL::new_unary(UnaryOp::Yesterday, content.push_negation())
//             }
//             LabeledPLTL::Unary(UnaryOp::Next, content) => {
//                 LabeledPLTL::new_unary(UnaryOp::Next, content.push_negation())
//             }
//             LabeledPLTL::Binary(BinaryOp::And, lhs, rhs) => {
//                 LabeledPLTL::new_binary(BinaryOp::Or, lhs.push_negation(), rhs.push_negation())
//             }
//             LabeledPLTL::Binary(BinaryOp::Or, lhs, rhs) => {
//                 LabeledPLTL::new_binary(BinaryOp::And, lhs.push_negation(), rhs.push_negation())
//             }
//             LabeledPLTL::Binary(BinaryOp::Until, lhs, rhs) => {
//                 LabeledPLTL::new_binary(BinaryOp::Release, lhs.push_negation(), rhs.push_negation())
//             }
//             LabeledPLTL::Binary(BinaryOp::Release, lhs, rhs) => {
//                 LabeledPLTL::new_binary(BinaryOp::Until, lhs.push_negation(), rhs.push_negation())
//             }
//             LabeledPLTL::Binary(BinaryOp::WeakUntil, lhs, rhs) => LabeledPLTL::new_binary(
//                 BinaryOp::MightyRelease,
//                 lhs.push_negation(),
//                 rhs.push_negation(),
//             ),
//             LabeledPLTL::Binary(BinaryOp::MightyRelease, lhs, rhs) => LabeledPLTL::new_binary(
//                 BinaryOp::WeakUntil,
//                 lhs.push_negation(),
//                 rhs.push_negation(),
//             ),
//             LabeledPLTL::Binary(BinaryOp::Since, lhs, rhs) => LabeledPLTL::new_binary(
//                 BinaryOp::WeakBackTo,
//                 lhs.push_negation(),
//                 rhs.push_negation(),
//             ),
//             LabeledPLTL::Binary(BinaryOp::WeakBackTo, lhs, rhs) => {
//                 LabeledPLTL::new_binary(BinaryOp::Since, lhs.push_negation(), rhs.push_negation())
//             }
//             LabeledPLTL::Binary(BinaryOp::WeakSince, lhs, rhs) => {
//                 LabeledPLTL::new_binary(BinaryOp::BackTo, lhs.push_negation(), rhs.push_negation())
//             }
//             LabeledPLTL::Binary(BinaryOp::BackTo, lhs, rhs) => LabeledPLTL::new_binary(
//                 BinaryOp::WeakSince,
//                 lhs.push_negation(),
//                 rhs.push_negation(),
//             ),
//             LabeledPLTL::PastSubformula(_, _) => unreachable!(),
//         }
//     }

//     pub fn to_negation_normal_form(self) -> Self {
//         match self {
//             LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => self,
//             LabeledPLTL::Unary(UnaryOp::Not, box LabeledPLTL::Atom(_)) => self,
//             LabeledPLTL::Unary(UnaryOp::Not, content) => {
//                 content.push_negation().to_negation_normal_form()
//             }
//             LabeledPLTL::Unary(op, content) => {
//                 LabeledPLTL::new_unary(op, content.to_negation_normal_form())
//             }
//             LabeledPLTL::Binary(op, l, r) => LabeledPLTL::new_binary(
//                 op,
//                 l.to_negation_normal_form(),
//                 r.to_negation_normal_form(),
//             ),
//             LabeledPLTL::PastSubformula(_, _) => unreachable!(),
//         }
//     }
// }

impl LabeledPLTL {
    fn simplify_release_once(
        weak: bool,
        lhs: Box<LabeledPLTL>,
        rhs: Box<LabeledPLTL>,
    ) -> (Self, bool) {
        match (weak, lhs, rhs) {
            (false, box LabeledPLTL::Bottom, _) => (LabeledPLTL::Bottom, false),
            (true, _, box LabeledPLTL::Top) => (LabeledPLTL::Top, false),
            (_, box LabeledPLTL::Top, rhs) => (rhs.simplify(), false),
            (_, _, box LabeledPLTL::Bottom) => (LabeledPLTL::Bottom, false),
            (_, lhs, rhs) if lhs == rhs => (lhs.simplify(), false),
            (
                false,
                box LabeledPLTL::Release {
                    weak: false,
                    lhs: box llhs,
                    rhs: box lrhs,
                },
                box rhs,
            ) if lrhs == rhs => {
                let new_lhs = llhs.simplify();
                let rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (LabeledPLTL::Top, _) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (
                        LabeledPLTL::Release {
                            weak: false,
                            rhs: box lrhs,
                            ..
                        },
                        rhs,
                    ) if lrhs == rhs => true,
                    (lhs, rhs) => lhs == rhs,
                };
                (
                    LabeledPLTL::Release {
                        weak: false,
                        lhs: Box::new(new_lhs),
                        rhs: Box::new(rhs),
                    },
                    can_fold_further,
                )
            }
            (
                true,
                box lhs,
                box LabeledPLTL::Release {
                    weak: true,
                    lhs: box rlhs,
                    rhs: box rrhs,
                },
            ) if lhs == rlhs => {
                let lhs = lhs.simplify();
                let new_rhs = rrhs.simplify();
                let can_fold_further = match (&lhs, &new_rhs) {
                    (LabeledPLTL::Top, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (
                        lhs,
                        LabeledPLTL::Release {
                            weak: true,
                            lhs: box rlhs,
                            ..
                        },
                    ) if lhs == rlhs => true,
                    (lhs, rhs) => lhs == rhs,
                };
                (
                    LabeledPLTL::Release {
                        weak: true,
                        lhs: Box::new(lhs),
                        rhs: Box::new(new_rhs),
                    },
                    can_fold_further,
                )
            }
            (weak, lhs, rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (weak, &new_lhs, &new_rhs) {
                    (false, LabeledPLTL::Bottom, _) => true,
                    (true, _, LabeledPLTL::Top) => true,
                    (_, LabeledPLTL::Top, _) => true,
                    (_, _, LabeledPLTL::Bottom) => true,
                    (
                        false,
                        LabeledPLTL::Release {
                            weak: false,
                            rhs: box lrhs,
                            ..
                        },
                        rhs,
                    ) if lrhs == rhs => true,
                    (
                        true,
                        lhs,
                        LabeledPLTL::Release {
                            weak: true,
                            lhs: box rlhs,
                            ..
                        },
                    ) if lhs == rlhs => true,
                    (_, lhs, rhs) => lhs == rhs,
                };
                (
                    LabeledPLTL::Release {
                        weak,
                        lhs: Box::new(new_lhs),
                        rhs: Box::new(new_rhs),
                    },
                    can_fold_further,
                )
            }
        }
    }

    fn simplify_since_once(id: u32, lhs: Box<LabeledPLTL>, rhs: Box<LabeledPLTL>) -> (Self, bool) {
        match (lhs, rhs) {
            (_, box LabeledPLTL::Bottom) => (LabeledPLTL::Bottom, false),
            (box LabeledPLTL::Bottom, rhs) => (rhs.simplify(), false),
            (lhs, rhs) if lhs == rhs => (lhs.simplify(), false),
            (lhs, rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::BinaryTemporal {
                        id,
                        op: BinaryOp::Since,
                        weak: false,
                        lhs: Box::new(new_lhs),
                        rhs: Box::new(new_rhs),
                    },
                    can_fold_further,
                )
            }
        }
    }

    fn simplify_weak_since_once(
        id: u32,
        lhs: Box<LabeledPLTL>,
        rhs: Box<LabeledPLTL>,
    ) -> (Self, bool) {
        match (lhs, rhs) {
            (box LabeledPLTL::Bottom, rhs) => (rhs.simplify(), false),
            (box LabeledPLTL::Top, _) => (LabeledPLTL::Top, false),
            (_, box LabeledPLTL::Top) => (LabeledPLTL::Top, false),
            (lhs, rhs) if lhs == rhs => (lhs.simplify(), false),
            (lhs, rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (LabeledPLTL::Top, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::BinaryTemporal {
                        id,
                        op: BinaryOp::Since,
                        weak: true,
                        lhs: Box::new(new_lhs),
                        rhs: Box::new(new_rhs),
                    },
                    can_fold_further,
                )
            }
        }
    }

    fn simplify_back_to_once(
        id: u32,
        lhs: Box<LabeledPLTL>,
        rhs: Box<LabeledPLTL>,
    ) -> (Self, bool) {
        match (lhs, rhs) {
            (box LabeledPLTL::Bottom, _) => (LabeledPLTL::Bottom, false),
            (_, box LabeledPLTL::Bottom) => (LabeledPLTL::Bottom, false),
            (box LabeledPLTL::Top, rhs) => (rhs.simplify(), false),
            (lhs, rhs) if lhs == rhs => (lhs.simplify(), false),
            (lhs, rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (LabeledPLTL::Top, _) => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::BinaryTemporal {
                        id,
                        op: BinaryOp::BackTo,
                        weak: false,
                        lhs: Box::new(new_lhs),
                        rhs: Box::new(new_rhs),
                    },
                    can_fold_further,
                )
            }
        }
    }

    fn simplify_weak_back_to_once(
        id: u32,
        lhs: Box<LabeledPLTL>,
        rhs: Box<LabeledPLTL>,
    ) -> (Self, bool) {
        match (lhs, rhs) {
            (_, box LabeledPLTL::Bottom) => (LabeledPLTL::Bottom, false),
            (_, box LabeledPLTL::Top) => (LabeledPLTL::Top, false),
            (box LabeledPLTL::Top, rhs) => (rhs.simplify(), false),
            (lhs, rhs) if lhs == rhs => (lhs.simplify(), false),
            (lhs, rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (_, LabeledPLTL::Bottom) => true,
                    (_, LabeledPLTL::Top) => true,
                    (LabeledPLTL::Top, _) => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::BinaryTemporal {
                        id,
                        op: BinaryOp::BackTo,
                        weak: true,
                        lhs: Box::new(new_lhs),
                        rhs: Box::new(new_rhs),
                    },
                    can_fold_further,
                )
            }
        }
    }

    fn simplify_once(self) -> (Self, bool) {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) | LabeledPLTL::Not(_) => {
                (self, false)
            }
            LabeledPLTL::Yesterday {
                id,
                weak: false,
                content,
            } => {
                if content.as_ref() == &LabeledPLTL::Bottom {
                    (LabeledPLTL::Bottom, false)
                } else if let LabeledPLTL::Next(box inner_content) = *content {
                    inner_content.simplify_once()
                } else {
                    let (simplified, may_go_to_other_branch) = content.simplify_once();
                    (
                        LabeledPLTL::Yesterday {
                            id,
                            weak: false,
                            content: Box::new(simplified),
                        },
                        may_go_to_other_branch,
                    )
                }
            }
            LabeledPLTL::Yesterday {
                id,
                weak: true,
                content,
            } => {
                if content.as_ref() == &LabeledPLTL::Top {
                    (LabeledPLTL::Top, false)
                } else {
                    let (simplified, may_go_to_other_branch) = content.simplify_once();
                    (
                        LabeledPLTL::Yesterday {
                            id,
                            weak: true,
                            content: Box::new(simplified),
                        },
                        may_go_to_other_branch,
                    )
                }
            }
            LabeledPLTL::Next(box LabeledPLTL::Top) => (LabeledPLTL::Top, false),
            LabeledPLTL::Next(box LabeledPLTL::Bottom) => (LabeledPLTL::Bottom, false),
            LabeledPLTL::Next(box LabeledPLTL::Yesterday {
                weak: false,
                content,
                ..
            }) => content.simplify_once(),
            LabeledPLTL::Next(content) => {
                let (simplified, may_go_to_other_branch) = content.simplify_once();
                let may_go_to_other_branch = may_go_to_other_branch
                    || matches!(
                        simplified,
                        LabeledPLTL::Bottom
                            | LabeledPLTL::Top
                            | LabeledPLTL::Yesterday { weak: false, .. }
                    );
                (
                    LabeledPLTL::Next(Box::new(simplified)),
                    may_go_to_other_branch,
                )
            }
            LabeledPLTL::Until {
                lhs: box LabeledPLTL::Bottom,
                rhs,
                ..
            } => (rhs.simplify(), false),
            LabeledPLTL::Until {
                rhs: box LabeledPLTL::Top,
                ..
            } => (LabeledPLTL::Top, false),
            LabeledPLTL::Until { lhs, rhs, .. } if lhs == rhs => (lhs.simplify(), false),
            LabeledPLTL::Until {
                weak: false,
                rhs: box LabeledPLTL::Bottom,
                ..
            } => (LabeledPLTL::Bottom, false),
            LabeledPLTL::Until {
                weak: true,
                lhs: box LabeledPLTL::Top,
                ..
            } => (LabeledPLTL::Top, false),
            LabeledPLTL::Until {
                weak: false,
                lhs,
                rhs:
                    box LabeledPLTL::Until {
                        weak: false,
                        lhs: rlhs,
                        rhs: rrhs,
                    },
            } if lhs == rlhs => {
                let lhs = lhs.simplify();
                let new_rhs = rrhs.simplify();
                let can_fold_further = match (&lhs, &new_rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (
                        lhs,
                        LabeledPLTL::Until {
                            weak: false,
                            lhs: box rlhs,
                            ..
                        },
                    ) if lhs == rlhs => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::Until {
                        weak: false,
                        lhs: Box::new(lhs),
                        rhs: Box::new(new_rhs),
                    },
                    can_fold_further,
                )
            }
            LabeledPLTL::Until {
                weak: true,
                lhs:
                    box LabeledPLTL::Until {
                        weak: true,
                        lhs: llhs,
                        rhs: lrhs,
                    },
                rhs,
            } if lrhs == rhs => {
                let new_lhs = llhs.simplify();
                let rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (LabeledPLTL::Top, _) => true,
                    (
                        LabeledPLTL::Until {
                            weak: true,
                            rhs: box lrhs,
                            ..
                        },
                        rhs,
                    ) if lrhs == rhs => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::Until {
                        weak: true,
                        lhs: Box::new(new_lhs),
                        rhs: Box::new(rhs),
                    },
                    can_fold_further,
                )
            }
            LabeledPLTL::Until { weak, lhs, rhs } => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (weak, &new_lhs, &new_rhs) {
                    (_, LabeledPLTL::Bottom, _) => true,
                    (_, _, LabeledPLTL::Top) => true,
                    (false, _, LabeledPLTL::Bottom) => true,
                    (true, LabeledPLTL::Top, _) => true,
                    (
                        false,
                        lhs,
                        LabeledPLTL::Until {
                            weak: false,
                            lhs: box rlhs,
                            ..
                        },
                    ) if lhs == rlhs => true,
                    (
                        true,
                        LabeledPLTL::Until {
                            weak: true,
                            rhs: box lrhs,
                            ..
                        },
                        rhs,
                    ) if lrhs == rhs => true,
                    (_, new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::Until {
                        weak,
                        lhs: Box::new(new_lhs),
                        rhs: Box::new(new_rhs),
                    },
                    can_fold_further,
                )
            }
            LabeledPLTL::Release { weak, lhs, rhs } => Self::simplify_release_once(weak, lhs, rhs),
            LabeledPLTL::BinaryTemporal {
                id,
                op,
                weak,
                lhs,
                rhs,
            } => match (op, weak) {
                (BinaryOp::Since, false) => Self::simplify_since_once(id, lhs, rhs),
                (BinaryOp::Since, true) => Self::simplify_weak_since_once(id, lhs, rhs),
                (BinaryOp::BackTo, false) => Self::simplify_back_to_once(id, lhs, rhs),
                (BinaryOp::BackTo, true) => Self::simplify_weak_back_to_once(id, lhs, rhs),
                _ => unreachable!("only since and back_to should reach here"),
            },
            LabeledPLTL::Logical(BinaryOp::And, content) => {
                let mut result = Vec::with_capacity(content.len());
                for item in content {
                    let mut simplified = item.simplify();
                    if simplified == LabeledPLTL::Bottom {
                        return (LabeledPLTL::Bottom, false);
                    } else if let LabeledPLTL::Logical(inner_op, inner_content) = &mut simplified
                        && inner_op == &BinaryOp::And
                    {
                        result.extend(mem::take(inner_content));
                    } else if simplified != LabeledPLTL::Top {
                        result.push(simplified);
                    }
                }
                if result.is_empty() {
                    (LabeledPLTL::Top, false)
                } else if result.len() == 1 {
                    return (result.pop().unwrap(), false);
                } else {
                    result.sort();
                    result.dedup();
                    (LabeledPLTL::Logical(BinaryOp::And, result), false)
                }
            }
            LabeledPLTL::Logical(BinaryOp::Or, content) => {
                let mut result = Vec::with_capacity(content.len());
                for item in content {
                    let mut simplified = item.simplify();
                    if simplified == LabeledPLTL::Top {
                        return (LabeledPLTL::Top, false);
                    } else if let LabeledPLTL::Logical(inner_op, inner_content) = &mut simplified
                        && inner_op == &BinaryOp::Or
                    {
                        result.extend(mem::take(inner_content));
                    } else if simplified != LabeledPLTL::Bottom {
                        result.push(simplified);
                    }
                }
                if result.is_empty() {
                    (LabeledPLTL::Bottom, false)
                } else if result.len() == 1 {
                    return (result.pop().unwrap(), false);
                } else {
                    result.sort();
                    result.dedup();
                    (LabeledPLTL::Logical(BinaryOp::Or, result), false)
                }
            }
            LabeledPLTL::Logical(op, _) => {
                unreachable!("only `and` and `or` should reach here, found {op}");
            }
        }
    }

    pub fn simplify(self) -> Self {
        let mut result = self;
        for _ in 0..65536 {
            let (new_result, may_go_to_other_branch) = result.simplify_once();
            if !may_go_to_other_branch {
                return new_result;
            }
            result = new_result;
        }
        #[cfg(debug_assertions)]
        panic!("Simplification failed: {}", result);
        #[cfg(not(debug_assertions))]
        result
    }
}
