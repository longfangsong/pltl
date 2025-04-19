use std::mem;

use smallvec::SmallVec;

use crate::pltl::{BinaryOp, UnaryOp};

use super::LabeledPLTL;

impl LabeledPLTL {
    pub fn to_no_fgoh(self) -> Self {
        match self {
            LabeledPLTL::Top => LabeledPLTL::Top,
            LabeledPLTL::Bottom => LabeledPLTL::Bottom,
            LabeledPLTL::Atom(_) => self,
            LabeledPLTL::Unary(UnaryOp::Eventually, content) => {
                LabeledPLTL::new_binary(BinaryOp::Until, LabeledPLTL::Top, content.to_no_fgoh())
            }
            LabeledPLTL::Unary(UnaryOp::Globally, box content) => LabeledPLTL::new_binary(
                BinaryOp::WeakUntil,
                content.to_no_fgoh(),
                LabeledPLTL::Bottom,
            ),
            LabeledPLTL::Unary(UnaryOp::Once, content) => {
                LabeledPLTL::new_binary(BinaryOp::Since, LabeledPLTL::Top, content.to_no_fgoh())
            }
            LabeledPLTL::Unary(UnaryOp::Historically, box content) => LabeledPLTL::new_unary(
                UnaryOp::Not,
                LabeledPLTL::new_unary(
                    UnaryOp::Once,
                    LabeledPLTL::new_unary(UnaryOp::Not, content.clone()),
                )
                .to_no_fgoh(),
            ),
            LabeledPLTL::Unary(op, content) => LabeledPLTL::new_unary(op, content.to_no_fgoh()),
            LabeledPLTL::Binary(op, l, r) => {
                LabeledPLTL::new_binary(op, l.to_no_fgoh(), r.to_no_fgoh())
            }
            LabeledPLTL::PastSubformula(_, _) => self,
        }
    }

    fn push_negation(self) -> Self {
        match self {
            LabeledPLTL::Top => LabeledPLTL::Bottom,
            LabeledPLTL::Bottom => LabeledPLTL::Top,
            LabeledPLTL::Atom(_) => LabeledPLTL::new_unary(UnaryOp::Not, self),
            LabeledPLTL::Unary(UnaryOp::Not, box content) => content,
            LabeledPLTL::Unary(UnaryOp::Eventually, content) => {
                LabeledPLTL::new_unary(UnaryOp::Globally, content.push_negation())
            }
            LabeledPLTL::Unary(UnaryOp::Globally, content) => {
                LabeledPLTL::new_unary(UnaryOp::Eventually, content.push_negation())
            }
            LabeledPLTL::Unary(UnaryOp::Once, content) => {
                LabeledPLTL::new_unary(UnaryOp::Historically, content.push_negation())
            }
            LabeledPLTL::Unary(UnaryOp::Historically, content) => {
                LabeledPLTL::new_unary(UnaryOp::Once, content.push_negation())
            }
            LabeledPLTL::Unary(UnaryOp::Yesterday, content) => {
                LabeledPLTL::new_unary(UnaryOp::WeakYesterday, content.push_negation())
            }
            LabeledPLTL::Unary(UnaryOp::WeakYesterday, content) => {
                LabeledPLTL::new_unary(UnaryOp::Yesterday, content.push_negation())
            }
            LabeledPLTL::Unary(UnaryOp::Next, content) => {
                LabeledPLTL::new_unary(UnaryOp::Next, content.push_negation())
            }
            LabeledPLTL::Binary(BinaryOp::And, lhs, rhs) => {
                LabeledPLTL::new_binary(BinaryOp::Or, lhs.push_negation(), rhs.push_negation())
            }
            LabeledPLTL::Binary(BinaryOp::Or, lhs, rhs) => {
                LabeledPLTL::new_binary(BinaryOp::And, lhs.push_negation(), rhs.push_negation())
            }
            LabeledPLTL::Binary(BinaryOp::Until, lhs, rhs) => {
                LabeledPLTL::new_binary(BinaryOp::Release, lhs.push_negation(), rhs.push_negation())
            }
            LabeledPLTL::Binary(BinaryOp::Release, lhs, rhs) => {
                LabeledPLTL::new_binary(BinaryOp::Until, lhs.push_negation(), rhs.push_negation())
            }
            LabeledPLTL::Binary(BinaryOp::WeakUntil, lhs, rhs) => LabeledPLTL::new_binary(
                BinaryOp::MightyRelease,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
            LabeledPLTL::Binary(BinaryOp::MightyRelease, lhs, rhs) => LabeledPLTL::new_binary(
                BinaryOp::WeakUntil,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
            LabeledPLTL::Binary(BinaryOp::Since, lhs, rhs) => LabeledPLTL::new_binary(
                BinaryOp::WeakBackTo,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
            LabeledPLTL::Binary(BinaryOp::WeakBackTo, lhs, rhs) => {
                LabeledPLTL::new_binary(BinaryOp::Since, lhs.push_negation(), rhs.push_negation())
            }
            LabeledPLTL::Binary(BinaryOp::WeakSince, lhs, rhs) => {
                LabeledPLTL::new_binary(BinaryOp::BackTo, lhs.push_negation(), rhs.push_negation())
            }
            LabeledPLTL::Binary(BinaryOp::BackTo, lhs, rhs) => LabeledPLTL::new_binary(
                BinaryOp::WeakSince,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
            LabeledPLTL::PastSubformula(_, _) => unreachable!(),
        }
    }

    pub fn to_negation_normal_form(self) -> Self {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => self,
            LabeledPLTL::Unary(UnaryOp::Not, box LabeledPLTL::Atom(_)) => self,
            LabeledPLTL::Unary(UnaryOp::Not, content) => {
                content.push_negation().to_negation_normal_form()
            }
            LabeledPLTL::Unary(op, content) => {
                LabeledPLTL::new_unary(op, content.to_negation_normal_form())
            }
            LabeledPLTL::Binary(op, l, r) => LabeledPLTL::new_binary(
                op,
                l.to_negation_normal_form(),
                r.to_negation_normal_form(),
            ),
            LabeledPLTL::PastSubformula(_, _) => unreachable!(),
        }
    }
}

impl LabeledPLTL {
    fn collect_commutative(self, op: BinaryOp, result: &mut SmallVec<[Self; 8]>) {
        match self {
            LabeledPLTL::Binary(self_op, box lhs, box rhs) if op == self_op => {
                lhs.collect_commutative(op, result);
                rhs.collect_commutative(op, result);
            }
            _ => result.push(self),
        }
    }

    // return: (result, may_go_to_other_branch)
    fn simplify_once(self) -> (Self, bool) {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => (self, false),
            LabeledPLTL::Unary(UnaryOp::Not, box LabeledPLTL::Bottom) => (LabeledPLTL::Top, false),
            LabeledPLTL::Unary(UnaryOp::Not, box LabeledPLTL::Top) => (LabeledPLTL::Bottom, false),
            LabeledPLTL::Unary(UnaryOp::Not, box LabeledPLTL::Unary(UnaryOp::Not, box pltl)) => {
                (pltl.simplify(), false)
            }

            LabeledPLTL::Unary(UnaryOp::Next, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Unary(UnaryOp::Next, box LabeledPLTL::Top) => (LabeledPLTL::Top, false),
            LabeledPLTL::Unary(
                UnaryOp::Next,
                box LabeledPLTL::Unary(UnaryOp::Yesterday, content),
            ) => (content.simplify(), false),
            LabeledPLTL::Unary(UnaryOp::Next, content) => {
                let content_simplified = content.simplify();
                let may_go_to_other_branch = matches!(
                    &content_simplified,
                    LabeledPLTL::Bottom
                        | LabeledPLTL::Top
                        | LabeledPLTL::Unary(UnaryOp::Yesterday, _)
                );
                (
                    LabeledPLTL::new_unary(UnaryOp::Next, content_simplified),
                    may_go_to_other_branch,
                )
            }

            LabeledPLTL::Unary(UnaryOp::Yesterday, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Unary(UnaryOp::Yesterday, content) => {
                let content_simplified = content.simplify();
                let may_go_to_other_branch = content_simplified == LabeledPLTL::Bottom;
                (
                    LabeledPLTL::new_unary(UnaryOp::Yesterday, content_simplified),
                    may_go_to_other_branch,
                )
            }
            LabeledPLTL::Unary(UnaryOp::WeakYesterday, box LabeledPLTL::Top) => {
                (LabeledPLTL::Top, false)
            }
            LabeledPLTL::Unary(UnaryOp::WeakYesterday, content) => {
                let content_simplified = content.simplify();
                let may_go_to_other_branch = content_simplified == LabeledPLTL::Top;
                (
                    LabeledPLTL::new_unary(UnaryOp::WeakYesterday, content_simplified),
                    may_go_to_other_branch,
                )
            }
            LabeledPLTL::Unary(op, content) => {
                let content_simplified = content.simplify();
                let may_go_to_other_branch = op == UnaryOp::Not
                    && matches!(
                        &content_simplified,
                        LabeledPLTL::Bottom
                            | LabeledPLTL::Top
                            | LabeledPLTL::Unary(UnaryOp::Not, _)
                    );
                (
                    LabeledPLTL::new_unary(op, content_simplified),
                    may_go_to_other_branch,
                )
            }

            LabeledPLTL::Binary(BinaryOp::And, box LabeledPLTL::Bottom, _) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::And, _, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::And, box LabeledPLTL::Top, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::And, box lhs, box LabeledPLTL::Top) => {
                (lhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::And, _, _) => {
                let mut pendings = SmallVec::new();
                let mut result = SmallVec::<[LabeledPLTL; 8]>::new();
                self.collect_commutative(BinaryOp::And, &mut pendings);
                while !pendings.is_empty() {
                    for pending in mem::take(&mut pendings) {
                        let simplified = pending.simplify();
                        match simplified {
                            LabeledPLTL::Bottom => return (LabeledPLTL::Bottom, true),
                            LabeledPLTL::Binary(BinaryOp::And, _, _) => {
                                simplified.collect_commutative(BinaryOp::And, &mut pendings);
                            }
                            atom @ LabeledPLTL::Atom(_) => {
                                if result
                                    .contains(&LabeledPLTL::new_unary(UnaryOp::Not, atom.clone()))
                                {
                                    return (LabeledPLTL::Bottom, false);
                                } else {
                                    result.push(atom)
                                }
                            }
                            LabeledPLTL::Unary(UnaryOp::Not, box atom @ LabeledPLTL::Atom(_)) => {
                                if result.contains(&atom) {
                                    return (LabeledPLTL::Bottom, false);
                                } else {
                                    result.push(LabeledPLTL::new_unary(UnaryOp::Not, atom))
                                }
                            }
                            _ => result.push(simplified),
                        }
                    }
                }
                result.sort();
                result.dedup();
                let first_is_top = if result.first() == Some(&LabeledPLTL::Top) {
                    1
                } else {
                    0
                };
                let result = result
                    .into_iter()
                    .skip(first_is_top)
                    .reduce(|acc, x| acc & x)
                    .unwrap_or(LabeledPLTL::Top);
                let may_go_to_other_branch = !matches!(
                    result,
                    LabeledPLTL::Binary(BinaryOp::And, _, _) | LabeledPLTL::Top
                );
                (result, may_go_to_other_branch)
            }

            LabeledPLTL::Binary(BinaryOp::Or, box LabeledPLTL::Top, _) => (LabeledPLTL::Top, false),
            LabeledPLTL::Binary(BinaryOp::Or, _, box LabeledPLTL::Top) => (LabeledPLTL::Top, false),
            LabeledPLTL::Binary(BinaryOp::Or, box LabeledPLTL::Bottom, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::Or, box lhs, box LabeledPLTL::Bottom) => {
                (lhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::Or, _, _) => {
                let mut pendings = SmallVec::new();
                let mut result = SmallVec::<[LabeledPLTL; 8]>::new();

                self.collect_commutative(BinaryOp::Or, &mut pendings);
                while !pendings.is_empty() {
                    for pending in mem::take(&mut pendings) {
                        let simplified = pending.simplify();
                        match simplified {
                            LabeledPLTL::Top => return (LabeledPLTL::Top, false),
                            LabeledPLTL::Binary(BinaryOp::Or, _, _) => {
                                simplified.collect_commutative(BinaryOp::Or, &mut pendings);
                            }
                            atom @ LabeledPLTL::Atom(_) => {
                                if result
                                    .contains(&LabeledPLTL::new_unary(UnaryOp::Not, atom.clone()))
                                {
                                    return (LabeledPLTL::Top, false);
                                } else {
                                    result.push(atom)
                                }
                            }
                            LabeledPLTL::Unary(UnaryOp::Not, box atom @ LabeledPLTL::Atom(_)) => {
                                if result.contains(&atom) {
                                    return (LabeledPLTL::Top, false);
                                } else {
                                    result.push(LabeledPLTL::new_unary(UnaryOp::Not, atom))
                                }
                            }
                            _ => result.push(simplified),
                        }
                    }
                }

                result.sort();
                result.dedup();
                let first_is_bottom = if result.first() == Some(&LabeledPLTL::Bottom) {
                    1
                } else {
                    0
                };
                let result = result
                    .into_iter()
                    .skip(first_is_bottom)
                    .reduce(|acc, x| acc | x)
                    .unwrap_or(LabeledPLTL::Bottom);
                let may_go_to_other_branch = !matches!(
                    result,
                    LabeledPLTL::Binary(BinaryOp::Or, _, _) | LabeledPLTL::Bottom
                );
                (result, may_go_to_other_branch)
            }

            LabeledPLTL::Binary(BinaryOp::Until, box LabeledPLTL::Bottom, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::Until, _, box LabeledPLTL::Top) => {
                (LabeledPLTL::Top, false)
            }
            LabeledPLTL::Binary(BinaryOp::Until, _, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::Until, box lhs, box rhs) if lhs == rhs => {
                (lhs.simplify(), false)
            }
            LabeledPLTL::Binary(
                BinaryOp::Until,
                box lhs,
                box LabeledPLTL::Binary(BinaryOp::Until, box rlhs, box rrhs),
            ) if lhs == rlhs => {
                let lhs = lhs.simplify();
                let new_rhs = rrhs.simplify();
                let can_fold_further = match (&lhs, &new_rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (lhs, LabeledPLTL::Binary(BinaryOp::Until, box rlhs, box rrhs))
                        if lhs == rlhs =>
                    {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::new_binary(BinaryOp::Until, lhs, new_rhs),
                    can_fold_further,
                )
            }
            LabeledPLTL::Binary(BinaryOp::Until, box lhs, box rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (new_lhs, LabeledPLTL::Binary(BinaryOp::Until, box rlhs, _))
                        if new_lhs == rlhs =>
                    {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::new_binary(BinaryOp::Until, new_lhs, new_rhs),
                    can_fold_further,
                )
            }

            LabeledPLTL::Binary(BinaryOp::Release, box LabeledPLTL::Top, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::Release, _, box LabeledPLTL::Top) => {
                (LabeledPLTL::Top, false)
            }
            LabeledPLTL::Binary(BinaryOp::Release, _, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::Release, box lhs, box rhs) if lhs == rhs => {
                (lhs.simplify(), false)
            }
            LabeledPLTL::Binary(
                BinaryOp::Release,
                box lhs,
                box LabeledPLTL::Binary(BinaryOp::Release, box rlhs, box rrhs),
            ) if lhs == rlhs => {
                let lhs = lhs.simplify();
                let new_rhs = rrhs.simplify();
                let can_fold_further = match (&lhs, &new_rhs) {
                    (LabeledPLTL::Top, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (lhs, LabeledPLTL::Binary(BinaryOp::Release, box rlhs, _)) if lhs == rlhs => {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::new_binary(BinaryOp::Release, lhs, new_rhs),
                    can_fold_further,
                )
            }
            LabeledPLTL::Binary(BinaryOp::Release, box lhs, box rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (LabeledPLTL::Top, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (lhs, LabeledPLTL::Binary(BinaryOp::Release, box rlhs, _)) if lhs == rlhs => {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::new_binary(BinaryOp::Release, new_lhs, new_rhs),
                    can_fold_further,
                )
            }

            LabeledPLTL::Binary(BinaryOp::WeakUntil, box LabeledPLTL::Top, _) => {
                (LabeledPLTL::Top, false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakUntil, box LabeledPLTL::Bottom, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakUntil, _, box LabeledPLTL::Top) => {
                (LabeledPLTL::Top, false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakUntil, box lhs, box rhs) if lhs == rhs => {
                (lhs.simplify(), false)
            }
            LabeledPLTL::Binary(
                BinaryOp::WeakUntil,
                box LabeledPLTL::Binary(BinaryOp::WeakUntil, box llhs, box lrhs),
                box rhs,
            ) if lrhs == rhs => {
                let new_lhs = llhs.simplify();
                let rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &rhs) {
                    (LabeledPLTL::Top, _) => true,
                    (LabeledPLTL::Bottom, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (LabeledPLTL::Binary(BinaryOp::WeakUntil, _, box lrhs), rhs) if lrhs == rhs => {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::new_binary(BinaryOp::WeakUntil, new_lhs, rhs),
                    can_fold_further,
                )
            }
            LabeledPLTL::Binary(BinaryOp::WeakUntil, box lhs, box rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (LabeledPLTL::Top, _) => true,
                    (LabeledPLTL::Bottom, _) => true,
                    (_, LabeledPLTL::Top) => true,
                    (LabeledPLTL::Binary(BinaryOp::WeakUntil, _, box lrhs), new_rhs)
                        if lrhs == new_rhs =>
                    {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::new_binary(BinaryOp::WeakUntil, new_lhs, new_rhs),
                    can_fold_further,
                )
            }

            LabeledPLTL::Binary(BinaryOp::MightyRelease, box LabeledPLTL::Bottom, _) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::MightyRelease, box LabeledPLTL::Top, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::MightyRelease, _, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::MightyRelease, box lhs, box rhs) if lhs == rhs => {
                (lhs.simplify(), false)
            }
            LabeledPLTL::Binary(
                BinaryOp::MightyRelease,
                box LabeledPLTL::Binary(BinaryOp::MightyRelease, box llhs, box lrhs),
                box rhs,
            ) if lrhs == rhs => {
                let new_lhs = llhs.simplify();
                let rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (LabeledPLTL::Top, _) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (LabeledPLTL::Binary(BinaryOp::MightyRelease, _, box lrhs), rhs)
                        if lrhs == rhs =>
                    {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::new_binary(BinaryOp::MightyRelease, new_lhs, rhs),
                    can_fold_further,
                )
            }
            LabeledPLTL::Binary(BinaryOp::MightyRelease, box lhs, box rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (LabeledPLTL::Bottom, _) => true,
                    (LabeledPLTL::Top, _) => true,
                    (_, LabeledPLTL::Bottom) => true,
                    (LabeledPLTL::Binary(BinaryOp::MightyRelease, _, box lrhs), new_rhs)
                        if lrhs == new_rhs =>
                    {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    LabeledPLTL::new_binary(BinaryOp::MightyRelease, new_lhs, new_rhs),
                    can_fold_further,
                )
            }

            LabeledPLTL::Binary(BinaryOp::Since, _, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::Since, box LabeledPLTL::Bottom, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::Since, box lhs, box rhs) => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if lhs == rhs {
                    (lhs, false)
                } else {
                    let can_fold_further = lhs == LabeledPLTL::Bottom || rhs == LabeledPLTL::Bottom;
                    (
                        LabeledPLTL::new_binary(BinaryOp::Since, lhs, rhs),
                        can_fold_further,
                    )
                }
            }

            LabeledPLTL::Binary(BinaryOp::WeakSince, box LabeledPLTL::Bottom, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakSince, box LabeledPLTL::Top, _) => {
                (LabeledPLTL::Top, false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakSince, _, box LabeledPLTL::Top) => {
                (LabeledPLTL::Top, false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakSince, box lhs, box rhs) => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if lhs == rhs {
                    (lhs.simplify(), false)
                } else {
                    let can_fold_further = lhs == LabeledPLTL::Bottom
                        || lhs == LabeledPLTL::Top
                        || rhs == LabeledPLTL::Top;
                    (
                        LabeledPLTL::new_binary(BinaryOp::WeakSince, lhs, rhs),
                        can_fold_further,
                    )
                }
            }

            LabeledPLTL::Binary(BinaryOp::BackTo, box LabeledPLTL::Bottom, _) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::BackTo, _, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::BackTo, box LabeledPLTL::Top, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::BackTo, box lhs, box rhs) => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if lhs == rhs {
                    (lhs.simplify(), false)
                } else {
                    let can_fold_further = lhs == LabeledPLTL::Bottom
                        || lhs == LabeledPLTL::Top
                        || rhs == LabeledPLTL::Bottom;
                    (
                        LabeledPLTL::new_binary(BinaryOp::BackTo, lhs, rhs),
                        can_fold_further,
                    )
                }
            }

            LabeledPLTL::Binary(BinaryOp::WeakBackTo, box LabeledPLTL::Top, box rhs) => {
                (rhs.simplify(), false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakBackTo, _, box LabeledPLTL::Top) => {
                (LabeledPLTL::Top, false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakBackTo, _, box LabeledPLTL::Bottom) => {
                (LabeledPLTL::Bottom, false)
            }
            LabeledPLTL::Binary(BinaryOp::WeakBackTo, box lhs, box rhs) => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if lhs == rhs {
                    (lhs.simplify(), false)
                } else {
                    let can_fold_further = lhs == LabeledPLTL::Top
                        || rhs == LabeledPLTL::Top
                        || rhs == LabeledPLTL::Bottom;
                    (
                        LabeledPLTL::new_binary(BinaryOp::WeakBackTo, lhs, rhs),
                        can_fold_further,
                    )
                }
            }
            LabeledPLTL::PastSubformula(psf, state) => {
                (LabeledPLTL::PastSubformula(psf, state), false)
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
        println!("Simplification failed: {}", todo!());
        #[cfg(not(debug_assertions))]
        result
    }
}
