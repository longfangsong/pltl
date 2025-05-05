use std::mem;

use smallvec::SmallVec;

use super::{BinaryOp, UnaryOp, PLTL};

impl PLTL {
    pub fn to_no_fgoh(self) -> Self {
        match self {
            PLTL::Top => PLTL::Top,
            PLTL::Bottom => PLTL::Bottom,
            PLTL::Atom(_) => self,
            PLTL::Unary(UnaryOp::Eventually, content) => {
                PLTL::new_binary(BinaryOp::Until, PLTL::Top, content.to_no_fgoh())
            }
            PLTL::Unary(UnaryOp::Globally, box content) => {
                PLTL::new_binary(BinaryOp::WeakUntil, content.to_no_fgoh(), PLTL::Bottom)
            }
            PLTL::Unary(UnaryOp::Once, content) => {
                PLTL::new_binary(BinaryOp::Since, PLTL::Top, content.to_no_fgoh())
            }
            PLTL::Unary(UnaryOp::Historically, box content) => PLTL::new_unary(
                UnaryOp::Not,
                PLTL::new_unary(
                    UnaryOp::Once,
                    PLTL::new_unary(UnaryOp::Not, content.clone()),
                )
                .to_no_fgoh(),
            ),
            PLTL::Unary(op, content) => PLTL::new_unary(op, content.to_no_fgoh()),
            PLTL::Binary(op, l, r) => PLTL::new_binary(op, l.to_no_fgoh(), r.to_no_fgoh()),
        }
    }

    fn push_negation(self) -> Self {
        match self {
            PLTL::Top => PLTL::Bottom,
            PLTL::Bottom => PLTL::Top,
            PLTL::Atom(_) => PLTL::new_unary(UnaryOp::Not, self),
            PLTL::Unary(UnaryOp::Not, box content) => content,
            PLTL::Unary(UnaryOp::Eventually, content) => {
                PLTL::new_unary(UnaryOp::Globally, content.push_negation())
            }
            PLTL::Unary(UnaryOp::Globally, content) => {
                PLTL::new_unary(UnaryOp::Eventually, content.push_negation())
            }
            PLTL::Unary(UnaryOp::Once, content) => {
                PLTL::new_unary(UnaryOp::Historically, content.push_negation())
            }
            PLTL::Unary(UnaryOp::Historically, content) => {
                PLTL::new_unary(UnaryOp::Once, content.push_negation())
            }
            PLTL::Unary(UnaryOp::Yesterday, content) => {
                PLTL::new_unary(UnaryOp::WeakYesterday, content.push_negation())
            }
            PLTL::Unary(UnaryOp::WeakYesterday, content) => {
                PLTL::new_unary(UnaryOp::Yesterday, content.push_negation())
            }
            PLTL::Unary(UnaryOp::Next, content) => {
                PLTL::new_unary(UnaryOp::Next, content.push_negation())
            }
            PLTL::Binary(BinaryOp::And, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::Or, lhs.push_negation(), rhs.push_negation())
            }
            PLTL::Binary(BinaryOp::Or, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::And, lhs.push_negation(), rhs.push_negation())
            }
            PLTL::Binary(BinaryOp::Until, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::Release, lhs.push_negation(), rhs.push_negation())
            }
            PLTL::Binary(BinaryOp::Release, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::Until, lhs.push_negation(), rhs.push_negation())
            }
            PLTL::Binary(BinaryOp::WeakUntil, lhs, rhs) => PLTL::new_binary(
                BinaryOp::MightyRelease,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
            PLTL::Binary(BinaryOp::MightyRelease, lhs, rhs) => PLTL::new_binary(
                BinaryOp::WeakUntil,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
            PLTL::Binary(BinaryOp::Since, lhs, rhs) => PLTL::new_binary(
                BinaryOp::WeakBackTo,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
            PLTL::Binary(BinaryOp::WeakBackTo, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::Since, lhs.push_negation(), rhs.push_negation())
            }
            PLTL::Binary(BinaryOp::WeakSince, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::BackTo, lhs.push_negation(), rhs.push_negation())
            }
            PLTL::Binary(BinaryOp::BackTo, lhs, rhs) => PLTL::new_binary(
                BinaryOp::WeakSince,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
        }
    }

    pub fn to_negation_normal_form(self) -> Self {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => self,
            PLTL::Unary(UnaryOp::Not, box PLTL::Atom(_)) => self,
            PLTL::Unary(UnaryOp::Not, content) => content.push_negation().to_negation_normal_form(),
            PLTL::Unary(op, content) => PLTL::new_unary(op, content.to_negation_normal_form()),
            PLTL::Binary(op, l, r) => {
                PLTL::new_binary(op, l.to_negation_normal_form(), r.to_negation_normal_form())
            }
        }
    }
}

impl PLTL {
    fn collect_commutative(self, op: BinaryOp, result: &mut SmallVec<[Self; 8]>) {
        match self {
            PLTL::Binary(self_op, box lhs, box rhs) if op == self_op => {
                lhs.collect_commutative(op, result);
                rhs.collect_commutative(op, result);
            }
            _ => result.push(self),
        }
    }

    // return: (result, may_go_to_other_branch)
    fn simplify_once(self) -> (Self, bool) {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => (self, false),
            PLTL::Unary(UnaryOp::Not, box PLTL::Bottom) => (PLTL::Top, false),
            PLTL::Unary(UnaryOp::Not, box PLTL::Top) => (PLTL::Bottom, false),
            PLTL::Unary(UnaryOp::Not, box PLTL::Unary(UnaryOp::Not, box pltl)) => {
                (pltl.simplify(), false)
            }

            PLTL::Unary(UnaryOp::Next, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Unary(UnaryOp::Next, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Unary(UnaryOp::Next, box PLTL::Unary(UnaryOp::Yesterday, content)) => {
                (content.simplify(), false)
            }
            PLTL::Unary(UnaryOp::Next, content) => {
                let content_simplified = content.simplify();
                let may_go_to_other_branch = matches!(
                    &content_simplified,
                    PLTL::Bottom | PLTL::Top | PLTL::Unary(UnaryOp::Yesterday, _)
                );
                (
                    PLTL::new_unary(UnaryOp::Next, content_simplified),
                    may_go_to_other_branch,
                )
            }

            PLTL::Unary(UnaryOp::Yesterday, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Unary(UnaryOp::Yesterday, content) => {
                let content_simplified = content.simplify();
                let may_go_to_other_branch = content_simplified == PLTL::Bottom;
                (
                    PLTL::new_unary(UnaryOp::Yesterday, content_simplified),
                    may_go_to_other_branch,
                )
            }
            PLTL::Unary(UnaryOp::WeakYesterday, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Unary(UnaryOp::WeakYesterday, content) => {
                let content_simplified = content.simplify();
                let may_go_to_other_branch = content_simplified == PLTL::Top;
                (
                    PLTL::new_unary(UnaryOp::WeakYesterday, content_simplified),
                    may_go_to_other_branch,
                )
            }
            PLTL::Unary(op, content) => {
                let content_simplified = content.simplify();
                let may_go_to_other_branch = op == UnaryOp::Not
                    && matches!(
                        &content_simplified,
                        PLTL::Bottom | PLTL::Top | PLTL::Unary(UnaryOp::Not, _)
                    );
                (
                    PLTL::new_unary(op, content_simplified),
                    may_go_to_other_branch,
                )
            }

            PLTL::Binary(BinaryOp::And, box PLTL::Bottom, _) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::And, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::And, box PLTL::Top, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::And, box lhs, box PLTL::Top) => (lhs.simplify(), false),
            PLTL::Binary(BinaryOp::And, _, _) => {
                let mut pendings = SmallVec::new();
                let mut result = SmallVec::<[PLTL; 8]>::new();
                self.collect_commutative(BinaryOp::And, &mut pendings);
                while !pendings.is_empty() {
                    for pending in mem::take(&mut pendings) {
                        let simplified = pending.simplify();
                        match simplified {
                            PLTL::Bottom => return (PLTL::Bottom, true),
                            PLTL::Binary(BinaryOp::And, _, _) => {
                                simplified.collect_commutative(BinaryOp::And, &mut pendings);
                            }
                            atom @ PLTL::Atom(_) => {
                                if result.contains(&PLTL::new_unary(UnaryOp::Not, atom.clone())) {
                                    return (PLTL::Bottom, false);
                                } else {
                                    result.push(atom)
                                }
                            }
                            PLTL::Unary(UnaryOp::Not, box atom @ PLTL::Atom(_)) => {
                                if result.contains(&atom) {
                                    return (PLTL::Bottom, false);
                                } else {
                                    result.push(PLTL::new_unary(UnaryOp::Not, atom))
                                }
                            }
                            _ => result.push(simplified),
                        }
                    }
                }
                result.sort();
                result.dedup();
                let first_is_top = if result.first() == Some(&PLTL::Top) {
                    1
                } else {
                    0
                };
                let result = result
                    .into_iter()
                    .skip(first_is_top)
                    .reduce(|acc, x| acc & x)
                    .unwrap_or(PLTL::Top);
                let may_go_to_other_branch =
                    !matches!(result, PLTL::Binary(BinaryOp::And, _, _) | PLTL::Top);
                (result, may_go_to_other_branch)
            }

            PLTL::Binary(BinaryOp::Or, box PLTL::Top, _) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::Or, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::Or, box PLTL::Bottom, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::Or, box lhs, box PLTL::Bottom) => (lhs.simplify(), false),
            PLTL::Binary(BinaryOp::Or, _, _) => {
                let mut pendings = SmallVec::new();
                let mut result = SmallVec::<[PLTL; 8]>::new();

                self.collect_commutative(BinaryOp::Or, &mut pendings);
                while !pendings.is_empty() {
                    for pending in mem::take(&mut pendings) {
                        let simplified = pending.simplify();
                        match simplified {
                            PLTL::Top => return (PLTL::Top, false),
                            PLTL::Binary(BinaryOp::Or, _, _) => {
                                simplified.collect_commutative(BinaryOp::Or, &mut pendings);
                            }
                            atom @ PLTL::Atom(_) => {
                                if result.contains(&PLTL::new_unary(UnaryOp::Not, atom.clone())) {
                                    return (PLTL::Top, false);
                                } else {
                                    result.push(atom)
                                }
                            }
                            PLTL::Unary(UnaryOp::Not, box atom @ PLTL::Atom(_)) => {
                                if result.contains(&atom) {
                                    return (PLTL::Top, false);
                                } else {
                                    result.push(PLTL::new_unary(UnaryOp::Not, atom))
                                }
                            }
                            _ => result.push(simplified),
                        }
                    }
                }

                result.sort();
                result.dedup();
                let first_is_bottom = if result.first() == Some(&PLTL::Bottom) {
                    1
                } else {
                    0
                };
                let result = result
                    .into_iter()
                    .skip(first_is_bottom)
                    .reduce(|acc, x| acc | x)
                    .unwrap_or(PLTL::Bottom);
                let may_go_to_other_branch =
                    !matches!(result, PLTL::Binary(BinaryOp::Or, _, _) | PLTL::Bottom);
                (result, may_go_to_other_branch)
            }

            PLTL::Binary(BinaryOp::Until, box PLTL::Bottom, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::Until, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::Until, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::Until, box lhs, box rhs) if lhs == rhs => {
                (lhs.simplify(), false)
            }
            PLTL::Binary(
                BinaryOp::Until,
                box lhs,
                box PLTL::Binary(BinaryOp::Until, box rlhs, box rrhs),
            ) if lhs == rlhs => {
                let lhs = lhs.simplify();
                let new_rhs = rrhs.simplify();
                let can_fold_further = match (&lhs, &new_rhs) {
                    (PLTL::Bottom, _) => true,
                    (_, PLTL::Top) => true,
                    (_, PLTL::Bottom) => true,
                    (lhs, PLTL::Binary(BinaryOp::Until, box rlhs, box rrhs)) if lhs == rlhs => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    PLTL::new_binary(BinaryOp::Until, lhs, new_rhs),
                    can_fold_further,
                )
            }
            PLTL::Binary(BinaryOp::Until, box lhs, box rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (PLTL::Bottom, _) => true,
                    (_, PLTL::Top) => true,
                    (_, PLTL::Bottom) => true,
                    (new_lhs, PLTL::Binary(BinaryOp::Until, box rlhs, _)) if new_lhs == rlhs => {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    PLTL::new_binary(BinaryOp::Until, new_lhs, new_rhs),
                    can_fold_further,
                )
            }

            PLTL::Binary(BinaryOp::Release, box PLTL::Top, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::Release, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::Release, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::Release, box lhs, box rhs) if lhs == rhs => {
                (lhs.simplify(), false)
            }
            PLTL::Binary(
                BinaryOp::Release,
                box lhs,
                box PLTL::Binary(BinaryOp::Release, box rlhs, box rrhs),
            ) if lhs == rlhs => {
                let lhs = lhs.simplify();
                let new_rhs = rrhs.simplify();
                let can_fold_further = match (&lhs, &new_rhs) {
                    (PLTL::Top, _) => true,
                    (_, PLTL::Top) => true,
                    (_, PLTL::Bottom) => true,
                    (lhs, PLTL::Binary(BinaryOp::Release, box rlhs, _)) if lhs == rlhs => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    PLTL::new_binary(BinaryOp::Release, lhs, new_rhs),
                    can_fold_further,
                )
            }
            PLTL::Binary(BinaryOp::Release, box lhs, box rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (PLTL::Top, _) => true,
                    (_, PLTL::Top) => true,
                    (_, PLTL::Bottom) => true,
                    (lhs, PLTL::Binary(BinaryOp::Release, box rlhs, _)) if lhs == rlhs => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    PLTL::new_binary(BinaryOp::Release, new_lhs, new_rhs),
                    can_fold_further,
                )
            }

            PLTL::Binary(BinaryOp::WeakUntil, box PLTL::Top, _) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::WeakUntil, box PLTL::Bottom, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::WeakUntil, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::WeakUntil, box lhs, box rhs) if lhs == rhs => {
                (lhs.simplify(), false)
            }
            PLTL::Binary(
                BinaryOp::WeakUntil,
                box PLTL::Binary(BinaryOp::WeakUntil, box llhs, box lrhs),
                box rhs,
            ) if lrhs == rhs => {
                let new_lhs = llhs.simplify();
                let rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &rhs) {
                    (PLTL::Top, _) => true,
                    (PLTL::Bottom, _) => true,
                    (_, PLTL::Top) => true,
                    (PLTL::Binary(BinaryOp::WeakUntil, _, box lrhs), rhs) if lrhs == rhs => true,
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    PLTL::new_binary(BinaryOp::WeakUntil, new_lhs, rhs),
                    can_fold_further,
                )
            }
            PLTL::Binary(BinaryOp::WeakUntil, box lhs, box rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (PLTL::Top, _) => true,
                    (PLTL::Bottom, _) => true,
                    (_, PLTL::Top) => true,
                    (PLTL::Binary(BinaryOp::WeakUntil, _, box lrhs), new_rhs)
                        if lrhs == new_rhs =>
                    {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    PLTL::new_binary(BinaryOp::WeakUntil, new_lhs, new_rhs),
                    can_fold_further,
                )
            }

            PLTL::Binary(BinaryOp::MightyRelease, box PLTL::Bottom, _) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::MightyRelease, box PLTL::Top, box rhs) => {
                (rhs.simplify(), false)
            }
            PLTL::Binary(BinaryOp::MightyRelease, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::MightyRelease, box lhs, box rhs) if lhs == rhs => {
                (lhs.simplify(), false)
            }
            PLTL::Binary(
                BinaryOp::MightyRelease,
                box PLTL::Binary(BinaryOp::MightyRelease, box llhs, box lrhs),
                box rhs,
            ) if lrhs == rhs => {
                let new_lhs = llhs.simplify();
                let rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &rhs) {
                    (PLTL::Bottom, _) => true,
                    (PLTL::Top, _) => true,
                    (_, PLTL::Bottom) => true,
                    (PLTL::Binary(BinaryOp::MightyRelease, _, box lrhs), rhs) if lrhs == rhs => {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    PLTL::new_binary(BinaryOp::MightyRelease, new_lhs, rhs),
                    can_fold_further,
                )
            }
            PLTL::Binary(BinaryOp::MightyRelease, box lhs, box rhs) => {
                let new_lhs = lhs.simplify();
                let new_rhs = rhs.simplify();
                let can_fold_further = match (&new_lhs, &new_rhs) {
                    (PLTL::Bottom, _) => true,
                    (PLTL::Top, _) => true,
                    (_, PLTL::Bottom) => true,
                    (PLTL::Binary(BinaryOp::MightyRelease, _, box lrhs), new_rhs)
                        if lrhs == new_rhs =>
                    {
                        true
                    }
                    (new_lhs, new_rhs) => new_lhs == new_rhs,
                };
                (
                    PLTL::new_binary(BinaryOp::MightyRelease, new_lhs, new_rhs),
                    can_fold_further,
                )
            }

            PLTL::Binary(BinaryOp::Since, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::Since, box PLTL::Bottom, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::Since, box lhs, box rhs) => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if lhs == rhs {
                    (lhs, false)
                } else {
                    let can_fold_further = lhs == PLTL::Bottom || rhs == PLTL::Bottom;
                    (
                        PLTL::new_binary(BinaryOp::Since, lhs, rhs),
                        can_fold_further,
                    )
                }
            }

            PLTL::Binary(BinaryOp::WeakSince, box PLTL::Bottom, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::WeakSince, box PLTL::Top, _) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::WeakSince, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::WeakSince, box lhs, box rhs) => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if lhs == rhs {
                    (lhs.simplify(), false)
                } else {
                    let can_fold_further =
                        lhs == PLTL::Bottom || lhs == PLTL::Top || rhs == PLTL::Top;
                    (
                        PLTL::new_binary(BinaryOp::WeakSince, lhs, rhs),
                        can_fold_further,
                    )
                }
            }

            PLTL::Binary(BinaryOp::BackTo, box PLTL::Bottom, _) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::BackTo, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::BackTo, box PLTL::Top, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::BackTo, box lhs, box rhs) => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if lhs == rhs {
                    (lhs.simplify(), false)
                } else {
                    let can_fold_further =
                        lhs == PLTL::Bottom || lhs == PLTL::Top || rhs == PLTL::Bottom;
                    (
                        PLTL::new_binary(BinaryOp::BackTo, lhs, rhs),
                        can_fold_further,
                    )
                }
            }

            PLTL::Binary(BinaryOp::WeakBackTo, box PLTL::Top, box rhs) => (rhs.simplify(), false),
            PLTL::Binary(BinaryOp::WeakBackTo, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::WeakBackTo, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::WeakBackTo, box lhs, box rhs) => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if lhs == rhs {
                    (lhs.simplify(), false)
                } else {
                    let can_fold_further =
                        lhs == PLTL::Top || rhs == PLTL::Top || rhs == PLTL::Bottom;
                    (
                        PLTL::new_binary(BinaryOp::WeakBackTo, lhs, rhs),
                        can_fold_further,
                    )
                }
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
        panic!("Simplification failed: {result}");
        #[cfg(not(debug_assertions))]
        result
    }
}

#[cfg(test)]
mod tests {
    use crate::pltl::ganerator::generate_formula;

    // #[test]
    // fn test_simplify() {
    //     let (pltl, ctx) = PLTL::from_string("p & ¬p").unwrap();
    //     println!("{}", pltl);
    //     let simplified = pltl.to_no_fgoh();
    //     println!("{}", simplified);
    //     let simplified = simplified.simplify();
    //     println!("{}", simplified);
    // }

    #[test]
    fn test_simplify() {
        for _ in 0..1000 {
            let pltl = generate_formula(5, 2);
            println!("{pltl}");
            let simplified = pltl.to_no_fgoh().simplify();
            println!("{simplified}");
            println!("----");
        }
    }
}
