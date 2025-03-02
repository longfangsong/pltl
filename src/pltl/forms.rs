use super::{BinaryOp, UnaryOp, PLTL};

impl PLTL {
    pub fn remove_FGOH(&self) -> Self {
        match self {
            PLTL::Top => PLTL::Top,
            PLTL::Bottom => PLTL::Bottom,
            PLTL::Atom(_) => self.clone(),
            PLTL::Unary(UnaryOp::Eventually, content) => {
                PLTL::new_binary(BinaryOp::Until, PLTL::Top, content.remove_FGOH())
            }
            PLTL::Unary(UnaryOp::Globally, box content) => {
                PLTL::new_binary(BinaryOp::WeakUntil, content.remove_FGOH(), PLTL::Bottom)
            }
            PLTL::Unary(UnaryOp::Once, content) => {
                PLTL::new_binary(BinaryOp::Since, PLTL::Top, content.remove_FGOH())
            }
            PLTL::Unary(UnaryOp::Historically, box content) => PLTL::new_unary(
                UnaryOp::Not,
                PLTL::new_unary(
                    UnaryOp::Once,
                    PLTL::new_unary(UnaryOp::Not, content.clone()),
                )
                .remove_FGOH(),
            ),
            PLTL::Unary(op, content) => PLTL::new_unary(*op, content.remove_FGOH()),
            PLTL::Binary(op, l, r) => PLTL::new_binary(*op, l.remove_FGOH(), r.remove_FGOH()),
        }
    }

    fn push_negation(&self) -> Self {
        match self {
            PLTL::Top => PLTL::Bottom,
            PLTL::Bottom => PLTL::Top,
            PLTL::Atom(_) => PLTL::new_unary(UnaryOp::Not, self.clone()),
            PLTL::Unary(UnaryOp::Not, box content) => content.clone(),
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
                BinaryOp::WeakBefore,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
            PLTL::Binary(BinaryOp::WeakBefore, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::Since, lhs.push_negation(), rhs.push_negation())
            }
            PLTL::Binary(BinaryOp::WeakSince, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::Before, lhs.push_negation(), rhs.push_negation())
            }
            PLTL::Binary(BinaryOp::Before, lhs, rhs) => PLTL::new_binary(
                BinaryOp::WeakSince,
                lhs.push_negation(),
                rhs.push_negation(),
            ),
        }
    }

    pub fn negation_normal_form(&self) -> Self {
        match self {
            PLTL::Top => PLTL::Top,
            PLTL::Bottom => PLTL::Bottom,
            PLTL::Atom(_) => self.clone(),
            PLTL::Unary(UnaryOp::Not, box PLTL::Atom(_)) => self.clone(),
            PLTL::Unary(UnaryOp::Not, content) => content.push_negation().negation_normal_form(),
            PLTL::Unary(op, content) => PLTL::new_unary(*op, content.negation_normal_form()),
            PLTL::Binary(op, l, r) => {
                PLTL::new_binary(*op, l.negation_normal_form(), r.negation_normal_form())
            }
        }
    }

    pub fn to_dnf(&self) -> Self {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => self.clone(),
            PLTL::Unary(op, content) => PLTL::new_unary(*op, content.to_dnf()),
            PLTL::Binary(BinaryOp::And, lhs, rhs) => {
                let lhs_dnf = lhs.to_dnf();
                let rhs_dnf = rhs.to_dnf();

                match (&lhs_dnf, &rhs_dnf) {
                    (
                        PLTL::Binary(BinaryOp::Or, box l1, box l2),
                        PLTL::Binary(BinaryOp::Or, box r1, box r2),
                    ) => PLTL::new_binary(
                        BinaryOp::Or,
                        PLTL::new_binary(
                            BinaryOp::Or,
                            PLTL::new_binary(
                                BinaryOp::Or,
                                PLTL::new_binary(BinaryOp::And, l1.clone(), r1.clone()).to_dnf(),
                                PLTL::new_binary(BinaryOp::And, l1.clone(), r2.clone()).to_dnf(),
                            ),
                            PLTL::new_binary(BinaryOp::And, l2.clone(), r1.clone()).to_dnf(),
                        ),
                        PLTL::new_binary(BinaryOp::And, l2.clone(), r2.clone()).to_dnf(),
                    ),
                    (PLTL::Binary(BinaryOp::Or, box l1, box l2), _) => PLTL::new_binary(
                        BinaryOp::Or,
                        PLTL::new_binary(BinaryOp::And, l1.clone(), rhs_dnf.clone()).to_dnf(),
                        PLTL::new_binary(BinaryOp::And, l2.clone(), rhs_dnf.clone()).to_dnf(),
                    ),
                    (_, PLTL::Binary(BinaryOp::Or, box r1, box r2)) => PLTL::new_binary(
                        BinaryOp::Or,
                        PLTL::new_binary(BinaryOp::And, lhs_dnf.clone(), r1.clone()).to_dnf(),
                        PLTL::new_binary(BinaryOp::And, lhs_dnf.clone(), r2.clone()).to_dnf(),
                    ),
                    _ => PLTL::new_binary(BinaryOp::And, lhs_dnf, rhs_dnf),
                }
            }
            PLTL::Binary(BinaryOp::Or, lhs, rhs) => {
                PLTL::new_binary(BinaryOp::Or, lhs.to_dnf(), rhs.to_dnf())
            }
            PLTL::Binary(op, lhs, rhs) => PLTL::new_binary(*op, lhs.to_dnf(), rhs.to_dnf()),
        }
    }

    pub fn flatten(&self) -> Self {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => self.clone(),
            PLTL::Unary(op, content) => PLTL::new_unary(*op, content.flatten()),
            PLTL::Binary(BinaryOp::And, box lhs, box rhs) => {
                let lhs = lhs.flatten();
                let rhs = rhs.flatten();
                match (lhs, rhs) {
                    (PLTL::Binary(BinaryOp::And, box l1, box l2), r) => PLTL::new_binary(
                        BinaryOp::And,
                        l1,
                        PLTL::new_binary(BinaryOp::And, l2, r).flatten(),
                    ),
                    (l, r) => PLTL::new_binary(BinaryOp::And, l, r),
                }
            }
            PLTL::Binary(BinaryOp::Or, box lhs, box rhs) => {
                let lhs = lhs.flatten();
                let rhs = rhs.flatten();
                match (lhs, rhs) {
                    (PLTL::Binary(BinaryOp::Or, box l1, box l2), r) => PLTL::new_binary(
                        BinaryOp::Or,
                        l1,
                        PLTL::new_binary(BinaryOp::Or, l2, r).flatten(),
                    ),
                    (l, r) => PLTL::new_binary(BinaryOp::Or, l, r),
                }
            }
            PLTL::Binary(op, lhs, rhs) => PLTL::new_binary(*op, lhs.flatten(), rhs.flatten()),
        }
    }

    fn least_operators_on_no_FGOH(self) -> Self {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => self,
            PLTL::Unary(UnaryOp::WeakYesterday, box content) => PLTL::new_binary(
                BinaryOp::Or,
                PLTL::new_unary(UnaryOp::Yesterday, content.least_operators_on_no_FGOH()),
                PLTL::new_unary(UnaryOp::Not, PLTL::new_unary(UnaryOp::Yesterday, PLTL::Top)),
            ),
            PLTL::Binary(BinaryOp::WeakUntil, box lhs, box rhs) => {
                let lhs = lhs.least_operators_on_no_FGOH();
                let rhs = rhs.least_operators_on_no_FGOH();
                PLTL::new_binary(
                    BinaryOp::Or,
                    PLTL::new_binary(BinaryOp::Until, lhs.clone(), rhs),
                    PLTL::new_unary(UnaryOp::Globally, lhs).least_operators(),
                )
            }
            PLTL::Binary(BinaryOp::WeakSince, box lhs, box rhs) => {
                let lhs = lhs.least_operators_on_no_FGOH();
                let rhs = rhs.least_operators_on_no_FGOH();
                PLTL::new_binary(
                    BinaryOp::Or,
                    PLTL::new_binary(BinaryOp::Since, lhs.clone(), rhs),
                    PLTL::new_unary(UnaryOp::Historically, lhs).least_operators(),
                )
            }
            PLTL::Binary(BinaryOp::MightyRelease, box lhs, box rhs) => {
                let lhs = lhs.least_operators_on_no_FGOH();
                let rhs = rhs.least_operators_on_no_FGOH();
                PLTL::new_binary(
                    BinaryOp::Until,
                    rhs.clone(),
                    PLTL::new_binary(BinaryOp::And, lhs, rhs),
                )
            }
            PLTL::Binary(BinaryOp::Before, box lhs, box rhs) => {
                let lhs = lhs.least_operators_on_no_FGOH();
                let rhs = rhs.least_operators_on_no_FGOH();
                PLTL::new_binary(
                    BinaryOp::Since,
                    rhs.clone(),
                    PLTL::new_binary(BinaryOp::And, lhs, rhs),
                )
            }
            PLTL::Binary(BinaryOp::Release, box lhs, box rhs) => {
                let lhs = lhs.least_operators_on_no_FGOH();
                let rhs = rhs.least_operators_on_no_FGOH();
                PLTL::new_binary(
                    BinaryOp::WeakUntil,
                    rhs.clone(),
                    PLTL::new_binary(BinaryOp::And, lhs, rhs),
                )
                .least_operators_on_no_FGOH()
            }
            PLTL::Binary(BinaryOp::WeakBefore, box lhs, box rhs) => {
                let lhs = lhs.least_operators_on_no_FGOH();
                let rhs = rhs.least_operators_on_no_FGOH();
                PLTL::new_binary(
                    BinaryOp::WeakSince,
                    rhs.clone(),
                    PLTL::new_binary(BinaryOp::And, lhs, rhs),
                )
                .least_operators_on_no_FGOH()
            }
            PLTL::Unary(op, content) => PLTL::new_unary(op, content.least_operators_on_no_FGOH()),
            PLTL::Binary(op, lhs, rhs) => PLTL::new_binary(
                op,
                lhs.least_operators_on_no_FGOH(),
                rhs.least_operators_on_no_FGOH(),
            ),
        }
    }

    pub fn least_operators(&self) -> Self {
        self.remove_FGOH().least_operators_on_no_FGOH()
    }
}

impl PLTL {
    fn simplify_until_simplest(&self) -> (PLTL, bool) {
        // println!("simplify_until_simplest: {}", self);
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => (self.clone(), false),
            PLTL::Unary(UnaryOp::Not, box PLTL::Bottom) => (PLTL::Top, true),
            PLTL::Unary(UnaryOp::Not, box PLTL::Top) => (PLTL::Bottom, true),
            PLTL::Unary(UnaryOp::Not, box PLTL::Unary(UnaryOp::Not, box inner)) => {
                (inner.clone(), true)
            }
            PLTL::Unary(unary_op, box inner) => {
                let (inner, changed) = inner.simplify_until_simplest();
                (PLTL::new_unary(*unary_op, inner), changed)
            }
            PLTL::Binary(BinaryOp::And, box PLTL::Bottom, _) => (PLTL::Bottom, true),
            PLTL::Binary(BinaryOp::And, _, box PLTL::Bottom) => (PLTL::Bottom, true),
            PLTL::Binary(BinaryOp::And, box PLTL::Top, box rhs) => (rhs.clone(), true),
            PLTL::Binary(BinaryOp::And, box lhs, box PLTL::Top) => (lhs.clone(), true),
            PLTL::Binary(BinaryOp::And, box lhs, box rhs) if lhs == rhs => (lhs.clone(), true),
            PLTL::Binary(
                BinaryOp::And,
                box PLTL::Binary(BinaryOp::And, box llhs, box lrhs),
                box rhs,
            ) => {
                let (llhs, _) = llhs.simplify_until_simplest();
                let (lrhs, _) = lrhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    PLTL::new_binary(
                        BinaryOp::And,
                        llhs.clone(),
                        PLTL::new_binary(BinaryOp::And, lrhs.clone(), rhs.clone()),
                    ),
                    true,
                )
            }
            PLTL::Binary(
                BinaryOp::And,
                box lhs,
                box PLTL::Binary(BinaryOp::And, box rlhs, box rhs),
            ) if lhs == rlhs => {
                let (lhs, _) = lhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    PLTL::new_binary(BinaryOp::And, lhs.clone(), rhs.clone()),
                    true,
                )
            }
            PLTL::Binary(
                BinaryOp::And,
                box lhs,
                box PLTL::Binary(BinaryOp::And, box rlhs, box rhs),
            ) if rlhs < lhs => {
                let (rlhs, _) = rlhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    PLTL::new_binary(
                        BinaryOp::And,
                        rlhs.clone(),
                        PLTL::new_binary(BinaryOp::And, lhs.clone(), rhs.clone()),
                    ),
                    true,
                )
            }
            PLTL::Binary(BinaryOp::And, box lhs, box rhs) if rhs < lhs => {
                let (rhs, _) = rhs.simplify_until_simplest();
                let (lhs, _) = lhs.simplify_until_simplest();
                (
                    PLTL::new_binary(BinaryOp::And, rhs.clone(), lhs.clone()),
                    true,
                )
            }
            PLTL::Binary(BinaryOp::Or, box PLTL::Top, _) => (PLTL::Top, true),
            PLTL::Binary(BinaryOp::Or, _, box PLTL::Top) => (PLTL::Top, true),
            PLTL::Binary(BinaryOp::Or, box PLTL::Bottom, box rhs) => (rhs.clone(), true),
            PLTL::Binary(BinaryOp::Or, box lhs, box PLTL::Bottom) => (lhs.clone(), true),
            PLTL::Binary(BinaryOp::Or, box lhs, box rhs) if lhs == rhs => (lhs.clone(), true),
            PLTL::Binary(
                BinaryOp::Or,
                box PLTL::Binary(BinaryOp::Or, box llhs, box lrhs),
                box rhs,
            ) => {
                let (llhs, _) = llhs.simplify_until_simplest();
                let (lrhs, _) = lrhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    PLTL::new_binary(
                        BinaryOp::Or,
                        llhs.clone(),
                        PLTL::new_binary(BinaryOp::Or, lrhs.clone(), rhs.clone()),
                    ),
                    true,
                )
            }
            PLTL::Binary(
                BinaryOp::Or,
                box lhs,
                box PLTL::Binary(BinaryOp::Or, box rlhs, box rhs),
            ) if lhs == rlhs => {
                let (lhs, _) = lhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    PLTL::new_binary(BinaryOp::Or, lhs.clone(), rhs.clone()),
                    true,
                )
            }
            PLTL::Binary(
                BinaryOp::Or,
                box lhs,
                box PLTL::Binary(BinaryOp::Or, box rlhs, box rhs),
            ) if rlhs < lhs => {
                let (rlhs, _) = rlhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    PLTL::new_binary(
                        BinaryOp::Or,
                        rlhs.clone(),
                        PLTL::new_binary(BinaryOp::Or, lhs.clone(), rhs.clone()),
                    ),
                    true,
                )
            }
            PLTL::Binary(BinaryOp::Or, box lhs, box rhs) if rhs < lhs => {
                let (rhs, _) = rhs.simplify_until_simplest();
                let (lhs, _) = lhs.simplify_until_simplest();
                (
                    PLTL::new_binary(BinaryOp::Or, rhs.clone(), lhs.clone()),
                    true,
                )
            }

            PLTL::Binary(BinaryOp::Until, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::Until, box PLTL::Bottom, box rhs) => (rhs.clone(), true),
            PLTL::Binary(BinaryOp::Until, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::Until, box lhs, box rhs) if lhs == rhs => (lhs.clone(), true),

            PLTL::Binary(BinaryOp::Release, box PLTL::Top, box rhs) => (rhs.clone(), true),
            PLTL::Binary(BinaryOp::Release, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::Release, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::Release, box lhs, box rhs) if lhs == rhs => (lhs.clone(), true),

            PLTL::Binary(BinaryOp::WeakUntil, box PLTL::Top, _) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::WeakUntil, box PLTL::Bottom, box rhs) => (rhs.clone(), true),
            PLTL::Binary(BinaryOp::WeakUntil, _, box PLTL::Top) => (PLTL::Top, false),
            PLTL::Binary(BinaryOp::WeakUntil, box lhs, box rhs) if lhs == rhs => {
                (lhs.clone(), true)
            }

            PLTL::Binary(BinaryOp::MightyRelease, box PLTL::Bottom, _) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::MightyRelease, _, box PLTL::Bottom) => (PLTL::Bottom, false),
            PLTL::Binary(BinaryOp::MightyRelease, box PLTL::Top, box rhs) => (rhs.clone(), true),
            PLTL::Binary(BinaryOp::MightyRelease, box lhs, box rhs) if lhs == rhs => {
                (lhs.clone(), true)
            }

            PLTL::Binary(
                op @ (BinaryOp::Release | BinaryOp::Until),
                box lhs,
                box PLTL::Binary(op2 @ (BinaryOp::Release | BinaryOp::Until), box rlhs, box rrhs),
            ) if op == op2 && lhs == rlhs => {
                let (lhs, _) = lhs.simplify_until_simplest();
                let (rrhs, _) = rrhs.simplify_until_simplest();
                (PLTL::new_binary(*op, lhs, rrhs), true)
            }
            PLTL::Binary(
                op @ (BinaryOp::MightyRelease | BinaryOp::WeakUntil),
                box PLTL::Binary(
                    op2 @ (BinaryOp::MightyRelease | BinaryOp::WeakUntil),
                    box llhs,
                    box lrhs,
                ),
                box rhs,
            ) if op == op2 && lrhs == rhs => {
                let (llhs, _) = llhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (PLTL::new_binary(*op, llhs, rhs), true)
            }
            PLTL::Binary(binary_op, box lhs, box rhs) => {
                let (lhs, changed_lhs) = lhs.simplify_until_simplest();
                let (rhs, changed_rhs) = rhs.simplify_until_simplest();
                (
                    PLTL::new_binary(*binary_op, lhs, rhs),
                    changed_lhs || changed_rhs,
                )
            }
        }
    }

    pub fn simplify(&self) -> PLTL {
        let mut result = self.clone();
        loop {
            let (new_result, changed) = result.simplify_until_simplest();
            if !changed {
                return new_result;
            }
            result = new_result;
        }
    }

    pub fn normal_form(&self) -> Self {
        self.remove_FGOH()
            .negation_normal_form()
            .simplify()
            .flatten()
            .simplify()
    }
}
