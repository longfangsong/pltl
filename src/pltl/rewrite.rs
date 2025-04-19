use super::{BinaryOp, UnaryOp, PLTL};
use crate::utils::Set;

pub type Rewrite = bool;
pub type RewriteState = bool;
pub const WEAKEN: Rewrite = true;
pub const STRENGTHEN: Rewrite = false;

impl UnaryOp {
    pub fn weaken(&self) -> UnaryOp {
        if self == &UnaryOp::Yesterday {
            UnaryOp::WeakYesterday
        } else {
            *self
        }
    }

    pub fn strengthen(&self) -> UnaryOp {
        if self == &UnaryOp::WeakYesterday {
            UnaryOp::Yesterday
        } else {
            *self
        }
    }

    pub fn weaken_state(&self) -> RewriteState {
        match self {
            UnaryOp::Yesterday => STRENGTHEN,
            UnaryOp::WeakYesterday => WEAKEN,
            _ => unreachable!("Must be past formula"),
        }
    }

    #[inline]
    pub fn rewrite(&self, rewrite: Rewrite) -> UnaryOp {
        if rewrite == WEAKEN {
            self.weaken()
        } else {
            self.strengthen()
        }
    }
}

impl BinaryOp {
    pub fn weaken(&self) -> BinaryOp {
        match self {
            BinaryOp::Since => BinaryOp::WeakSince,
            BinaryOp::BackTo => BinaryOp::WeakBackTo,
            _ => *self,
        }
    }

    pub fn strengthen(&self) -> BinaryOp {
        match self {
            BinaryOp::WeakSince => BinaryOp::Since,
            BinaryOp::WeakBackTo => BinaryOp::BackTo,
            _ => *self,
        }
    }

    pub fn weaken_state(&self) -> RewriteState {
        match self {
            BinaryOp::Since => STRENGTHEN,
            BinaryOp::BackTo => STRENGTHEN,
            BinaryOp::WeakSince => WEAKEN,
            BinaryOp::WeakBackTo => WEAKEN,
            _ => unreachable!("Must be past formula"),
        }
    }

    #[inline]
    pub fn rewrite(&self, rewrite: Rewrite) -> BinaryOp {
        if rewrite == WEAKEN {
            self.weaken()
        } else {
            self.strengthen()
        }
    }
}

impl PLTL {
    pub fn weaken(&mut self) -> &mut Self {
        match self {
            PLTL::Unary(op, _) => *op = op.weaken(),
            PLTL::Binary(op, _, _) => *op = op.weaken(),
            _ => (),
        }
        self
    }

    pub fn strengthen(&mut self) -> &mut Self {
        match self {
            PLTL::Unary(op, _) => *op = op.strengthen(),
            PLTL::Binary(op, _, _) => *op = op.strengthen(),
            _ => (),
        }
        self
    }

    pub fn weaken_state(&self) -> RewriteState {
        match self {
            PLTL::Unary(op, _) => op.weaken_state(),
            PLTL::Binary(op, _, _) => op.weaken_state(),
            _ => unreachable!("Must be past formula"),
        }
    }

    pub fn rewrite(&mut self, rewrite: Rewrite) -> &mut Self {
        match self {
            PLTL::Unary(op, _) => *op = op.rewrite(rewrite),
            PLTL::Binary(op, _, _) => *op = op.rewrite(rewrite),
            _ => (),
        }
        self
    }

    pub fn rewrite_with_set(&mut self, set: &Set<PLTL>) -> &mut Self {
        let in_set =
            matches!(self, PLTL::Unary(_, _) | PLTL::Binary(_, _, _)) && set.contains(self);
        match self {
            PLTL::Unary(op, content) if in_set => {
                *op = op.weaken();
                content.rewrite_with_set(set);
            }
            PLTL::Unary(op, content) => {
                content.rewrite_with_set(set);
                *op = op.strengthen();
            }
            PLTL::Binary(op, lhs, rhs) if in_set => {
                *op = op.weaken();
                lhs.rewrite_with_set(set);
                rhs.rewrite_with_set(set);
            }
            PLTL::Binary(op, lhs, rhs) => {
                *op = op.strengthen();
                lhs.rewrite_with_set(set);
                rhs.rewrite_with_set(set);
            }
            _ => (),
        }
        self
    }

    pub fn weaken_condition(&self) -> Self {
        match self {
            PLTL::Unary(UnaryOp::Yesterday, box content) => content.clone(),
            PLTL::Binary(BinaryOp::Since, _, box rhs) => rhs.clone(),
            PLTL::Binary(BinaryOp::BackTo, box lhs, box rhs) => {
                PLTL::new_binary(BinaryOp::And, lhs.clone(), rhs.clone())
            }
            PLTL::Unary(UnaryOp::WeakYesterday, box content) => content.clone(),
            PLTL::Binary(BinaryOp::WeakSince, box lhs, box rhs) => {
                PLTL::new_binary(BinaryOp::Or, lhs.clone(), rhs.clone())
            }
            PLTL::Binary(BinaryOp::WeakBackTo, _, box rhs) => rhs.clone(),
            _ => unreachable!("Must be past formula"),
        }
    }

    pub fn v_rewrite(&mut self, m: &Set<PLTL>) -> &mut Self {
        let in_set = matches!(self, PLTL::Binary(_, _, _)) && m.contains(self);
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => (),
            PLTL::Unary(_, annotated) => {
                annotated.v_rewrite(m);
            }
            PLTL::Binary(op @ BinaryOp::Until, box lhs, box rhs) => {
                if in_set {
                    lhs.v_rewrite(m);
                    rhs.v_rewrite(m);
                    *op = BinaryOp::WeakUntil;
                } else {
                    *self = Self::Bottom;
                }
            }
            PLTL::Binary(op @ BinaryOp::MightyRelease, box lhs, box rhs) => {
                if in_set {
                    lhs.v_rewrite(m);
                    rhs.v_rewrite(m);
                    *op = BinaryOp::Release;
                } else {
                    *self = Self::Bottom;
                }
            }
            PLTL::Binary(_, box lhs, box rhs) => {
                lhs.v_rewrite(m);
                rhs.v_rewrite(m);
            }
        }
        self
    }

    pub fn u_rewrite(&mut self, n: &Set<PLTL>) -> &mut Self {
        let in_set = matches!(self, PLTL::Binary(_, _, _)) && n.contains(self);
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => (),
            PLTL::Unary(_, annotated) => {
                annotated.u_rewrite(n);
            }
            PLTL::Binary(op @ BinaryOp::WeakUntil, box lhs, box rhs) => {
                if in_set {
                    *self = Self::Top;
                } else {
                    lhs.u_rewrite(n);
                    rhs.u_rewrite(n);
                    *op = BinaryOp::Until;
                }
            }
            PLTL::Binary(op @ BinaryOp::Release, box lhs, box rhs) => {
                if in_set {
                    *self = Self::Top;
                } else {
                    lhs.u_rewrite(n);
                    rhs.u_rewrite(n);
                    *op = BinaryOp::MightyRelease;
                }
            }
            PLTL::Binary(_, box lhs, box rhs) => {
                lhs.u_rewrite(n);
                rhs.u_rewrite(n);
            }
        }
        self
    }
}

impl PLTL {
    pub fn eq_without_strength(&self, other: &Self) -> bool {
        match (self, other) {
            (PLTL::Top, PLTL::Top) => true,
            (PLTL::Bottom, PLTL::Bottom) => true,
            (PLTL::Atom(lhs), PLTL::Atom(rhs)) => lhs == rhs,
            (PLTL::Unary(lhs_op, box lhs), PLTL::Unary(rhs_op, box rhs))
                if lhs_op.strengthen() == rhs_op.strengthen() =>
            {
                Self::eq_without_strength(lhs, rhs)
            }
            (PLTL::Binary(lhs_op, lhs_lhs, lhs_rhs), PLTL::Binary(rhs_op, rhs_lhs, rhs_rhs))
                if lhs_op.strengthen() == rhs_op.strengthen() =>
            {
                Self::eq_without_strength(lhs_lhs, rhs_lhs)
                    && Self::eq_without_strength(lhs_rhs, rhs_rhs)
            }
            _ => false,
        }
    }
}

pub fn rewrite_set_with_set(set: &Set<PLTL>, rewrite_with: &Set<PLTL>) -> Set<PLTL> {
    let mut result = Set::default();
    for pltl in set {
        let mut rewritten = pltl.clone();
        rewritten.rewrite_with_set(rewrite_with);
        result.insert(rewritten);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pltl::PLTL;

    #[test]
    fn test_rewrite_with_set() {
        let (ltl, mut ctx) = PLTL::from_string("a S b").unwrap();
        let the_set = Set::from_iter([ltl].into_iter());

        let mut ltl = PLTL::from_string_increment(
            "(Y (a S b)) | (~Y (a S b)) | (Y (a ~S b)) | (a S b) | (a ~S b)",
            &mut ctx,
        );
        ltl.rewrite_with_set(&the_set);
        assert_eq!(
            format!("{}", ltl.latex(&ctx)),
            "Y(a \\widetilde{S} b) ∨ Y(a \\widetilde{S} b) ∨ Y(a S b) ∨ (a \\widetilde{S} b) ∨ (a S b)"
        );
    }
}
