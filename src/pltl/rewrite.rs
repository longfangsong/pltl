use std::collections::HashSet;

use super::{BinaryOp, UnaryOp, PLTL};

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
            BinaryOp::Before => BinaryOp::WeakBefore,
            _ => *self,
        }
    }

    pub fn strengthen(&self) -> BinaryOp {
        match self {
            BinaryOp::WeakSince => BinaryOp::Since,
            BinaryOp::WeakBefore => BinaryOp::Before,
            _ => *self,
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
    pub fn weaken(&self) -> Self {
        match self {
            PLTL::Unary(op, content) => PLTL::Unary(op.weaken(), content.clone()),
            PLTL::Binary(op, lhs, rhs) => PLTL::Binary(op.weaken(), lhs.clone(), rhs.clone()),
            _ => self.clone(),
        }
    }

    pub fn inplace_weaken(&mut self) {
        match self {
            PLTL::Unary(op, _) => *op = op.weaken(),
            PLTL::Binary(op, _, _) => *op = op.weaken(),
            _ => (),
        }
    }

    pub fn strengthen(&self) -> Self {
        match self {
            PLTL::Unary(op, content) => PLTL::Unary(op.strengthen(), content.clone()),
            PLTL::Binary(op, lhs, rhs) => PLTL::Binary(op.strengthen(), lhs.clone(), rhs.clone()),
            _ => self.clone(),
        }
    }

    pub fn inplace_strengthen(&mut self) {
        match self {
            PLTL::Unary(op, _) => *op = op.strengthen(),
            PLTL::Binary(op, _, _) => *op = op.strengthen(),
            _ => (),
        }
    }

    #[inline]
    pub fn rewrite(&self, rewrite: Rewrite) -> Self {
        if rewrite == WEAKEN {
            self.weaken()
        } else {
            self.strengthen()
        }
    }

    #[inline]
    pub fn inplace_rewrite(&mut self, rewrite: Rewrite) {
        if rewrite == WEAKEN {
            self.inplace_weaken()
        } else {
            self.inplace_strengthen()
        }
    }

    pub fn rewrite_with_set(&self, set: &HashSet<PLTL>) -> Self {
        match self {
            PLTL::Unary(op, content) if set.contains(self) => {
                PLTL::new_unary(op.weaken(), content.rewrite_with_set(set))
            }
            PLTL::Unary(op, content) => {
                PLTL::new_unary(op.strengthen(), content.rewrite_with_set(set))
            }
            PLTL::Binary(op, lhs, rhs) if set.contains(self) => PLTL::new_binary(
                op.weaken(),
                lhs.rewrite_with_set(set),
                rhs.rewrite_with_set(set),
            ),
            PLTL::Binary(op, lhs, rhs) => PLTL::new_binary(
                op.strengthen(),
                lhs.rewrite_with_set(set),
                rhs.rewrite_with_set(set),
            ),
            _ => self.clone(),
        }
    }

    pub fn weaken_condition(&self) -> Self {
        match self {
            PLTL::Unary(UnaryOp::Yesterday, box content) => content.clone(),
            PLTL::Binary(BinaryOp::Since, _, box rhs) => rhs.clone(),
            PLTL::Binary(BinaryOp::Before, box lhs, box rhs) => {
                PLTL::new_binary(BinaryOp::And, lhs.clone(), rhs.clone())
            }
            PLTL::Unary(UnaryOp::WeakYesterday, box content) => content.clone(),
            PLTL::Binary(BinaryOp::WeakSince, box lhs, box rhs) => {
                PLTL::new_binary(BinaryOp::Or, lhs.clone(), rhs.clone())
            }
            PLTL::Binary(BinaryOp::WeakBefore, _, box rhs) => rhs.clone(),
            _ => unreachable!("Must be past formula"),
        }
    }

    pub fn v_rewrite(&self, s: &HashSet<PLTL>) -> Self {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => self.clone(),
            PLTL::Unary(unary_op, annotated) => Self::new_unary(*unary_op, annotated.v_rewrite(s)),
            PLTL::Binary(BinaryOp::Until, box lhs, box rhs) => {
                if s.contains(self) {
                    let rewritten_lhs = lhs.v_rewrite( s);
                    let rewritten_rhs = rhs.v_rewrite( s);
                    Self::new_binary(BinaryOp::WeakUntil, rewritten_lhs, rewritten_rhs)
                } else {
                    Self::Bottom
                }
            }
            PLTL::Binary(BinaryOp::MightyRelease, box lhs, box rhs) => {
                if s.contains(self) {
                    let rewritten_lhs = lhs.v_rewrite(s);
                    let rewritten_rhs = rhs.v_rewrite(s);
                    Self::new_binary(BinaryOp::Release, rewritten_lhs, rewritten_rhs)
                } else {
                    Self::Bottom
                }
            }
            PLTL::Binary(binary_op, box lhs, box rhs) => 
                Self::new_binary(*binary_op, lhs.v_rewrite(s), rhs.v_rewrite(s)),
        }
    }

    pub fn u_rewrite(&self, s: &HashSet<PLTL>) -> Self {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => self.clone(),
            PLTL::Unary(unary_op, annotated) => Self::new_unary(*unary_op, annotated.u_rewrite(s)),
            PLTL::Binary(BinaryOp::WeakUntil, box lhs, box rhs) => {
                if s.contains(self) {
                    Self::Top
                } else {
                    let rewritten_lhs = lhs.u_rewrite(s);
                    let rewritten_rhs = rhs.u_rewrite(s);
                    Self::new_binary(BinaryOp::Until, rewritten_lhs, rewritten_rhs)
                }
            }
            PLTL::Binary(BinaryOp::Release, box lhs, box rhs) => {
                if s.contains(self) {
                    Self::Top
                } else {
                    Self::new_binary(BinaryOp::MightyRelease, lhs.u_rewrite(s), rhs.u_rewrite(s))
                }
            }
            PLTL::Binary(binary_op, box lhs, box rhs) => 
                Self::new_binary(*binary_op, lhs.u_rewrite(s), rhs.u_rewrite(s)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pltl::parse;

    #[test]
    fn test_rewrite_with_set() {
        let the_set = HashSet::from([parse("a S b").unwrap().1]);

        let ltl: PLTL = "(Y (a S b)) | (~Y (a S b)) | (Y (a ~S b)) | (a S b) | (a ~S b)".parse().unwrap();
        let weakened_ltl = ltl.rewrite_with_set(&the_set);
        assert_eq!(
            format!("{}", weakened_ltl.latex()),
            "Y(a \\widetilde{S} b) ∨ Y(a \\widetilde{S} b) ∨ Y(a S b) ∨ (a \\widetilde{S} b) ∨ (a S b)"
        );
    }
}
