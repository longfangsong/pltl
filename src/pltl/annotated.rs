use core::fmt;
use std::{collections::HashSet, ptr};

use super::{
    past_subformula::{PastSubformula, PastSubformulaSet, PastSubformularSetContext},
    BinaryOp, UnaryOp, PLTL,
};
use crate::utils::BitSet;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Annotated {
    Top,
    Bottom,
    Atom(u32),
    Unary(UnaryOp, Box<Annotated>),
    Binary(BinaryOp, Box<Annotated>, Box<Annotated>),
    PastSubformula(PastSubformula),
}

impl fmt::Display for Annotated {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Annotated::Top => write!(f, "⊤"),
            Annotated::Bottom => write!(f, "⊥"),
            Annotated::Atom(s) => write!(f, "\"{}\"", s),
            Annotated::Unary(UnaryOp::Not, box content @ Annotated::Unary(UnaryOp::Not, _)) => {
                write!(f, "{}{}", UnaryOp::Not, content)
            }
            Annotated::Unary(op, box content @ Annotated::Binary(_, _, _)) => {
                write!(f, "{}({})", op, content)
            }
            Annotated::Unary(op, box content) => write!(f, "{}{}", op, content),
            Annotated::Binary(op, box lhs, box rhs) => {
                let lhs = match (op, lhs) {
                    (BinaryOp::And, Annotated::Binary(BinaryOp::And, _, _)) => format!("{}", lhs),
                    (BinaryOp::Or, Annotated::Binary(BinaryOp::Or, _, _)) => format!("{}", lhs),
                    (_, Annotated::Binary(_, _, _)) => {
                        format!("({})", lhs)
                    }
                    _ => format!("{}", lhs),
                };
                let rhs = match (op, rhs) {
                    (BinaryOp::And, Annotated::Binary(BinaryOp::And, _, _)) => format!("{}", rhs),
                    (BinaryOp::Or, Annotated::Binary(BinaryOp::Or, _, _)) => format!("{}", rhs),
                    (_, Annotated::Binary(_, _, _)) => {
                        format!("({})", rhs)
                    }
                    _ => format!("{}", rhs),
                };
                write!(f, "{} {} {}", lhs, op, rhs)
            }
            Annotated::PastSubformula(past_subformula) => {
                write!(f, "({}, {:b})", past_subformula.id, past_subformula.state)
            }
        }
    }
}

impl Annotated {
    pub fn new_binary(op: BinaryOp, lhs: Annotated, rhs: Annotated) -> Self {
        Annotated::Binary(op, Box::new(lhs), Box::new(rhs))
    }

    pub fn new_unary(op: UnaryOp, arg: Annotated) -> Self {
        Annotated::Unary(op, Box::new(arg))
    }

    /// Note the pltl must in the context in it's **original** form
    pub(crate) fn from_pltl(pltl: &PLTL, context: &PastSubformularSetContext) -> Self {
        match pltl {
            PLTL::Top => Annotated::Top,
            PLTL::Bottom => Annotated::Bottom,
            PLTL::Atom(atom) => Annotated::Atom(*atom),
            PLTL::Unary(op, box arg) => {
                if op.is_past() {
                    let psf_id = context
                        .past_subformulas
                        .iter()
                        .position(|&psf| ptr::eq(psf, pltl))
                        .unwrap();
                    Annotated::PastSubformula(PastSubformula {
                        id: psf_id as u32,
                        state: context.initial_state,
                    })
                } else {
                    Annotated::new_unary(*op, Annotated::from_pltl(arg, context))
                }
            }
            PLTL::Binary(op, box lhs, box rhs) => {
                if op.is_past() {
                    let psf_id = context
                        .past_subformulas
                        .iter()
                        .position(|&psf| ptr::eq(psf, pltl))
                        .unwrap();
                    Annotated::PastSubformula(PastSubformula {
                        id: psf_id as u32,
                        state: context.initial_state,
                    })
                } else {
                    Annotated::Binary(
                        *op,
                        Box::new(Annotated::from_pltl(lhs, context)),
                        Box::new(Annotated::from_pltl(rhs, context)),
                    )
                }
            }
        }
    }

    pub fn new(context: &PastSubformularSetContext) -> Self {
        Annotated::from_pltl(context.origin, context)
    }

    pub fn to_pltl(&self, context: &PastSubformularSetContext) -> PLTL {
        match self {
            Annotated::Top => PLTL::Top,
            Annotated::Bottom => PLTL::Bottom,
            Annotated::Atom(atom) => PLTL::Atom(*atom),
            Annotated::Unary(op, arg) => PLTL::new_unary(*op, arg.to_pltl(context)),
            Annotated::Binary(op, left, right) => {
                PLTL::new_binary(*op, left.to_pltl(context), right.to_pltl(context))
            }
            Annotated::PastSubformula(psf) => psf.to_pltl(context),
        }
    }

    pub fn rewrite_with_set(
        &self,
        context: &PastSubformularSetContext,
        set: &PastSubformulaSet,
    ) -> Self {
        match self {
            Annotated::Top => Annotated::Top,
            Annotated::Bottom => Annotated::Bottom,
            Annotated::Atom(atom) => Annotated::Atom(*atom),
            Annotated::Unary(op, arg) => {
                Annotated::Unary(*op, Box::new(arg.rewrite_with_set(context, set)))
            }
            Annotated::Binary(op, left, right) => Annotated::Binary(
                *op,
                Box::new(left.rewrite_with_set(context, set)),
                Box::new(right.rewrite_with_set(context, set)),
            ),
            Annotated::PastSubformula(psf) => Annotated::PastSubformula(psf.rewrite(context, set)),
        }
    }

    // todo: is it possible to return a `PastSubformulaSet`?
    pub fn past_subformula_set(
        &self,
        context: &PastSubformularSetContext,
    ) -> HashSet<PastSubformula> {
        match self {
            Annotated::PastSubformula(psf) => {
                let mask = context.masks[psf.id as usize];
                mask.iter()
                    .map(|i| PastSubformula {
                        id: i,
                        state: psf.state,
                    })
                    .collect()
            }
            Annotated::Unary(_, arg) => arg.past_subformula_set(context),
            Annotated::Binary(_, left, right) => {
                let mut result = left.past_subformula_set(context);
                result.extend(right.past_subformula_set(context));
                result
            }
            _ => HashSet::new(),
        }
    }

    fn simplify_until_simplest(&self) -> (Annotated, bool) {
        match self {
            Annotated::Top | Annotated::Bottom | Annotated::Atom(_) => (self.clone(), false),
            Annotated::Unary(UnaryOp::Not, box Annotated::Bottom) => (Annotated::Top, true),
            Annotated::Unary(UnaryOp::Not, box Annotated::Top) => (Annotated::Bottom, true),
            Annotated::Unary(UnaryOp::Not, box Annotated::Unary(UnaryOp::Not, box inner)) => {
                (inner.clone(), true)
            }
            Annotated::Unary(unary_op, box inner) => {
                let (inner, changed) = inner.simplify_until_simplest();
                (Annotated::new_unary(*unary_op, inner), changed)
            }
            Annotated::Binary(BinaryOp::And, box Annotated::Bottom, _) => (Annotated::Bottom, true),
            Annotated::Binary(BinaryOp::And, _, box Annotated::Bottom) => (Annotated::Bottom, true),
            Annotated::Binary(BinaryOp::And, box Annotated::Top, box rhs) => (rhs.clone(), true),
            Annotated::Binary(BinaryOp::And, box lhs, box Annotated::Top) => (lhs.clone(), true),
            Annotated::Binary(BinaryOp::And, box lhs, box rhs) if lhs == rhs => (lhs.clone(), true),
            Annotated::Binary(
                BinaryOp::And,
                box Annotated::Binary(BinaryOp::And, box llhs, box lrhs),
                box rhs,
            ) => {
                let (llhs, _) = llhs.simplify_until_simplest();
                let (lrhs, _) = lrhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    Annotated::new_binary(
                        BinaryOp::And,
                        llhs.clone(),
                        Annotated::new_binary(BinaryOp::And, lrhs.clone(), rhs.clone()),
                    ),
                    true,
                )
            }
            Annotated::Binary(
                BinaryOp::And,
                box lhs,
                box Annotated::Binary(BinaryOp::And, box rlhs, box rhs),
            ) if lhs == rlhs => {
                let (lhs, _) = lhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    Annotated::new_binary(BinaryOp::And, lhs.clone(), rhs.clone()),
                    true,
                )
            }
            Annotated::Binary(
                BinaryOp::And,
                box lhs,
                box Annotated::Binary(BinaryOp::And, box rlhs, box rhs),
            ) if rlhs < lhs => {
                let (rlhs, _) = rlhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    Annotated::new_binary(
                        BinaryOp::And,
                        rlhs.clone(),
                        Annotated::new_binary(BinaryOp::And, lhs.clone(), rhs.clone()),
                    ),
                    true,
                )
            }
            Annotated::Binary(BinaryOp::And, box lhs, box rhs) if rhs < lhs => {
                let (rhs, _) = rhs.simplify_until_simplest();
                let (lhs, _) = lhs.simplify_until_simplest();
                (
                    Annotated::new_binary(BinaryOp::And, rhs.clone(), lhs.clone()),
                    true,
                )
            }
            Annotated::Binary(BinaryOp::Or, box Annotated::Top, _) => (Annotated::Top, true),
            Annotated::Binary(BinaryOp::Or, _, box Annotated::Top) => (Annotated::Top, true),
            Annotated::Binary(BinaryOp::Or, box Annotated::Bottom, box rhs) => (rhs.clone(), true),
            Annotated::Binary(BinaryOp::Or, box lhs, box Annotated::Bottom) => (lhs.clone(), true),
            Annotated::Binary(BinaryOp::Or, box lhs, box rhs) if lhs == rhs => (lhs.clone(), true),
            Annotated::Binary(
                BinaryOp::Or,
                box Annotated::Binary(BinaryOp::Or, box llhs, box lrhs),
                box rhs,
            ) => {
                let (llhs, _) = llhs.simplify_until_simplest();
                let (lrhs, _) = lrhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    Annotated::new_binary(
                        BinaryOp::Or,
                        llhs.clone(),
                        Annotated::new_binary(BinaryOp::Or, lrhs.clone(), rhs.clone()),
                    ),
                    true,
                )
            }
            Annotated::Binary(
                BinaryOp::Or,
                box lhs,
                box Annotated::Binary(BinaryOp::Or, box rlhs, box rhs),
            ) if lhs == rlhs => {
                let (lhs, _) = lhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    Annotated::new_binary(BinaryOp::Or, lhs.clone(), rhs.clone()),
                    true,
                )
            }
            Annotated::Binary(
                BinaryOp::Or,
                box lhs,
                box Annotated::Binary(BinaryOp::Or, box rlhs, box rhs),
            ) if rlhs < lhs => {
                let (rlhs, _) = rlhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (
                    Annotated::new_binary(
                        BinaryOp::Or,
                        rlhs.clone(),
                        Annotated::new_binary(BinaryOp::Or, lhs.clone(), rhs.clone()),
                    ),
                    true,
                )
            }
            Annotated::Binary(BinaryOp::Or, box lhs, box rhs) if rhs < lhs => {
                let (rhs, _) = rhs.simplify_until_simplest();
                let (lhs, _) = lhs.simplify_until_simplest();
                (
                    Annotated::new_binary(BinaryOp::Or, rhs.clone(), lhs.clone()),
                    true,
                )
            }

            Annotated::Binary(BinaryOp::Until, _, box Annotated::Top) => (Annotated::Top, false),
            Annotated::Binary(BinaryOp::Until, box Annotated::Bottom, box rhs) => {
                (rhs.clone(), true)
            }
            Annotated::Binary(BinaryOp::Until, _, box Annotated::Bottom) => {
                (Annotated::Bottom, false)
            }
            Annotated::Binary(BinaryOp::Until, box lhs, box rhs) if lhs == rhs => {
                (lhs.clone(), true)
            }

            Annotated::Binary(BinaryOp::Release, box Annotated::Top, box rhs) => {
                (rhs.clone(), true)
            }
            Annotated::Binary(BinaryOp::Release, _, box Annotated::Top) => (Annotated::Top, false),
            Annotated::Binary(BinaryOp::Release, _, box Annotated::Bottom) => {
                (Annotated::Bottom, false)
            }
            Annotated::Binary(BinaryOp::Release, box lhs, box rhs) if lhs == rhs => {
                (lhs.clone(), true)
            }

            Annotated::Binary(BinaryOp::WeakUntil, box Annotated::Top, _) => {
                (Annotated::Top, false)
            }
            Annotated::Binary(BinaryOp::WeakUntil, box Annotated::Bottom, box rhs) => {
                (rhs.clone(), true)
            }
            Annotated::Binary(BinaryOp::WeakUntil, _, box Annotated::Top) => {
                (Annotated::Top, false)
            }
            Annotated::Binary(BinaryOp::WeakUntil, box lhs, box rhs) if lhs == rhs => {
                (lhs.clone(), true)
            }

            Annotated::Binary(BinaryOp::MightyRelease, box Annotated::Bottom, _) => {
                (Annotated::Bottom, false)
            }
            Annotated::Binary(BinaryOp::MightyRelease, _, box Annotated::Bottom) => {
                (Annotated::Bottom, false)
            }
            Annotated::Binary(BinaryOp::MightyRelease, box Annotated::Top, box rhs) => {
                (rhs.clone(), true)
            }
            Annotated::Binary(BinaryOp::MightyRelease, box lhs, box rhs) if lhs == rhs => {
                (lhs.clone(), true)
            }

            Annotated::Binary(
                op @ (BinaryOp::Release | BinaryOp::Until),
                box lhs,
                box Annotated::Binary(
                    op2 @ (BinaryOp::Release | BinaryOp::Until),
                    box rlhs,
                    box rrhs,
                ),
            ) if op == op2 && lhs == rlhs => {
                let (lhs, _) = lhs.simplify_until_simplest();
                let (rrhs, _) = rrhs.simplify_until_simplest();
                (Annotated::new_binary(*op, lhs, rrhs), true)
            }
            Annotated::Binary(
                op @ (BinaryOp::MightyRelease | BinaryOp::WeakUntil),
                box Annotated::Binary(
                    op2 @ (BinaryOp::MightyRelease | BinaryOp::WeakUntil),
                    box llhs,
                    box lrhs,
                ),
                box rhs,
            ) if op == op2 && lrhs == rhs => {
                let (llhs, _) = llhs.simplify_until_simplest();
                let (rhs, _) = rhs.simplify_until_simplest();
                (Annotated::new_binary(*op, llhs, rhs), true)
            }
            Annotated::Binary(binary_op, box lhs, box rhs) => {
                let (lhs, changed_lhs) = lhs.simplify_until_simplest();
                let (rhs, changed_rhs) = rhs.simplify_until_simplest();
                (
                    Annotated::new_binary(*binary_op, lhs, rhs),
                    changed_lhs || changed_rhs,
                )
            }
            this @ Annotated::PastSubformula(_) => (this.clone(), false),
        }
    }

    pub fn simplify(&self) -> Annotated {
        let mut result = self.clone();
        loop {
            let (new_result, changed) = result.simplify_until_simplest();
            if !changed {
                return new_result;
            }
            result = new_result;
        }
    }
}
