// use super::{BinaryOp, UnaryOp, LabeledPLTLWithoutStrength};
// use crate::{pltl::rewrite::{Rewrite, RewriteState, STRENGTHEN, WEAKEN}, utils::{BitSet32, Set}};


use crate::{pltl::BinaryOp, utils::{BitSet32, Set}};

use super::{Context, LabeledPLTL};

impl LabeledPLTL {
    pub fn rewrite_with_set(&mut self, set: BitSet32) {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => (),
            LabeledPLTL::Unary(_, labeled_pltl) => {
                labeled_pltl.rewrite_with_set(set);
            }
            LabeledPLTL::Binary(_, lhs, rhs) => {
                lhs.rewrite_with_set(set);
                rhs.rewrite_with_set(set);
            }
            LabeledPLTL::PastSubformula(_, weaken_state) => {
                *weaken_state = set;
            }
        }
    }

    pub fn v_rewrite(&mut self, m: &Set<LabeledPLTL>, ctx: &Context) {
        let contains = matches!(self, LabeledPLTL::Binary(BinaryOp::Until | BinaryOp::MightyRelease, _, _)) && m.contains(self);
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => (),
            LabeledPLTL::Unary(_, content) => content.v_rewrite(m, ctx),
            LabeledPLTL::Binary(op @ BinaryOp::Until, lhs, rhs) => {
                if contains {
                    lhs.v_rewrite(m, ctx);
                    rhs.v_rewrite(m, ctx);
                    *op = BinaryOp::WeakUntil;
                } else {
                    *self = LabeledPLTL::Bottom;
                }
            }
            LabeledPLTL::Binary(op @ BinaryOp::MightyRelease, lhs, rhs) => {
                if contains {
                    lhs.v_rewrite(m, ctx);
                    rhs.v_rewrite(m, ctx);
                    *op = BinaryOp::Release;
                } else {
                    *self = LabeledPLTL::Bottom;
                }
            }
            LabeledPLTL::Binary(_, lhs, rhs) => {
                lhs.v_rewrite(m, ctx);
                rhs.v_rewrite(m, ctx);
            }
            LabeledPLTL::PastSubformula(id, state) => {
                let mut psf = ctx.expand_once[*id as usize].clone();
                psf.set_is_weak(*state);
                psf.v_rewrite(m, ctx);
                *self = psf;
            }
        }
    }

    pub fn u_rewrite(&mut self, n: &Set<LabeledPLTL>, ctx: &Context) {
        let contains = matches!(self, LabeledPLTL::Binary(BinaryOp::Until | BinaryOp::MightyRelease, _, _)) && n.contains(self);
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => (),
            LabeledPLTL::Unary(_, content) => content.u_rewrite(n, ctx),
            LabeledPLTL::Binary(op @ BinaryOp::WeakUntil, lhs, rhs) => {
                if contains {
                    lhs.u_rewrite(n, ctx);
                    rhs.u_rewrite(n, ctx);
                    *op = BinaryOp::Until;
                }
            }
            LabeledPLTL::Binary(op @ BinaryOp::Release, lhs, rhs) => {
                if contains {
                    lhs.u_rewrite(n, ctx);
                    rhs.u_rewrite(n, ctx);
                    *op = BinaryOp::MightyRelease;
                }
            }
            LabeledPLTL::Binary(_, lhs, rhs) => {
                lhs.u_rewrite(n, ctx);
                rhs.u_rewrite(n, ctx);
            }
            LabeledPLTL::PastSubformula(id, state) => {
                let mut psf = ctx.expand_once[*id as usize].clone();
                psf.set_is_weak(*state);
                psf.u_rewrite(n, ctx);
                *self = psf;
            }
        }
    }
}

// impl LabeledPLTLWithoutStrength {
//     pub fn weaken(&mut self) -> &mut Self {
//         self.rewrite(WEAKEN)
//     }

//     pub fn strengthen(&mut self) -> &mut Self {
//         self.rewrite(STRENGTHEN)
//     }

//     pub fn weaken_state(&self) -> RewriteState {
//         match self {
//             LabeledPLTLWithoutStrength::PastSubformula(_, weaken_state) => *weaken_state,
//             _ => unreachable!("Must be past formula"),
//         }
//     }

//     pub fn rewrite(&mut self, rewrite: Rewrite) -> &mut Self {
//         match self {
//             LabeledPLTLWithoutStrength::PastSubformula(_, weaken_state) => {
//                 *weaken_state = rewrite;
//             }
//             _ => (),
//         }
//         self
//     }

//     pub fn rewrite_with_set(&mut self, set: PastSubformulaSet) -> &mut Self {
//         match self {
//             LabeledPLTLWithoutStrength::PastSubformula(_, weaken_state) => {
//                 *weaken_state = rewrite;
//             }
//             _ => (),
//         }
//         self
//     }

//     pub fn weaken_condition(&self) -> Self {
//         match self {
//             LabeledPLTLWithoutStrength::Unary(UnaryOp::Yesterday, box content) => content.clone(),
//             LabeledPLTLWithoutStrength::Binary(BinaryOp::Since, _, box rhs) => rhs.clone(),
//             LabeledPLTLWithoutStrength::Binary(BinaryOp::BackTo, box lhs, box rhs) => {
//                 LabeledPLTLWithoutStrength::new_binary(BinaryOp::And, lhs.clone(), rhs.clone())
//             }
//             LabeledPLTLWithoutStrength::Unary(UnaryOp::WeakYesterday, box content) => content.clone(),
//             LabeledPLTLWithoutStrength::Binary(BinaryOp::WeakSince, box lhs, box rhs) => {
//                 LabeledPLTLWithoutStrength::new_binary(BinaryOp::Or, lhs.clone(), rhs.clone())
//             }
//             LabeledPLTLWithoutStrength::Binary(BinaryOp::WeakBackTo, _, box rhs) => rhs.clone(),
//             _ => unreachable!("Must be past formula"),
//         }
//     }

//     pub fn v_rewrite(&mut self, m: &Set<LabeledPLTLWithoutStrength>) -> &mut Self {
//         let in_set = matches!(self, LabeledPLTLWithoutStrength::Binary(_, _, _)) && m.contains(self);
//         match self {
//             LabeledPLTLWithoutStrength::Top | LabeledPLTLWithoutStrength::Bottom | LabeledPLTLWithoutStrength::Atom(_) => (),
//             LabeledPLTLWithoutStrength::Unary(_, annotated) => {
//                 annotated.v_rewrite(m);
//             }
//             LabeledPLTLWithoutStrength::Binary(op @ BinaryOp::Until, box lhs, box rhs) => {
//                 if in_set {
//                     lhs.v_rewrite(m);
//                     rhs.v_rewrite(m);
//                     *op = BinaryOp::WeakUntil;
//                 } else {
//                     *self = Self::Bottom;
//                 }
//             }
//             LabeledPLTLWithoutStrength::Binary(op @ BinaryOp::MightyRelease, box lhs, box rhs) => {
//                 if in_set {
//                     lhs.v_rewrite(m);
//                     rhs.v_rewrite(m);
//                     *op = BinaryOp::Release;
//                 } else {
//                     *self = Self::Bottom;
//                 }
//             }
//             LabeledPLTLWithoutStrength::Binary(_, box lhs, box rhs) => {
//                 lhs.v_rewrite(m);
//                 rhs.v_rewrite(m);
//             }
//         }
//         self
//     }

//     pub fn u_rewrite(&mut self, n: &Set<LabeledPLTLWithoutStrength>) -> &mut Self {
//         let in_set = matches!(self, LabeledPLTLWithoutStrength::Binary(_, _, _)) && n.contains(self);
//         match self {
//             LabeledPLTLWithoutStrength::Top | LabeledPLTLWithoutStrength::Bottom | LabeledPLTLWithoutStrength::Atom(_) => (),
//             LabeledPLTLWithoutStrength::Unary(_, annotated) => {
//                 annotated.u_rewrite(n);
//             }
//             LabeledPLTLWithoutStrength::Binary(op @ BinaryOp::WeakUntil, box lhs, box rhs) => {
//                 if in_set {
//                     *self = Self::Top;
//                 } else {
//                     lhs.u_rewrite(n);
//                     rhs.u_rewrite(n);
//                     *op = BinaryOp::Until;
//                 }
//             }
//             LabeledPLTLWithoutStrength::Binary(op @ BinaryOp::Release, box lhs, box rhs) => {
//                 if in_set {
//                     *self = Self::Top;
//                 } else {
//                     lhs.u_rewrite(n);
//                     rhs.u_rewrite(n);
//                     *op = BinaryOp::MightyRelease;
//                 }
//             }
//             LabeledPLTLWithoutStrength::Binary(_, box lhs, box rhs) => {
//                 lhs.u_rewrite(n);
//                 rhs.u_rewrite(n);
//             }
//         }
//         self
//     }
// }