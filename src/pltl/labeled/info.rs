use std::fmt::Binary;

use crate::{
    pltl::{BinaryOp, UnaryOp},
    utils::{BitSet, BitSet32, Set},
};

use super::{Context, LabeledPLTL};

impl LabeledPLTL {
    pub fn past_subformulas_without_state(&self, ctx: &Context) -> BitSet32 {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => BitSet32::default(),
            LabeledPLTL::Unary(_, labeled_pltlwithout_strength) => {
                labeled_pltlwithout_strength.past_subformulas_without_state(ctx)
            }
            LabeledPLTL::Binary(_, lhs, rhs) => {
                let left = lhs.past_subformulas_without_state(ctx);
                let right = rhs.past_subformulas_without_state(ctx);
                left | right
            }
            LabeledPLTL::PastSubformula(id, _) => {
                // todo: push down state?
                ctx.past_subformula_contains[*id as usize].clone()
            }
        }
    }

    pub fn past_subformulas(&self, ctx: &Context) -> Set<(u32, BitSet32)> {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => Set::default(),
            LabeledPLTL::Unary(_, labeled_pltl) => labeled_pltl.past_subformulas(ctx),
            LabeledPLTL::Binary(_, lhs, rhs) => lhs
                .past_subformulas(ctx)
                .into_iter()
                .chain(rhs.past_subformulas(ctx).into_iter())
                .collect(),
            LabeledPLTL::PastSubformula(id, state) => ctx.past_subformula_contains[*id as usize]
                .iter()
                .map(|id| (id, state & ctx.past_subformula_contains[id as usize]))
                .collect(),
        }
    }

    pub fn set_is_weak(&mut self, weaken_state: BitSet32) {
        match self {
            LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => (),
            LabeledPLTL::Unary(_, labeled_pltl) => {
                labeled_pltl.set_is_weak(weaken_state);
            }
            LabeledPLTL::Binary(_, lhs, rhs) => {
                lhs.set_is_weak(weaken_state);
                rhs.set_is_weak(weaken_state);
            }
            LabeledPLTL::PastSubformula(_, weak) => {
                *weak = weaken_state;
            }
        }
    }
}

pub fn psf_weaken_condition(ctx: &Context, psf_id: u32, state: BitSet32) -> LabeledPLTL {
    let mut result = match (state.get(psf_id), &ctx.expand_once[psf_id as usize]) {
        (true, LabeledPLTL::Binary(BinaryOp::WeakSince | BinaryOp::Since, box lhs, box rhs)) => {
            // WeakSince
            LabeledPLTL::new_binary(BinaryOp::Or, lhs.clone(), rhs.clone())
        }
        (false, LabeledPLTL::Binary(BinaryOp::WeakSince | BinaryOp::Since, _, box rhs)) => {
            // Since
            rhs.clone()
        }
        (true, LabeledPLTL::Binary(BinaryOp::WeakBackTo | BinaryOp::BackTo, _, box rhs)) => {
            // WeakBackTo
            rhs.clone()
        }
        (false, LabeledPLTL::Binary(BinaryOp::WeakBackTo | BinaryOp::BackTo, box lhs, box rhs)) => {
            // BackTo
            LabeledPLTL::new_binary(BinaryOp::And, lhs.clone(), rhs.clone())
        }
        (_, LabeledPLTL::Unary(UnaryOp::Yesterday | UnaryOp::WeakYesterday, box content)) => {
            content.clone()
        }
        _ => unreachable!(),
    };
    // todo: is weaken_condition.set(psf_id, false); necessary?
    result.set_is_weak(state);
    result
}

pub fn weaken_condition(ctx: &Context, pltl: &LabeledPLTL) -> LabeledPLTL {
    match pltl {
        LabeledPLTL::Top | LabeledPLTL::Bottom | LabeledPLTL::Atom(_) => unreachable!(),
        LabeledPLTL::Unary(UnaryOp::Yesterday | UnaryOp::WeakYesterday, box content) => {
            content.clone()
        }
        LabeledPLTL::Binary(BinaryOp::WeakSince, box lhs, box rhs) => LabeledPLTL::new_binary(
            BinaryOp::Or,
            lhs.clone(),
            rhs.clone(),
        ),
        LabeledPLTL::Binary(BinaryOp::Since | BinaryOp::WeakBackTo, _, box rhs) => rhs.clone(),
        LabeledPLTL::Binary(BinaryOp::BackTo, box lhs, box rhs) => LabeledPLTL::new_binary(
            BinaryOp::And,
            lhs.clone(),
            rhs.clone(),
        ),
        LabeledPLTL::PastSubformula(id, state) => {
            psf_weaken_condition(ctx, *id, *state)
        }
        _ => unreachable!(),
    }
}

impl LabeledPLTL {
    pub fn eq_under_ctx(&self, other: &Self, ctx: &Context) -> bool {
        match (self, other) {
            (LabeledPLTL::Top, LabeledPLTL::Top) => true,
            (LabeledPLTL::Bottom, LabeledPLTL::Bottom) => true,
            (LabeledPLTL::Atom(a), LabeledPLTL::Atom(b)) => a == b,
            (LabeledPLTL::Unary(lhs_op, lhs_content), LabeledPLTL::Unary(rhs_op, rhs_content)) => {
                lhs_op == rhs_op && Self::eq_under_ctx(lhs_content, rhs_content, ctx)
            }
            (
                LabeledPLTL::Binary(lhs_op, lhs_left, lhs_right),
                LabeledPLTL::Binary(rhs_op, rhs_left, rhs_right),
            ) => {
                lhs_op == rhs_op
                    && Self::eq_under_ctx(lhs_left, rhs_left, ctx)
                    && Self::eq_under_ctx(lhs_right, rhs_right, ctx)
            }
            (
                LabeledPLTL::PastSubformula(lhs_id, lhs_weaken_state),
                LabeledPLTL::PastSubformula(rhs_id, rhs_weaken_state),
            ) => {
                if lhs_id == rhs_id {
                    let normalized_lhs_weaken_state =
                        lhs_weaken_state & ctx.past_subformula_contains[*lhs_id as usize];
                    let normalized_rhs_weaken_state =
                        rhs_weaken_state & ctx.past_subformula_contains[*rhs_id as usize];
                    normalized_lhs_weaken_state == normalized_rhs_weaken_state
                } else {
                    let lhs_expand_once = &ctx.expand_once[*lhs_id as usize];
                    let rhs_expand_once = &ctx.expand_once[*rhs_id as usize];
                    match (lhs_expand_once, rhs_expand_once) {
                        (
                            LabeledPLTL::Unary(lhs_op, lhs_content),
                            LabeledPLTL::Unary(rhs_op, rhs_content),
                        ) => {
                            let lhs_op_with_state = lhs_op.rewrite(lhs_weaken_state.get(*lhs_id));
                            let rhs_op_with_state = rhs_op.rewrite(rhs_weaken_state.get(*rhs_id));
                            lhs_op_with_state == rhs_op_with_state
                                && Self::eq_under_ctx(lhs_content, rhs_content, ctx)
                        }
                        (
                            LabeledPLTL::Binary(lhs_op, lhs_left, lhs_right),
                            LabeledPLTL::Binary(rhs_op, rhs_left, rhs_right),
                        ) => {
                            let lhs_op_with_state = lhs_op.rewrite(lhs_weaken_state.get(*lhs_id));
                            let rhs_op_with_state = rhs_op.rewrite(rhs_weaken_state.get(*rhs_id));
                            lhs_op_with_state == rhs_op_with_state
                                && Self::eq_under_ctx(lhs_left, rhs_left, ctx)
                                && Self::eq_under_ctx(lhs_right, rhs_right, ctx)
                        }
                        _ => false,
                    }
                }
            }
            _ => false,
        }
    }
}
