use crate::pltl;
use clap::builder::Str;
use std::{
    fmt,
    ops::{BitAnd, BitOr},
    ptr,
};

use crate::utils::{BitSet, BitSet32};

use super::{rewrite::RewriteState, BinaryOp, UnaryOp, PLTL};

pub mod after_function;
mod forms;
pub mod info;
mod rewrite;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LabeledPLTL {
    Top,
    Bottom,
    Atom(u32),
    Unary(UnaryOp, Box<LabeledPLTL>),
    Binary(BinaryOp, Box<LabeledPLTL>, Box<LabeledPLTL>),
    PastSubformula(u32, BitSet32),
}

#[derive(Debug, Clone, Default)]
pub struct Context<'a> {
    pub past_subformulas: Vec<&'a PLTL>,
    pub past_subformula_contains: Vec<BitSet32>,
    pub expand_once: Vec<LabeledPLTL>,
    pub initial_weaken_state: BitSet32,
}

impl<'a> fmt::Display for Context<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let max_psf_id_width = self
            .past_subformulas
            .len()
            .to_string()
            .len()
            .max("id".len());
        let max_psf_width = self
            .past_subformulas
            .iter()
            .map(|psf| psf.to_string().len())
            .max()
            .unwrap_or(0)
            .max("psf_expanded".len());
        let max_expand_once_width = self
            .expand_once
            .iter()
            .map(|e| e.to_string().len())
            .max()
            .unwrap_or(0)
            .max("expand_once".len());

        write!(f, "{:>width$}\t", "id", width = max_psf_id_width)?;
        write!(f, "{:>width$}\t", "psf_expanded", width = max_psf_width)?;
        writeln!(
            f,
            "{:>width$}",
            "expand_once",
            width = max_expand_once_width
        )?;
        for (i, psf) in self.past_subformulas.iter().enumerate() {
            write!(f, "{:>width$}\t", i, width = max_psf_id_width)?;
            write!(f, "{:>width$}\t", psf.to_string(), width = max_psf_width)?;
            writeln!(
                f,
                "{:>width$}",
                self.expand_once[i].to_string(),
                width = max_expand_once_width
            )?;
        }
        Ok(())
    }
}

impl fmt::Display for LabeledPLTL {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LabeledPLTL::Top => write!(f, "⊤"),
            LabeledPLTL::Bottom => write!(f, "⊥"),
            LabeledPLTL::Atom(label) => write!(f, "\"{}\"", label),
            LabeledPLTL::Unary(op, box content) => write!(f, "({} {})", op, content),
            LabeledPLTL::Binary(op, box left, box right) => {
                write!(f, "({} {} {})", left, op, right)
            }
            LabeledPLTL::PastSubformula(index, is_weak) => {
                write!(f, "<{}, 0b{:b}>", index, is_weak)
            }
        }
    }
}

impl LabeledPLTL {
    pub fn new_unary(op: UnaryOp, r: Self) -> Self {
        Self::Unary(op, Box::new(r))
    }

    pub fn new_binary(op: BinaryOp, l: Self, r: Self) -> Self {
        Self::Binary(op, Box::new(l), Box::new(r))
    }
}

impl BitAnd for LabeledPLTL {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::new_binary(BinaryOp::And, self, rhs)
    }
}

impl BitOr for LabeledPLTL {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::new_binary(BinaryOp::Or, self, rhs)
    }
}

impl LabeledPLTL {
    fn from_pltl_impl<'a>(
        pltl: &'a PLTL,
        context: &mut Context<'a>,
    ) -> (LabeledPLTL, BitSet32, BitSet32) {
        match pltl {
            PLTL::Top => (LabeledPLTL::Top, BitSet32::default(), BitSet32::default()),
            PLTL::Bottom => (
                LabeledPLTL::Bottom,
                BitSet32::default(),
                BitSet32::default(),
            ),
            PLTL::Atom(label) => (
                LabeledPLTL::Atom(*label),
                BitSet32::default(),
                BitSet32::default(),
            ),
            PLTL::Unary(op @ (UnaryOp::Yesterday | UnaryOp::WeakYesterday), box content) => {
                let (inner_result, inner_psfs, inner_is_weak) =
                    Self::from_pltl_impl(content, context);
                let op_id = context
                    .past_subformulas
                    .iter()
                    .position(|&x| x == pltl)
                    .unwrap_or(context.past_subformulas.len()) as u32;
                let is_weak =
                    inner_is_weak | ((matches!(op, UnaryOp::WeakYesterday) as u32) << op_id);
                let result = LabeledPLTL::PastSubformula(op_id, is_weak);
                let psfs = inner_psfs | (1 << op_id);
                context
                    .initial_weaken_state
                    .set(op_id, matches!(op, UnaryOp::WeakYesterday));
                context.past_subformulas.push(pltl);
                context.past_subformula_contains.push(psfs);
                context
                    .expand_once
                    .push(LabeledPLTL::new_unary(*op, inner_result));
                (result, psfs, is_weak)
            }
            PLTL::Unary(op, subformula) => {
                let (inner_result, inner_psfs, inner_is_weak) =
                    Self::from_pltl_impl(subformula, context);
                (
                    LabeledPLTL::new_unary(*op, inner_result),
                    inner_psfs,
                    inner_is_weak,
                )
            }
            PLTL::Binary(
                op @ (BinaryOp::BackTo
                | BinaryOp::WeakBackTo
                | BinaryOp::Since
                | BinaryOp::WeakSince),
                box lhs,
                box rhs,
            ) => {
                let (lhs_result, lhs_psfs, lhs_is_weak) = Self::from_pltl_impl(lhs, context);
                let (rhs_result, rhs_psfs, rhs_is_weak) = Self::from_pltl_impl(rhs, context);
                let op_id = context
                    .past_subformulas
                    .iter()
                    .position(|&x| x == pltl)
                    .unwrap_or(context.past_subformulas.len()) as u32;
                let is_weak = lhs_is_weak
                    | rhs_is_weak
                    | ((matches!(op, BinaryOp::WeakBackTo | BinaryOp::WeakSince) as u32) << op_id);
                let result = LabeledPLTL::PastSubformula(op_id, is_weak);
                let psfs = lhs_psfs | rhs_psfs | (1 << op_id);
                context.initial_weaken_state.set(
                    op_id,
                    matches!(op, BinaryOp::WeakBackTo | BinaryOp::WeakSince),
                );
                context.past_subformulas.push(pltl);
                context.past_subformula_contains.push(psfs);
                context
                    .expand_once
                    .push(LabeledPLTL::new_binary(*op, lhs_result, rhs_result));
                (result, psfs, is_weak)
            }
            PLTL::Binary(op, left, right) => {
                let (lhs_result, lhs_psfs, lhs_is_weak) = Self::from_pltl_impl(left, context);
                let (rhs_result, rhs_psfs, rhs_is_weak) = Self::from_pltl_impl(right, context);
                (
                    LabeledPLTL::new_binary(*op, lhs_result, rhs_result),
                    lhs_psfs | rhs_psfs,
                    lhs_is_weak | rhs_is_weak,
                )
            }
        }
    }

    pub fn new<'a>(pltl: &'a PLTL) -> (Self, Context<'a>) {
        let mut context = Context::default();
        let (result, _, _) = Self::from_pltl_impl(pltl, &mut context);
        (result, context)
    }

    pub fn normalize(&mut self, ctx: &Context) {
        if let LabeledPLTL::PastSubformula(psf_id, weaken_state) = self {
            *weaken_state = ctx.past_subformula_contains[*psf_id as usize] & *weaken_state;
        }
    }
}

impl LabeledPLTL {
    pub fn format(&self, ctx: &Context, pltl_context: &pltl::Context) -> String {
        match self {
            LabeledPLTL::Top => "⊤".to_string(),
            LabeledPLTL::Bottom => "⊥".to_string(),
            LabeledPLTL::Atom(label) => pltl_context.atoms[*label as usize].to_string(),
            LabeledPLTL::Unary(op, box content) => {
                format!("({} {})", op, content.format(ctx, pltl_context))
            }
            LabeledPLTL::Binary(op, box left, box right) => format!(
                "({} {} {})",
                left.format(ctx, pltl_context),
                op,
                right.format(ctx, pltl_context)
            ),
            LabeledPLTL::PastSubformula(psf_id, weaken_state) => {
                let is_weak = weaken_state.get(*psf_id);
                match &ctx.expand_once[*psf_id as usize] {
                    LabeledPLTL::Unary(UnaryOp::Yesterday | UnaryOp::WeakYesterday, content) => {
                        format!("({} {})", if is_weak { "~Y" } else { "Y" }, content.format(ctx, pltl_context))
                    }
                    LabeledPLTL::Binary(BinaryOp::BackTo | BinaryOp::WeakBackTo, lhs, rhs) => {
                        format!("({} {} {})", lhs.format(ctx, pltl_context), if is_weak { "~B" } else { "B" }, rhs.format(ctx, pltl_context))
                    }
                    LabeledPLTL::Binary(BinaryOp::Since | BinaryOp::WeakSince, lhs, rhs) => {
                        format!("({} {} {})", lhs.format(ctx, pltl_context), if is_weak { "~S" } else { "S" }, rhs.format(ctx, pltl_context))
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}

impl<'a> Context<'a> {
    // Please make sure that the pltl is in the context
    pub fn to_labeled(&self, pltl: &'a PLTL) -> LabeledPLTL {
        match pltl {
            PLTL::Top => LabeledPLTL::Top,
            PLTL::Bottom => LabeledPLTL::Bottom,
            PLTL::Atom(label) => LabeledPLTL::Atom(*label),
            PLTL::Unary(UnaryOp::Yesterday | UnaryOp::WeakYesterday, _) => {
                let psf_id = self
                    .past_subformulas
                    .iter()
                    .position(|&x| ptr::eq(x, pltl))
                    .unwrap();
                LabeledPLTL::PastSubformula(
                    psf_id as u32,
                    self.initial_weaken_state & self.past_subformula_contains[psf_id],
                )
            }
            PLTL::Unary(op, subformula) => LabeledPLTL::new_unary(*op, self.to_labeled(subformula)),
            PLTL::Binary(
                BinaryOp::BackTo | BinaryOp::WeakBackTo | BinaryOp::Since | BinaryOp::WeakSince,
                _,
                _,
            ) => {
                let psf_id = self
                    .past_subformulas
                    .iter()
                    .position(|&x| ptr::eq(x, pltl))
                    .unwrap();
                LabeledPLTL::PastSubformula(
                    psf_id as u32,
                    self.initial_weaken_state & self.past_subformula_contains[psf_id],
                )
            }
            PLTL::Binary(op, left, right) => {
                LabeledPLTL::new_binary(*op, self.to_labeled(left), self.to_labeled(right))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let (pltl, ctx) = PLTL::from_string("(a S b) & (c B (a ~S b)) | Y a").unwrap();
        let (labeled_pltl, context) = LabeledPLTL::new(&pltl);
        println!("{}", ctx);
        println!("{}", context);
        println!("{}", labeled_pltl);
    }
}
