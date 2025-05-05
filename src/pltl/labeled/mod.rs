use crate::{pltl, utils::BitSet};
// use std::{
//     fmt,
//     ops::{BitAnd, BitOr},
//     ptr,
// };

// use crate::utils::{BitSet, BitSet32};

use std::{
    fmt,
    ops::{BitAnd, BitOr},
};

use itertools::Itertools;

use crate::utils::BitSet32;

use super::{BinaryOp, UnaryOp, PLTL};

pub mod after_function;
mod forms;
pub mod info;
mod rewrite;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LabeledPLTL {
    Top,
    Bottom,
    Atom(u32),
    Not(u32),
    Yesterday {
        id: u32,
        weak: bool,
        content: Box<LabeledPLTL>,
    },
    Next(Box<LabeledPLTL>),
    Logical(BinaryOp, Vec<LabeledPLTL>),
    Until {
        // U(0) or W(1)
        weak: bool,
        lhs: Box<LabeledPLTL>,
        rhs: Box<LabeledPLTL>,
    },
    Release {
        // M(0) or R(1)
        weak: bool,
        lhs: Box<LabeledPLTL>,
        rhs: Box<LabeledPLTL>,
    },
    BinaryTemporal {
        id: u32,
        op: BinaryOp,
        weak: bool,
        lhs: Box<LabeledPLTL>,
        rhs: Box<LabeledPLTL>,
    },
}

#[derive(Debug, Clone, Default)]
pub struct Context {
    pub past_subformulas: Vec<LabeledPLTL>,
    pub psf_containing_relation: Vec<BitSet32>,
}

impl fmt::Display for Context {
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
        let max_psf_containing_relation_width = self
            .psf_containing_relation
            .iter()
            .map(|x| x.to_string().len() + 2)
            .max()
            .unwrap_or(0)
            .max("psf_containing_relation".len());

        write!(f, "{:>width$}\t", "id", width = max_psf_id_width)?;
        write!(f, "{:>width$}\t", "psf_expanded", width = max_psf_width)?;
        writeln!(
            f,
            "{:>width$}\t",
            "psf_containing_relation",
            width = max_psf_containing_relation_width
        )?;
        for (i, psf) in self.past_subformulas.iter().enumerate() {
            write!(f, "{i:>max_psf_id_width$}\t")?;
            write!(f, "{:>width$}\t", psf.to_string(), width = max_psf_width)?;
            writeln!(
                f,
                "0b{:>width$b}\t",
                self.psf_containing_relation[i],
                width = max_psf_containing_relation_width - 2
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
            LabeledPLTL::Atom(label) => write!(f, "\"{label}\""),
            LabeledPLTL::Not(label) => write!(f, "(¬\"{label}\")"),
            LabeledPLTL::Yesterday { weak, content, .. } => {
                write!(f, "({}Y {content})", if *weak { "~" } else { "" })
            }
            LabeledPLTL::Next(labeled_pltl) => write!(f, "(X {labeled_pltl})"),
            LabeledPLTL::Logical(binary_op, content) => {
                write!(
                    f,
                    "({})",
                    content
                        .iter()
                        .map(|x| x.to_string())
                        .collect::<Vec<_>>()
                        .join(format!(" {binary_op} ").as_str())
                )
            }
            LabeledPLTL::Until { weak, lhs, rhs } => {
                write!(f, "({lhs} {} {rhs})", if *weak { "W" } else { "U" })
            }
            LabeledPLTL::Release { weak, lhs, rhs } => {
                write!(f, "({lhs} {} {rhs})", if *weak { "M" } else { "R" })
            }
            LabeledPLTL::BinaryTemporal {
                op, weak, lhs, rhs, ..
            } => write!(
                f,
                "({lhs} {}{} {rhs})",
                if *weak { "~" } else { "" },
                op.strengthen()
            ),
        }
    }
}

impl BitAnd for LabeledPLTL {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (
                LabeledPLTL::Logical(BinaryOp::And, mut lhs_content),
                LabeledPLTL::Logical(BinaryOp::And, rhs_content),
            ) => {
                lhs_content.extend(rhs_content);
                LabeledPLTL::Logical(BinaryOp::And, lhs_content)
            }
            (LabeledPLTL::Logical(BinaryOp::And, mut content), rhs) => {
                content.push(rhs);
                LabeledPLTL::Logical(BinaryOp::And, content)
            }
            (lhs, LabeledPLTL::Logical(BinaryOp::And, mut rhs_content)) => {
                rhs_content.push(lhs);
                LabeledPLTL::Logical(BinaryOp::And, rhs_content)
            }
            (lhs, rhs) => LabeledPLTL::Logical(BinaryOp::And, vec![lhs, rhs]),
        }
    }
}

impl BitOr for LabeledPLTL {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (
                LabeledPLTL::Logical(BinaryOp::Or, mut lhs_content),
                LabeledPLTL::Logical(BinaryOp::Or, rhs_content),
            ) => {
                lhs_content.extend(rhs_content);
                LabeledPLTL::Logical(BinaryOp::Or, lhs_content)
            }
            (LabeledPLTL::Logical(BinaryOp::Or, mut content), rhs) => {
                content.push(rhs);
                LabeledPLTL::Logical(BinaryOp::Or, content)
            }
            (lhs, LabeledPLTL::Logical(BinaryOp::Or, mut rhs_content)) => {
                rhs_content.push(lhs);
                LabeledPLTL::Logical(BinaryOp::Or, rhs_content)
            }
            (lhs, rhs) => LabeledPLTL::Logical(BinaryOp::Or, vec![lhs, rhs]),
        }
    }
}

impl LabeledPLTL {
    fn from_pltl_impl(pltl: &PLTL, context: &mut Context) -> (LabeledPLTL, BitSet32) {
        match pltl {
            PLTL::Top => (LabeledPLTL::Top, BitSet32::default()),
            PLTL::Bottom => (LabeledPLTL::Bottom, BitSet32::default()),
            PLTL::Atom(label) => (LabeledPLTL::Atom(*label), BitSet32::default()),
            PLTL::Unary(UnaryOp::Not, box PLTL::Atom(atom)) => {
                (LabeledPLTL::Not(*atom), BitSet32::default())
            }
            PLTL::Unary(UnaryOp::Not, _) => {
                unreachable!("Normalize should have been called before converting to LabeledPLTL");
            }
            PLTL::Unary(UnaryOp::Next, box content) => {
                let (inner_result, inner_psf_containing_relation) =
                    Self::from_pltl_impl(content, context);
                (
                    LabeledPLTL::Next(Box::new(inner_result)),
                    inner_psf_containing_relation,
                )
            }
            PLTL::Unary(op @ (UnaryOp::Yesterday | UnaryOp::WeakYesterday), box content) => {
                let is_weak = matches!(op, UnaryOp::WeakYesterday);
                let (inner_result, inner_psf_containing_relation) =
                    Self::from_pltl_impl(content, context);
                let (id, result) = context
                    .past_subformulas
                    .iter()
                    .find_position(|&x| {
                        if let LabeledPLTL::Yesterday { content, weak, .. } = x
                            && *weak == is_weak
                        {
                            &inner_result == content.as_ref()
                        } else {
                            false
                        }
                    })
                    .map(|(id, content)| (id as u32, content.clone()))
                    .unwrap_or_else(|| {
                        let id = context.past_subformulas.len() as u32;
                        let result = LabeledPLTL::Yesterday {
                            content: Box::new(inner_result),
                            weak: is_weak,
                            id,
                        };
                        context.past_subformulas.push(result.clone());
                        context
                            .psf_containing_relation
                            .push(inner_psf_containing_relation | (1 << id));
                        (id, result)
                    });
                let containing_relation = inner_psf_containing_relation | (1 << id);
                (result, containing_relation)
            }
            PLTL::Unary(_, _) => {
                unreachable!("Normalize should have been called before converting to LabeledPLTL");
            }
            PLTL::Binary(op @ (BinaryOp::And | BinaryOp::Or), box lhs, box rhs) => {
                let (lhs_result, lhs_psf_containing_relation) = Self::from_pltl_impl(lhs, context);
                let (rhs_result, rhs_psf_containing_relation) = Self::from_pltl_impl(rhs, context);
                (
                    LabeledPLTL::Logical(*op, vec![lhs_result, rhs_result]),
                    lhs_psf_containing_relation & rhs_psf_containing_relation,
                )
            }
            PLTL::Binary(op @ (BinaryOp::Until | BinaryOp::WeakUntil), box lhs, box rhs) => {
                let is_weak = matches!(op, BinaryOp::WeakUntil);
                let (lhs_result, lhs_psf_containing_relation) = Self::from_pltl_impl(lhs, context);
                let (rhs_result, rhs_psf_containing_relation) = Self::from_pltl_impl(rhs, context);
                let result = LabeledPLTL::Until {
                    weak: is_weak,
                    lhs: Box::new(lhs_result),
                    rhs: Box::new(rhs_result),
                };
                (
                    result,
                    lhs_psf_containing_relation | rhs_psf_containing_relation,
                )
            }
            PLTL::Binary(op @ (BinaryOp::Release | BinaryOp::MightyRelease), box lhs, box rhs) => {
                let is_weak = matches!(op, BinaryOp::Release);
                let (lhs_result, lhs_psf_containing_relation) = Self::from_pltl_impl(lhs, context);
                let (rhs_result, rhs_psf_containing_relation) = Self::from_pltl_impl(rhs, context);
                let result = LabeledPLTL::Release {
                    weak: is_weak,
                    lhs: Box::new(lhs_result),
                    rhs: Box::new(rhs_result),
                };
                (
                    result,
                    lhs_psf_containing_relation | rhs_psf_containing_relation,
                )
            }
            PLTL::Binary(
                op @ (BinaryOp::Since
                | BinaryOp::WeakSince
                | BinaryOp::BackTo
                | BinaryOp::WeakBackTo),
                box lhs,
                box rhs,
            ) => {
                let is_weak = matches!(op, BinaryOp::WeakSince | BinaryOp::WeakBackTo);
                let (lhs_result, lhs_psf_containing_relation) = Self::from_pltl_impl(lhs, context);
                let (rhs_result, rhs_psf_containing_relation) = Self::from_pltl_impl(rhs, context);
                let (id, result) = context
                    .past_subformulas
                    .iter()
                    .find_position(|&x| {
                        if let LabeledPLTL::BinaryTemporal {
                            op: x_op,
                            weak,
                            lhs,
                            rhs,
                            ..
                        } = x
                            && op == x_op
                            && *weak == is_weak
                        {
                            &lhs_result == lhs.as_ref() && &rhs_result == rhs.as_ref()
                        } else {
                            false
                        }
                    })
                    .map(|(id, content)| (id as u32, content.clone()))
                    .unwrap_or_else(|| {
                        let id = context.past_subformulas.len() as u32;
                        let result = LabeledPLTL::BinaryTemporal {
                            id,
                            op: op.strengthen(),
                            weak: is_weak,
                            lhs: Box::new(lhs_result),
                            rhs: Box::new(rhs_result),
                        };
                        context.past_subformulas.push(result.clone());
                        context.psf_containing_relation.push(
                            lhs_psf_containing_relation | rhs_psf_containing_relation | (1 << id),
                        );
                        (id, result)
                    });
                let containing_relation =
                    lhs_psf_containing_relation | rhs_psf_containing_relation | (1 << id);
                (result, containing_relation)
            }
        }
    }

    pub fn new(pltl: &PLTL) -> (Self, Context) {
        let mut context = Context::default();
        let (result, _) = Self::from_pltl_impl(pltl, &mut context);
        (result, context)
    }

    pub fn format(&self, pltl_ctx: &pltl::Context) -> String {
        match self {
            LabeledPLTL::Top => "⊤".to_string(),
            LabeledPLTL::Bottom => "⊥".to_string(),
            LabeledPLTL::Atom(label) => pltl_ctx.atoms[*label as usize].clone(),
            LabeledPLTL::Not(label) => format!("¬{}", &pltl_ctx.atoms[*label as usize]),
            LabeledPLTL::Yesterday { weak, content, .. } => {
                format!(
                    "{}Y ({})",
                    if *weak { "~" } else { "" },
                    content.format(pltl_ctx)
                )
            }
            LabeledPLTL::Next(labeled_pltl) => format!("X ({})", labeled_pltl.format(pltl_ctx)),
            LabeledPLTL::Logical(binary_op, content) => content
                .iter()
                .map(|x| x.format(pltl_ctx))
                .collect::<Vec<_>>()
                .join(format!(" {binary_op} ").as_str())
                .to_string(),
            LabeledPLTL::Until { weak, lhs, rhs } => {
                format!(
                    "({}) {} ({})",
                    lhs.format(pltl_ctx),
                    if *weak { "W" } else { "U" },
                    rhs.format(pltl_ctx)
                )
            }
            LabeledPLTL::Release { weak, lhs, rhs } => {
                format!(
                    "({}) {} ({})",
                    lhs.format(pltl_ctx),
                    if *weak { "M" } else { "R" },
                    rhs.format(pltl_ctx)
                )
            }
            LabeledPLTL::BinaryTemporal {
                op, weak, lhs, rhs, ..
            } => {
                format!(
                    "({}) {} ({})",
                    lhs.format(pltl_ctx),
                    op.with_weaken_state(*weak),
                    rhs.format(pltl_ctx)
                )
            }
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let (pltl, ctx) = PLTL::from_string("(a S b) & (c B (a ~S b)) | Y a | X (a S b)").unwrap();
        let (labeled_pltl, context) = LabeledPLTL::new(&pltl);
        println!("{ctx}");
        println!("{context}");
        println!("{labeled_pltl}");
        assert_eq!(context.past_subformulas.len(), 4);
        assert_eq!(
            context
                .past_subformulas
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>(),
            vec![
                r#"("0" S "1")"#,
                r#"("0" ~S "1")"#,
                r#"("2" B ("0" ~S "1"))"#,
                r#"(Y "0")"#
            ]
        );
        assert_eq!(
            labeled_pltl.to_string(),
            "((((\"0\" S \"1\") ∧ (\"2\" B (\"0\" ~S \"1\"))) ∨ (Y \"0\")) ∨ (X (\"0\" S \"1\")))"
        );
    }
}
