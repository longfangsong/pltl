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
        fn add_parentheses(expr: &LabeledPLTL) -> String {
            match expr {
                LabeledPLTL::Top
                | LabeledPLTL::Bottom
                | LabeledPLTL::Atom(_)
                | LabeledPLTL::Not(_)
                | LabeledPLTL::Yesterday { .. }
                | LabeledPLTL::Next(_) => expr.to_string(),
                LabeledPLTL::Logical(_, _)
                | LabeledPLTL::Until { .. }
                | LabeledPLTL::Release { .. }
                | LabeledPLTL::BinaryTemporal { .. } => format!("({expr})"),
            }
        }
        match self {
            LabeledPLTL::Top => write!(f, "⊤"),
            LabeledPLTL::Bottom => write!(f, "⊥"),
            LabeledPLTL::Atom(label) => write!(f, "\"{label}\""),
            LabeledPLTL::Not(label) => write!(f, "¬\"{label}\""),
            LabeledPLTL::Yesterday { weak, content, .. } => {
                let content_str = add_parentheses(content);
                write!(f, "{}Y{content_str}", if *weak { "~" } else { "" })
            }
            LabeledPLTL::Next(labeled_pltl) => {
                let content_str = add_parentheses(labeled_pltl);
                write!(f, "X{content_str}")
            }
            LabeledPLTL::Logical(binary_op, content) => {
                write!(
                    f,
                    "{}",
                    content
                        .iter()
                        .map(add_parentheses)
                        .collect::<Vec<_>>()
                        .join(format!(" {binary_op} ").as_str())
                )
            }
            LabeledPLTL::Until { weak, lhs, rhs } => {
                let lhs_str = add_parentheses(lhs);
                let rhs_str = add_parentheses(rhs);
                write!(f, "{lhs_str} {} {rhs_str}", if *weak { "W" } else { "U" })
            }
            LabeledPLTL::Release { weak, lhs, rhs } => {
                let lhs_str = add_parentheses(lhs);
                let rhs_str = add_parentheses(rhs);
                write!(f, "{lhs_str} {} {rhs_str}", if *weak { "R" } else { "M" })
            }
            LabeledPLTL::BinaryTemporal {
                op, weak, lhs, rhs, ..
            } => {
                let lhs_str = add_parentheses(lhs);
                let rhs_str = add_parentheses(rhs);
                write!(
                    f,
                    "{lhs_str} {}{} {rhs_str}",
                    if *weak { "~" } else { "" },
                    op.strengthen()
                )
            }
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
                        // println!("pltl: {pltl}, x: {x}, lhs_result: {lhs_result}, rhs_result: {rhs_result}, lhs: {lhs}, rhs: {rhs}");
                        if let LabeledPLTL::BinaryTemporal {
                            op: x_op,
                            weak,
                            lhs,
                            rhs,
                            ..
                        } = x
                            && op.strengthen() == x_op.strengthen()
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

    pub fn format_with_parentheses(&self, pltl_ctx: &pltl::Context) -> String {
        match self {
            LabeledPLTL::Top
            | LabeledPLTL::Bottom
            | LabeledPLTL::Atom(_)
            | LabeledPLTL::Not(_)
            | LabeledPLTL::Yesterday { .. }
            | LabeledPLTL::Next(_) => self.format(pltl_ctx),
            LabeledPLTL::Logical(_, _)
            | LabeledPLTL::Until { .. }
            | LabeledPLTL::Release { .. }
            | LabeledPLTL::BinaryTemporal { .. } => format!("({})", self.format(pltl_ctx)),
        }
    }

    pub fn format(&self, pltl_ctx: &pltl::Context) -> String {
        match self {
            LabeledPLTL::Top => "⊤".to_string(),
            LabeledPLTL::Bottom => "⊥".to_string(),
            LabeledPLTL::Atom(label) => pltl_ctx.atoms[*label as usize].clone(),
            LabeledPLTL::Not(label) => format!("¬{}", &pltl_ctx.atoms[*label as usize]),
            LabeledPLTL::Yesterday { weak, content, .. } => {
                format!(
                    "{}Y {}",
                    if *weak { "~" } else { "" },
                    content.format_with_parentheses(pltl_ctx)
                )
            }
            LabeledPLTL::Next(labeled_pltl) => {
                format!("X {}", labeled_pltl.format_with_parentheses(pltl_ctx))
            }
            LabeledPLTL::Logical(binary_op, content) => content
                .iter()
                .map(|x| x.format_with_parentheses(pltl_ctx))
                .collect::<Vec<_>>()
                .join(format!(" {binary_op} ").as_str())
                .to_string(),
            LabeledPLTL::Until { weak, lhs, rhs } => {
                let lhs_str = lhs.format_with_parentheses(pltl_ctx);
                let rhs_str = rhs.format_with_parentheses(pltl_ctx);
                format!("{} {} {}", lhs_str, if *weak { "W" } else { "U" }, rhs_str)
            }
            LabeledPLTL::Release { weak, lhs, rhs } => {
                let lhs_str = lhs.format_with_parentheses(pltl_ctx);
                let rhs_str = rhs.format_with_parentheses(pltl_ctx);
                format!("{} {} {}", lhs_str, if *weak { "R" } else { "M" }, rhs_str)
            }
            LabeledPLTL::BinaryTemporal {
                op, weak, lhs, rhs, ..
            } => {
                let lhs_str = lhs.format_with_parentheses(pltl_ctx);
                let rhs_str = rhs.format_with_parentheses(pltl_ctx);
                format!("{} {} {}", lhs_str, op.with_weaken_state(*weak), rhs_str)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StructureDiff {
    Different,
    TotallySame,
    StructureSame(Vec<(u32, u32)>),
}

impl LabeledPLTL {
    pub fn same_structure(&self, other: &Self) -> bool {
        match (self, other) {
            (LabeledPLTL::Top, LabeledPLTL::Top) => true,
            (LabeledPLTL::Bottom, LabeledPLTL::Bottom) => true,
            (LabeledPLTL::Atom(label), LabeledPLTL::Atom(other_label)) => label == other_label,
            (LabeledPLTL::Not(label), LabeledPLTL::Not(other_label)) => label == other_label,
            (
                LabeledPLTL::Yesterday { content, .. },
                LabeledPLTL::Yesterday {
                    content: other_content,
                    ..
                },
            ) => content.same_structure(other_content),
            (LabeledPLTL::Next(content), LabeledPLTL::Next(other_content)) => {
                content.same_structure(other_content)
            }
            (LabeledPLTL::Logical(op, content), LabeledPLTL::Logical(other_op, other_content)) => {
                op == other_op
                    && content
                        .iter()
                        .zip(other_content.iter())
                        .all(|(x, y)| x.same_structure(y))
            }
            (
                LabeledPLTL::Until { lhs, rhs, .. },
                LabeledPLTL::Until {
                    lhs: other_lhs,
                    rhs: other_rhs,
                    ..
                },
            ) => lhs.same_structure(other_lhs) && rhs.same_structure(other_rhs),
            (
                LabeledPLTL::Release { lhs, rhs, .. },
                LabeledPLTL::Release {
                    lhs: other_lhs,
                    rhs: other_rhs,
                    ..
                },
            ) => lhs.same_structure(other_lhs) && rhs.same_structure(other_rhs),
            (
                LabeledPLTL::BinaryTemporal { lhs, rhs, .. },
                LabeledPLTL::BinaryTemporal {
                    lhs: other_lhs,
                    rhs: other_rhs,
                    ..
                },
            ) => lhs.same_structure(other_lhs) && rhs.same_structure(other_rhs),
            _ => false,
        }
    }

    pub fn structure_diff(&self, other: &Self) -> StructureDiff {
        match (self, other) {
            (LabeledPLTL::Top, LabeledPLTL::Top) => StructureDiff::TotallySame,
            (LabeledPLTL::Bottom, LabeledPLTL::Bottom) => StructureDiff::TotallySame,
            (LabeledPLTL::Atom(label), LabeledPLTL::Atom(other_label)) => {
                if label == other_label {
                    StructureDiff::TotallySame
                } else {
                    StructureDiff::Different
                }
            }
            (LabeledPLTL::Not(label), LabeledPLTL::Not(other_label)) => {
                if label == other_label {
                    StructureDiff::TotallySame
                } else {
                    StructureDiff::Different
                }
            }
            (
                LabeledPLTL::Yesterday {
                    id, weak, content, ..
                },
                LabeledPLTL::Yesterday {
                    id: other_id,
                    content: other_content,
                    weak: other_weak,
                    ..
                },
            ) => {
                if *id == *other_id {
                    StructureDiff::TotallySame
                } else {
                    match content.structure_diff(other_content) {
                        StructureDiff::Different => StructureDiff::Different,
                        StructureDiff::TotallySame => {
                            if *weak == *other_weak {
                                StructureDiff::TotallySame
                            } else {
                                StructureDiff::StructureSame(vec![(*id, *other_id)])
                            }
                        }
                        StructureDiff::StructureSame(mut items) => {
                            if *weak != *other_weak {
                                items.push((*id, *other_id));
                            }
                            StructureDiff::StructureSame(items)
                        }
                    }
                }
            }
            (LabeledPLTL::Next(content), LabeledPLTL::Next(other_content)) => {
                content.structure_diff(other_content)
            }
            (LabeledPLTL::Logical(op, content), LabeledPLTL::Logical(other_op, other_content)) => {
                if op == other_op && content.len() == other_content.len() {
                    let mut result = vec![];
                    for (item, other_item) in content.iter().zip(other_content.iter()) {
                        match item.structure_diff(other_item) {
                            StructureDiff::Different => return StructureDiff::Different,
                            StructureDiff::TotallySame => (),
                            StructureDiff::StructureSame(items) => {
                                // currently we keep the first structure same
                                result.extend(items);
                                break;
                            }
                        }
                    }
                    if result.is_empty() {
                        StructureDiff::TotallySame
                    } else {
                        StructureDiff::StructureSame(result)
                    }
                } else {
                    StructureDiff::Different
                }
            }
            (
                LabeledPLTL::Until {
                    lhs,
                    rhs,
                    weak: lhs_weak,
                },
                LabeledPLTL::Until {
                    lhs: other_lhs,
                    rhs: other_rhs,
                    weak: rhs_weak,
                },
            )
            | (
                LabeledPLTL::Release {
                    lhs,
                    rhs,
                    weak: lhs_weak,
                },
                LabeledPLTL::Release {
                    lhs: other_lhs,
                    rhs: other_rhs,
                    weak: rhs_weak,
                },
            ) if lhs_weak == rhs_weak => {
                match (lhs.structure_diff(other_lhs), rhs.structure_diff(other_rhs)) {
                    (StructureDiff::Different, _) | (_, StructureDiff::Different) => {
                        StructureDiff::Different
                    }
                    (StructureDiff::TotallySame, StructureDiff::TotallySame) => {
                        StructureDiff::TotallySame
                    }
                    (StructureDiff::TotallySame, StructureDiff::StructureSame(items))
                    | (StructureDiff::StructureSame(items), StructureDiff::TotallySame) => {
                        StructureDiff::StructureSame(items)
                    }
                    (
                        StructureDiff::StructureSame(mut items),
                        StructureDiff::StructureSame(other_items),
                    ) => {
                        items.extend(other_items);
                        StructureDiff::StructureSame(items)
                    }
                }
            }
            (
                LabeledPLTL::BinaryTemporal {
                    op,
                    lhs,
                    rhs,
                    id,
                    weak,
                },
                LabeledPLTL::BinaryTemporal {
                    op: other_op,
                    lhs: other_lhs,
                    rhs: other_rhs,
                    id: other_id,
                    weak: other_weak,
                },
            ) if op.strengthen() == other_op.strengthen() => {
                if *id == *other_id {
                    StructureDiff::TotallySame
                } else {
                    match (lhs.structure_diff(other_lhs), rhs.structure_diff(other_rhs)) {
                        (StructureDiff::Different, _) | (_, StructureDiff::Different) => {
                            StructureDiff::Different
                        }
                        (StructureDiff::TotallySame, StructureDiff::TotallySame) => {
                            if *weak == *other_weak {
                                StructureDiff::TotallySame
                            } else {
                                StructureDiff::StructureSame(vec![(*id, *other_id)])
                            }
                        }
                        (StructureDiff::TotallySame, StructureDiff::StructureSame(mut items))
                        | (StructureDiff::StructureSame(mut items), StructureDiff::TotallySame) => {
                            if *weak != *other_weak {
                                items.push((*id, *other_id));
                            }
                            StructureDiff::StructureSame(items)
                        }
                        (
                            StructureDiff::StructureSame(mut items),
                            StructureDiff::StructureSame(other_items),
                        ) => {
                            items.extend(other_items);
                            if *weak != *other_weak {
                                items.push((*id, *other_id));
                            }
                            StructureDiff::StructureSame(items)
                        }
                    }
                }
            }
            _ => StructureDiff::Different,
        }
    }

    // equal without considering the id
    pub fn content_equal(&self, other: &Self) -> bool {
        match (self, other) {
            (LabeledPLTL::Top, LabeledPLTL::Top) => true,
            (LabeledPLTL::Bottom, LabeledPLTL::Bottom) => true,
            (LabeledPLTL::Atom(label), LabeledPLTL::Atom(other_label)) => label == other_label,
            (LabeledPLTL::Not(label), LabeledPLTL::Not(other_label)) => label == other_label,
            (
                LabeledPLTL::Yesterday { weak, content, .. },
                LabeledPLTL::Yesterday {
                    weak: other_weak,
                    content: other_content,
                    ..
                },
            ) => *weak == *other_weak && content.content_equal(other_content),
            (LabeledPLTL::Next(content), LabeledPLTL::Next(other_content)) => {
                content.content_equal(other_content)
            }
            (LabeledPLTL::Logical(op, content), LabeledPLTL::Logical(other_op, other_content)) => {
                op == other_op
                    && content
                        .iter()
                        .zip(other_content.iter())
                        .all(|(x, y)| x.content_equal(y))
            }
            (
                LabeledPLTL::Until {
                    lhs,
                    rhs,
                    weak: self_weak,
                },
                LabeledPLTL::Until {
                    lhs: other_lhs,
                    rhs: other_rhs,
                    weak: other_weak,
                },
            ) => {
                self_weak == other_weak
                    && lhs.content_equal(other_lhs)
                    && rhs.content_equal(other_rhs)
            }
            (
                LabeledPLTL::Release {
                    lhs,
                    rhs,
                    weak: self_weak,
                },
                LabeledPLTL::Release {
                    lhs: other_lhs,
                    rhs: other_rhs,
                    weak: other_weak,
                },
            ) => {
                self_weak == other_weak
                    && lhs.content_equal(other_lhs)
                    && rhs.content_equal(other_rhs)
            }
            (
                LabeledPLTL::BinaryTemporal {
                    lhs,
                    rhs,
                    weak: self_weak,
                    op: self_op,
                    ..
                },
                LabeledPLTL::BinaryTemporal {
                    lhs: other_lhs,
                    rhs: other_rhs,
                    weak: other_weak,
                    op: other_op,
                    ..
                },
            ) => {
                self_weak == other_weak
                    && self_op.strengthen() == other_op.strengthen()
                    && lhs.content_equal(other_lhs)
                    && rhs.content_equal(other_rhs)
            }
            _ => false,
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
