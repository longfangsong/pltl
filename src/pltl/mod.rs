pub mod after_function;

mod forms;

#[cfg(not(target_arch = "wasm32"))]
mod ganerator;
mod info;
pub mod labeled;
mod parse;
mod rewrite;
pub mod utils;

use parse::PLTLParseTree;
use serde::{Deserialize, Serialize};
use std::{
    fmt,
    ops::{BitAnd, BitOr},
    str::FromStr,
};
use wasm_bindgen::prelude::*;

/// Represents a context accompanied with PLTL formulas.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Context {
    /// Atoms are represented with numbers in a [`PLTL`].
    /// Here holds the atoms in the context.
    /// So in [`PLTL`] are the indices of the atoms.
    pub atoms: Vec<String>,
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let atoms_len = self.atoms.len().to_string().len().max("id".len());
        let atom_max_width = self
            .atoms
            .iter()
            .map(|atom| atom.len())
            .max()
            .unwrap_or(0)
            .max("atom".len());
        writeln!(
            f,
            "{:iwidth$}\t{:awidth$}",
            "id",
            "atom",
            iwidth = atoms_len,
            awidth = atom_max_width
        )?;
        for (i, atom) in self.atoms.iter().enumerate() {
            writeln!(f, "{i:atoms_len$}\t{atom:atom_max_width$}")?;
        }
        Ok(())
    }
}

#[wasm_bindgen]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Hash, PartialOrd, Ord)]
pub enum UnaryOp {
    Not,
    Next,
    Yesterday,

    Eventually,
    Once,
    Globally,
    Historically,
    WeakYesterday,
}

impl UnaryOp {
    pub fn from_name(s: &str) -> UnaryOp {
        match s {
            "Not" => UnaryOp::Not,
            "Next" => UnaryOp::Next,
            "Yesterday" => UnaryOp::Yesterday,
            "Eventually" => UnaryOp::Eventually,
            "Once" => UnaryOp::Once,
            "Globally" => UnaryOp::Globally,
            "Historically" => UnaryOp::Historically,
            "WeakYesterday" => UnaryOp::WeakYesterday,
            _ => unreachable!(),
        }
    }

    pub fn latex(self) -> &'static str {
        match self {
            UnaryOp::Not => "¬",
            UnaryOp::Next => "X",
            UnaryOp::Yesterday => "Y",
            UnaryOp::Eventually => "F",
            UnaryOp::Once => "O",
            UnaryOp::Globally => "G",
            UnaryOp::Historically => "H",
            UnaryOp::WeakYesterday => "\\widetilde{Y}",
        }
    }

    pub fn all_variants() -> &'static [UnaryOp] {
        &[
            UnaryOp::Not,
            UnaryOp::Next,
            UnaryOp::Yesterday,
            UnaryOp::Eventually,
            UnaryOp::Once,
            UnaryOp::Globally,
            UnaryOp::Historically,
            UnaryOp::WeakYesterday,
        ]
    }

    pub fn set_weaken_state(&self, weaken_state: bool) -> Self {
        match (self, weaken_state) {
            (UnaryOp::Yesterday, true) => UnaryOp::WeakYesterday,
            (UnaryOp::WeakYesterday, false) => UnaryOp::Yesterday,
            _ => *self,
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Self::WeakYesterday = self {
            write!(f, "~Y")
        } else {
            write!(f, "{}", self.latex())
        }
    }
}

#[wasm_bindgen]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Hash, PartialOrd, Ord)]
pub enum BinaryOp {
    And,

    Until,
    Since,

    WeakUntil,
    WeakSince,
    MightyRelease,
    BackTo,
    Release,
    WeakBackTo,

    Or,
}

impl BinaryOp {
    pub fn from_name(s: &str) -> BinaryOp {
        match s {
            "And" => BinaryOp::And,
            "Or" => BinaryOp::Or,
            "Until" => BinaryOp::Until,
            "Since" => BinaryOp::Since,
            "WeakUntil" => BinaryOp::WeakUntil,
            "WeakSince" => BinaryOp::WeakSince,
            "MightyRelease" => BinaryOp::MightyRelease,
            "Before" => BinaryOp::BackTo,
            "Release" => BinaryOp::Release,
            "WeakBefore" => BinaryOp::WeakBackTo,
            _ => unreachable!(),
        }
    }

    pub fn latex(self) -> &'static str {
        match self {
            BinaryOp::And => "∧",
            BinaryOp::Or => "∨",
            BinaryOp::Until => "U",
            BinaryOp::Since => "S",
            BinaryOp::WeakUntil => "W",
            BinaryOp::WeakSince => "\\widetilde{S}",
            BinaryOp::MightyRelease => "M",
            BinaryOp::BackTo => "B",
            BinaryOp::Release => "R",
            BinaryOp::WeakBackTo => "\\widetilde{B}",
        }
    }

    pub fn all_variants() -> &'static [BinaryOp] {
        &[
            BinaryOp::And,
            BinaryOp::Or,
            BinaryOp::Until,
            BinaryOp::Since,
            BinaryOp::WeakUntil,
            BinaryOp::WeakSince,
            BinaryOp::MightyRelease,
            BinaryOp::BackTo,
            BinaryOp::Release,
            BinaryOp::WeakBackTo,
        ]
    }

    pub fn with_weaken_state(&self, weaken_state: bool) -> Self {
        match (self, weaken_state) {
            (BinaryOp::WeakSince | BinaryOp::Since, false) => BinaryOp::Since,
            (BinaryOp::WeakSince | BinaryOp::Since, true) => BinaryOp::WeakSince,
            (BinaryOp::WeakBackTo | BinaryOp::BackTo, false) => BinaryOp::BackTo,
            (BinaryOp::WeakBackTo | BinaryOp::BackTo, true) => BinaryOp::WeakBackTo,
            _ => *self,
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinaryOp::WeakSince => write!(f, "~S"),
            BinaryOp::WeakBackTo => write!(f, "~B"),
            _ => write!(f, "{}", self.latex()),
        }
    }
}

/// Represents a Linear Temporal Logic with Past (PLTL) formula.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash, PartialOrd, Ord, Default)]
pub enum PLTL {
    Top,
    #[default]
    Bottom,
    Atom(u32),
    Unary(UnaryOp, Box<PLTL>),
    Binary(BinaryOp, Box<PLTL>, Box<PLTL>),
}

impl BitAnd for PLTL {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        PLTL::new_binary(BinaryOp::And, self, rhs)
    }
}

impl BitOr for PLTL {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        PLTL::new_binary(BinaryOp::Or, self, rhs)
    }
}

// Parsing
impl PLTL {
    fn from_parse_tree(pltl: PLTLParseTree, atom_map: &mut Vec<String>) -> Self {
        match pltl {
            PLTLParseTree::Top => PLTL::Top,
            PLTLParseTree::Bottom => PLTL::Bottom,
            PLTLParseTree::Atom(s) => {
                if let Some(i) = atom_map.iter().position(|x| *x == s) {
                    PLTL::Atom(i as u32)
                } else {
                    atom_map.push(s);
                    PLTL::Atom(atom_map.len() as u32 - 1)
                }
            }
            PLTLParseTree::Unary(op, box content) => {
                PLTL::Unary(op, Box::new(Self::from_parse_tree(content, atom_map)))
            }
            PLTLParseTree::Binary(op, box lhs, box rhs) => PLTL::Binary(
                op,
                Box::new(Self::from_parse_tree(lhs, atom_map)),
                Box::new(Self::from_parse_tree(rhs, atom_map)),
            ),
        }
    }

    /// Parses a string into a PLTL formula.
    /// Also returns the context of the formula.
    pub fn from_string(s: &str) -> Result<(Self, Context), parse::Error> {
        let mut atom_map = Vec::new();
        let parse_tree = PLTLParseTree::from_str(s)?;
        let pltl = Self::from_parse_tree(parse_tree, &mut atom_map);
        Ok((pltl, Context { atoms: atom_map }))
    }

    #[cfg(test)]
    pub fn from_string_increment(s: &str, ctx: &mut Context) -> Self {
        use parse::ParserInput;

        let input = ParserInput::new(s);
        Self::from_parse_tree(parse::parse(input).unwrap().1, &mut ctx.atoms)
    }
}

// Constructors
impl PLTL {
    pub fn new_atom(s: u32) -> Self {
        Self::Atom(s)
    }

    pub fn new_unary(op: UnaryOp, r: Self) -> Self {
        Self::Unary(op, Box::new(r))
    }

    pub fn new_binary(op: BinaryOp, l: Self, r: Self) -> Self {
        Self::Binary(op, Box::new(l), Box::new(r))
    }
}

impl fmt::Display for PLTL {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PLTL::Top => write!(f, "⊤"),
            PLTL::Bottom => write!(f, "⊥"),
            PLTL::Atom(s) => write!(f, "\"{s}\""),
            PLTL::Unary(UnaryOp::Not, box content @ PLTL::Unary(UnaryOp::Not, _)) => {
                write!(f, "{}{}", UnaryOp::Not, content)
            }
            PLTL::Unary(op, box content @ PLTL::Binary(_, _, _)) => {
                write!(f, "{op}({content})")
            }
            PLTL::Unary(op, box content) => write!(f, "{op}{content}"),
            PLTL::Binary(op, box lhs, box rhs) => {
                let lhs = match (op, lhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => format!("{lhs}"),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => format!("{lhs}"),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({lhs})")
                    }
                    _ => format!("{lhs}"),
                };
                let rhs = match (op, rhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => format!("{rhs}"),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => format!("{rhs}"),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({rhs})")
                    }
                    _ => format!("{rhs}"),
                };
                write!(f, "{lhs} {op} {rhs}")
            }
        }
    }
}

// Output
impl PLTL {
    pub fn latex(&self, ctx: &Context) -> String {
        match self {
            PLTL::Top => "⊤".to_string(),
            PLTL::Bottom => "⊥".to_string(),
            PLTL::Atom(s) => ctx.atoms[*s as usize].clone(),
            PLTL::Unary(UnaryOp::Not, box content @ PLTL::Unary(UnaryOp::Not, _)) => {
                format!("{}{}", UnaryOp::Not.latex(), content.latex(ctx))
            }
            PLTL::Unary(op, box content @ PLTL::Binary(_, _, _)) => {
                format!("{}({})", op.latex(), content.latex(ctx))
            }
            PLTL::Unary(op, box content) => format!("{}{}", op.latex(), content.latex(ctx)),
            PLTL::Binary(op, box lhs, box rhs) => {
                let lhs = match (op, lhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => lhs.latex(ctx),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => lhs.latex(ctx),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", lhs.latex(ctx))
                    }
                    _ => lhs.latex(ctx),
                };
                let rhs = match (op, rhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => rhs.latex(ctx),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => rhs.latex(ctx),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", rhs.latex(ctx))
                    }
                    _ => rhs.latex(ctx),
                };
                format!("{} {} {}", lhs, op.latex(), rhs)
            }
        }
    }

    pub fn format_with_atom_names(&self, atom_map: &[String]) -> String {
        match self {
            PLTL::Top => "⊤".to_string(),
            PLTL::Bottom => "⊥".to_string(),
            PLTL::Atom(s) => atom_map[*s as usize].clone(),
            PLTL::Unary(UnaryOp::Not, box content @ PLTL::Unary(UnaryOp::Not, _)) => {
                format!(
                    "{}{}",
                    UnaryOp::Not,
                    content.format_with_atom_names(atom_map)
                )
            }
            PLTL::Unary(op, box content @ PLTL::Binary(_, _, _)) => {
                format!("{}({})", op, content.format_with_atom_names(atom_map))
            }
            PLTL::Unary(op, box content) => {
                format!("{}{}", op, content.format_with_atom_names(atom_map))
            }
            PLTL::Binary(op, box lhs, box rhs) => {
                let lhs = match (op, lhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => {
                        lhs.format_with_atom_names(atom_map).to_string()
                    }
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => {
                        lhs.format_with_atom_names(atom_map).to_string()
                    }
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", lhs.format_with_atom_names(atom_map))
                    }
                    _ => lhs.format_with_atom_names(atom_map).to_string(),
                };
                let rhs = match (op, rhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => {
                        rhs.format_with_atom_names(atom_map).to_string()
                    }
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => {
                        rhs.format_with_atom_names(atom_map).to_string()
                    }
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", rhs.format_with_atom_names(atom_map))
                    }
                    _ => rhs.format_with_atom_names(atom_map).to_string(),
                };
                format!("{lhs} {op} {rhs}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pltl::{parse::PLTLParseTree, BinaryOp, UnaryOp, PLTL};

    #[test]
    fn test_latex() {
        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::Until,
                PLTLParseTree::new_atom("a"),
                PLTLParseTree::new_unary(UnaryOp::Not, PLTLParseTree::new_atom("b")),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "a U ¬b");

        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::Until,
                PLTLParseTree::new_binary(
                    BinaryOp::Until,
                    PLTLParseTree::new_atom("a"),
                    PLTLParseTree::new_atom("b"),
                ),
                PLTLParseTree::new_atom("c"),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "(a U b) U c");

        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::And,
                PLTLParseTree::new_binary(
                    BinaryOp::And,
                    PLTLParseTree::new_atom("a"),
                    PLTLParseTree::new_atom("b"),
                ),
                PLTLParseTree::new_binary(
                    BinaryOp::And,
                    PLTLParseTree::new_atom("c"),
                    PLTLParseTree::new_atom("d"),
                ),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "a ∧ b ∧ c ∧ d");

        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::And,
                PLTLParseTree::new_binary(
                    BinaryOp::Or,
                    PLTLParseTree::new_atom("a"),
                    PLTLParseTree::new_atom("b"),
                ),
                PLTLParseTree::new_binary(
                    BinaryOp::And,
                    PLTLParseTree::new_atom("c"),
                    PLTLParseTree::new_atom("d"),
                ),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "(a ∨ b) ∧ c ∧ d");

        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::And,
                PLTLParseTree::new_binary(
                    BinaryOp::Or,
                    PLTLParseTree::new_atom("a"),
                    PLTLParseTree::new_atom("b"),
                ),
                PLTLParseTree::new_unary(
                    UnaryOp::Not,
                    PLTLParseTree::new_binary(
                        BinaryOp::And,
                        PLTLParseTree::new_atom("c"),
                        PLTLParseTree::new_atom("d"),
                    ),
                ),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "(a ∨ b) ∧ ¬(c ∧ d)");

        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::And,
                PLTLParseTree::new_unary(
                    UnaryOp::Next,
                    PLTLParseTree::new_binary(
                        BinaryOp::Or,
                        PLTLParseTree::new_atom("a"),
                        PLTLParseTree::new_atom("b"),
                    ),
                ),
                PLTLParseTree::new_unary(
                    UnaryOp::Yesterday,
                    PLTLParseTree::new_unary(
                        UnaryOp::Not,
                        PLTLParseTree::new_binary(
                            BinaryOp::And,
                            PLTLParseTree::new_atom("c"),
                            PLTLParseTree::new_atom("d"),
                        ),
                    ),
                ),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "X(a ∨ b) ∧ Y¬(c ∧ d)");

        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_unary(
                UnaryOp::Not,
                PLTLParseTree::new_unary(UnaryOp::Not, PLTLParseTree::Top),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "¬¬⊤");

        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::Or,
                PLTLParseTree::new_binary(
                    BinaryOp::And,
                    PLTLParseTree::Bottom,
                    PLTLParseTree::new_atom("a"),
                ),
                PLTLParseTree::new_atom("b"),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "(⊥ ∧ a) ∨ b");

        let mut ctx = Context::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::Or,
                PLTLParseTree::new_binary(
                    BinaryOp::Or,
                    PLTLParseTree::Bottom,
                    PLTLParseTree::new_atom("a"),
                ),
                PLTLParseTree::new_binary(
                    BinaryOp::Or,
                    PLTLParseTree::new_unary(UnaryOp::Next, PLTLParseTree::new_atom("b")),
                    PLTLParseTree::new_binary(
                        BinaryOp::Since,
                        PLTLParseTree::Bottom,
                        PLTLParseTree::new_atom("a"),
                    ),
                ),
            ),
            &mut ctx.atoms,
        );
        assert_eq!(ltl.latex(&ctx), "⊥ ∨ a ∨ Xb ∨ (⊥ S a)");
    }
}
