pub mod after_function;
mod annotated;
pub mod forms;
mod info;
mod parse;
mod past_subformula;
mod rewrite;
pub mod utils;
use std::fmt;

pub use annotated::Annotated;
use parse::{parse, PLTLParseTree};
pub use past_subformula::{PastSubformulaSet, PastSubformularSetContext};
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use crate::utils::BiMap;

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
    Before,
    Release,
    WeakBefore,

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
            "Before" => BinaryOp::Before,
            "Release" => BinaryOp::Release,
            "WeakBefore" => BinaryOp::WeakBefore,
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
            BinaryOp::Before => "B",
            BinaryOp::Release => "R",
            BinaryOp::WeakBefore => "\\widetilde{B}",
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
            BinaryOp::Before,
            BinaryOp::Release,
            BinaryOp::WeakBefore,
        ]
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinaryOp::WeakSince => write!(f, "~S"),
            BinaryOp::WeakBefore => write!(f, "~B"),
            _ => write!(f, "{}", self.latex()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash, PartialOrd, Ord)]
pub enum PLTL {
    Top,
    Bottom,
    Atom(u32),
    Unary(UnaryOp, Box<PLTL>),
    Binary(BinaryOp, Box<PLTL>, Box<PLTL>),
}

impl PLTL {
    fn from_parse_tree(pltl: PLTLParseTree, atom_map: &mut BiMap<String, u32>) -> Self {
        match pltl {
            PLTLParseTree::Top => PLTL::Top,
            PLTLParseTree::Bottom => PLTL::Bottom,
            PLTLParseTree::Atom(s) => {
                if let Some(i) = atom_map.get_by_left(&s) {
                    PLTL::Atom(*i)
                } else {
                    atom_map.insert(s, atom_map.len() as u32);
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

    pub fn from_string(s: &str) -> (Self, BiMap<String, u32>) {
        let mut atom_map = BiMap::default();
        let pltl = Self::from_parse_tree(parse(s).unwrap().1, &mut atom_map);
        (pltl, atom_map)
    }

    #[cfg(test)]
    pub fn from_string_increment(s: &str, atom_map: &mut BiMap<String, u32>) -> Self {
        Self::from_parse_tree(parse(s).unwrap().1, atom_map)
    }

    pub fn new_atom(s: u32) -> Self {
        Self::Atom(s)
    }

    pub fn atom_with_name(s: &str, atom_map: &BiMap<String, u32>) -> Self {
        if let Some(i) = atom_map.get_by_left(s) {
            Self::Atom(*i)
        } else {
            panic!("Atom {} not found in atom map", s);
        }
    }

    pub fn new_unary(op: UnaryOp, r: Self) -> Self {
        Self::Unary(op, Box::new(r))
    }

    pub fn new_binary(op: BinaryOp, l: Self, r: Self) -> Self {
        Self::Binary(op, Box::new(l), Box::new(r))
    }
}

impl PLTL {
    pub fn latex(&self, atom_map: &BiMap<String, u32>) -> String {
        match self {
            PLTL::Top => "⊤".to_string(),
            PLTL::Bottom => "⊥".to_string(),
            PLTL::Atom(s) => atom_map.get_by_right(s).unwrap().to_string(),
            PLTL::Unary(UnaryOp::Not, box content @ PLTL::Unary(UnaryOp::Not, _)) => {
                format!("{}{}", UnaryOp::Not.latex(), content.latex(atom_map))
            }
            PLTL::Unary(op, box content @ PLTL::Binary(_, _, _)) => {
                format!("{}({})", op.latex(), content.latex(atom_map))
            }
            PLTL::Unary(op, box content) => format!("{}{}", op.latex(), content.latex(atom_map)),
            PLTL::Binary(op, box lhs, box rhs) => {
                let lhs = match (op, lhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => lhs.latex(atom_map),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => lhs.latex(atom_map),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", lhs.latex(atom_map))
                    }
                    _ => lhs.latex(atom_map),
                };
                let rhs = match (op, rhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => rhs.latex(atom_map),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => rhs.latex(atom_map),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", rhs.latex(atom_map))
                    }
                    _ => rhs.latex(atom_map),
                };
                format!("{} {} {}", lhs, op.latex(), rhs)
            }
        }
    }

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

impl fmt::Display for PLTL {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PLTL::Top => write!(f, "⊤"),
            PLTL::Bottom => write!(f, "⊥"),
            PLTL::Atom(s) => write!(f, "\"{}\"", s),
            PLTL::Unary(UnaryOp::Not, box content @ PLTL::Unary(UnaryOp::Not, _)) => {
                write!(f, "{}{}", UnaryOp::Not, content)
            }
            PLTL::Unary(op, box content @ PLTL::Binary(_, _, _)) => {
                write!(f, "{}({})", op, content)
            }
            PLTL::Unary(op, box content) => write!(f, "{}{}", op, content),
            PLTL::Binary(op, box lhs, box rhs) => {
                let lhs = match (op, lhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => format!("{}", lhs),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => format!("{}", lhs),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", lhs)
                    }
                    _ => format!("{}", lhs),
                };
                let rhs = match (op, rhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => format!("{}", rhs),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => format!("{}", rhs),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", rhs)
                    }
                    _ => format!("{}", rhs),
                };
                write!(f, "{} {} {}", lhs, op, rhs)
            }
        }
    }
}

impl PLTL {
    pub fn format_with_atom_names(&self, atom_map: &BiMap<String, u32>) -> String {
        match self {
            PLTL::Top => "⊤".to_string(),
            PLTL::Bottom => "⊥".to_string(),
            PLTL::Atom(s) => atom_map.get_by_right(s).unwrap().to_string(),
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
                format!("{} {} {}", lhs, op, rhs)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        pltl::{parse::PLTLParseTree, BinaryOp, UnaryOp, PLTL},
        utils::BiMap,
    };

    #[test]
    fn test_latex() {
        let mut atom_map = BiMap::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_binary(
                BinaryOp::Until,
                PLTLParseTree::new_atom("a"),
                PLTLParseTree::new_unary(UnaryOp::Not, PLTLParseTree::new_atom("b")),
            ),
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "a U ¬b");

        let mut atom_map = BiMap::default();
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
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "(a U b) U c");

        let mut atom_map = BiMap::default();
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
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "a ∧ b ∧ c ∧ d");

        let mut atom_map = BiMap::default();
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
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "(a ∨ b) ∧ c ∧ d");

        let mut atom_map = BiMap::default();
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
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "(a ∨ b) ∧ ¬(c ∧ d)");

        let mut atom_map = BiMap::default();
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
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "X(a ∨ b) ∧ Y¬(c ∧ d)");

        let mut atom_map = BiMap::default();
        let ltl = PLTL::from_parse_tree(
            PLTLParseTree::new_unary(
                UnaryOp::Not,
                PLTLParseTree::new_unary(UnaryOp::Not, PLTLParseTree::Top),
            ),
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "¬¬⊤");

        let mut atom_map = BiMap::default();
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
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "(⊥ ∧ a) ∨ b");

        let mut atom_map = BiMap::default();
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
            &mut atom_map,
        );
        assert_eq!(ltl.latex(&atom_map), "⊥ ∨ a ∨ Xb ∨ (⊥ S a)");
    }
}
