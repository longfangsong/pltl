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
pub use parse::parse;
pub use past_subformula::{PastSubformulaSet, PastSubformularSetContext};
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

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
    Atom(String),
    Unary(UnaryOp, Box<PLTL>),
    Binary(BinaryOp, Box<PLTL>, Box<PLTL>),
}

impl PLTL {
    pub fn new_atom(s: impl ToString) -> PLTL {
        PLTL::Atom(s.to_string())
    }

    pub fn new_unary(op: UnaryOp, r: PLTL) -> PLTL {
        PLTL::Unary(op, Box::new(r))
    }

    pub fn new_binary(op: BinaryOp, l: PLTL, r: PLTL) -> PLTL {
        PLTL::Binary(op, Box::new(l), Box::new(r))
    }

    pub fn latex(&self) -> String {
        match self {
            PLTL::Top => "⊤".to_string(),
            PLTL::Bottom => "⊥".to_string(),
            PLTL::Atom(s) => s.clone(),
            PLTL::Unary(UnaryOp::Not, box content @ PLTL::Unary(UnaryOp::Not, _)) => {
                format!("{}{}", UnaryOp::Not.latex(), content.latex())
            }
            PLTL::Unary(op, box content @ PLTL::Binary(_, _, _)) => {
                format!("{}({})", op.latex(), content.latex())
            }
            PLTL::Unary(op, box content) => format!("{}{}", op.latex(), content.latex()),
            PLTL::Binary(op, box lhs, box rhs) => {
                let lhs = match (op, lhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => lhs.latex(),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => lhs.latex(),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", lhs.latex())
                    }
                    _ => lhs.latex(),
                };
                let rhs = match (op, rhs) {
                    (BinaryOp::And, PLTL::Binary(BinaryOp::And, _, _)) => rhs.latex(),
                    (BinaryOp::Or, PLTL::Binary(BinaryOp::Or, _, _)) => rhs.latex(),
                    (_, PLTL::Binary(_, _, _)) => {
                        format!("({})", rhs.latex())
                    }
                    _ => rhs.latex(),
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
            PLTL::Atom(s) => write!(f, "{}", s),
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_latex() {
        let ltl = PLTL::new_binary(
            BinaryOp::Until,
            PLTL::new_atom("a"),
            PLTL::new_unary(UnaryOp::Not, PLTL::new_atom("b")),
        );
        assert_eq!(ltl.latex(), "a U ¬b");

        let ltl = PLTL::new_binary(
            BinaryOp::Until,
            PLTL::new_binary(BinaryOp::Until, PLTL::new_atom("a"), PLTL::new_atom("b")),
            PLTL::new_atom("c"),
        );
        assert_eq!(ltl.latex(), "(a U b) U c");

        let ltl = PLTL::new_binary(
            BinaryOp::And,
            PLTL::new_binary(BinaryOp::And, PLTL::new_atom("a"), PLTL::new_atom("b")),
            PLTL::new_binary(BinaryOp::And, PLTL::new_atom("c"), PLTL::new_atom("d")),
        );
        assert_eq!(ltl.latex(), "a ∧ b ∧ c ∧ d");

        let ltl = PLTL::new_binary(
            BinaryOp::And,
            PLTL::new_binary(BinaryOp::Or, PLTL::new_atom("a"), PLTL::new_atom("b")),
            PLTL::new_binary(BinaryOp::And, PLTL::new_atom("c"), PLTL::new_atom("d")),
        );
        assert_eq!(ltl.latex(), "(a ∨ b) ∧ c ∧ d");

        let ltl = PLTL::new_binary(
            BinaryOp::And,
            PLTL::new_binary(BinaryOp::Or, PLTL::new_atom("a"), PLTL::new_atom("b")),
            PLTL::new_unary(
                UnaryOp::Not,
                PLTL::new_binary(BinaryOp::And, PLTL::new_atom("c"), PLTL::new_atom("d")),
            ),
        );
        assert_eq!(ltl.latex(), "(a ∨ b) ∧ ¬(c ∧ d)");

        let ltl = PLTL::new_binary(
            BinaryOp::And,
            PLTL::new_unary(
                UnaryOp::Next,
                PLTL::new_binary(BinaryOp::Or, PLTL::new_atom("a"), PLTL::new_atom("b")),
            ),
            PLTL::new_unary(
                UnaryOp::Yesterday,
                PLTL::new_unary(
                    UnaryOp::Not,
                    PLTL::new_binary(BinaryOp::And, PLTL::new_atom("c"), PLTL::new_atom("d")),
                ),
            ),
        );
        assert_eq!(ltl.latex(), "X(a ∨ b) ∧ Y¬(c ∧ d)");

        let ltl = PLTL::new_unary(UnaryOp::Not, PLTL::new_unary(UnaryOp::Not, PLTL::Top));
        assert_eq!(ltl.latex(), "¬¬⊤");

        let ltl = PLTL::new_binary(
            BinaryOp::Or,
            PLTL::new_binary(BinaryOp::And, PLTL::Bottom, PLTL::new_atom("a")),
            PLTL::new_atom("b"),
        );
        assert_eq!(ltl.latex(), "(⊥ ∧ a) ∨ b");

        let ltl = PLTL::new_binary(
            BinaryOp::Or,
            PLTL::new_binary(BinaryOp::Or, PLTL::Bottom, PLTL::new_atom("a")),
            PLTL::new_binary(
                BinaryOp::Or,
                PLTL::new_unary(UnaryOp::Next, PLTL::new_atom("b")),
                PLTL::new_binary(BinaryOp::Since, PLTL::Bottom, PLTL::new_atom("a")),
            ),
        );
        assert_eq!(ltl.latex(), "⊥ ∨ a ∨ Xb ∨ (⊥ S a)");
    }
}
