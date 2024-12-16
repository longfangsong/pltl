use std::{collections::HashSet, fmt};

mod parse;
pub use parse::parse;

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum BasicPLTL {
    Top,
    Bottom,
    Atom(String),
    Not(Box<BasicPLTL>),
    And(Box<BasicPLTL>, Box<BasicPLTL>),
    Or(Box<BasicPLTL>, Box<BasicPLTL>),
    Next(Box<BasicPLTL>),
    Until(Box<BasicPLTL>, Box<BasicPLTL>),
    Yesterday(Box<BasicPLTL>),
    Since(Box<BasicPLTL>, Box<BasicPLTL>),
}

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum PLTL {
    // Basic part
    Top,
    Bottom,
    Atom(String),
    Not(Box<PLTL>),
    And(Box<PLTL>, Box<PLTL>),
    Or(Box<PLTL>, Box<PLTL>),
    Next(Box<PLTL>),
    Until(Box<PLTL>, Box<PLTL>),
    Yesterday(Box<PLTL>),
    Since(Box<PLTL>, Box<PLTL>),
    // Extended part
    /// F ϕ
    Eventually(Box<PLTL>),
    /// O ϕ
    Once(Box<PLTL>),
    /// G ϕ
    Globally(Box<PLTL>),
    /// H ϕ
    Historically(Box<PLTL>),
    /// ϕ W ψ
    WeakUntil(Box<PLTL>, Box<PLTL>),
    /// ϕ ~S̃ ψ
    WeakSince(Box<PLTL>, Box<PLTL>),
    /// ϕ M ψ
    MightyRelease(Box<PLTL>, Box<PLTL>),
    /// ϕ B ψ
    Before(Box<PLTL>, Box<PLTL>),
    /// ϕ R ψ
    Release(Box<PLTL>, Box<PLTL>),
    /// ϕ ~B ψ
    WeakBefore(Box<PLTL>, Box<PLTL>),
    /// ~Y ϕ
    WeakYesterday(Box<PLTL>),
}

impl fmt::Display for PLTL {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PLTL::Top => write!(f, "⊤"),
            PLTL::Bottom => write!(f, "⊥"),
            PLTL::Atom(s) => write!(f, "{}", s),
            PLTL::Not(pltl) => write!(f, "¬{}", pltl),
            PLTL::And(pltl, pltl1) => write!(f, "{} ∧ {}", pltl, pltl1),
            PLTL::Or(pltl, pltl1) => write!(f, "{} ∨ {}", pltl, pltl1),
            PLTL::Next(pltl) => write!(f, "X {}", pltl),
            PLTL::Until(pltl, pltl1) => write!(f, "{} U {}", pltl, pltl1),
            PLTL::Yesterday(pltl) => write!(f, "Y {}", pltl),
            PLTL::Since(pltl, pltl1) => write!(f, "{} S {}", pltl, pltl1),
            PLTL::Eventually(pltl) => write!(f, "F {}", pltl),
            PLTL::Once(pltl) => write!(f, "O {}", pltl),
            PLTL::Globally(pltl) => write!(f, "G {}", pltl),
            PLTL::Historically(pltl) => write!(f, "H {}", pltl),
            PLTL::WeakUntil(pltl, pltl1) => write!(f, "{} W {}", pltl, pltl1),
            PLTL::WeakSince(pltl, pltl1) => write!(f, "{} ~S {}", pltl, pltl1),
            PLTL::MightyRelease(pltl, pltl1) => write!(f, "{} M {}", pltl, pltl1),
            PLTL::Before(pltl, pltl1) => write!(f, "{} B {}", pltl, pltl1),
            PLTL::Release(pltl, pltl1) => write!(f, "{} R {}", pltl, pltl1),
            PLTL::WeakBefore(pltl, pltl1) => write!(f, "{} ~B {}", pltl, pltl1),
            PLTL::WeakYesterday(pltl) => write!(f, "~Y {}", pltl),
        }
    }
}

impl From<BasicPLTL> for PLTL {
    fn from(basic: BasicPLTL) -> Self {
        match basic {
            BasicPLTL::Top => PLTL::Top,
            BasicPLTL::Bottom => PLTL::Bottom,
            BasicPLTL::Atom(s) => PLTL::Atom(s),
            BasicPLTL::Not(box b) => PLTL::Not(Box::new(b.into())),
            BasicPLTL::And(box a, box b) => PLTL::And(Box::new(a.into()), Box::new(b.into())),
            BasicPLTL::Or(box a, box b) => PLTL::Or(Box::new(a.into()), Box::new(b.into())),
            BasicPLTL::Next(box b) => PLTL::Next(Box::new(b.into())),
            BasicPLTL::Until(box a, box b) => PLTL::Until(Box::new(a.into()), Box::new(b.into())),
            BasicPLTL::Yesterday(box b) => PLTL::Yesterday(Box::new(b.into())),
            BasicPLTL::Since(box a, box b) => PLTL::Since(Box::new(a.into()), Box::new(b.into())),
        }
    }
}

fn not_normal_form(inner: &PLTL) -> PLTL {
    match inner {
        PLTL::Top => PLTL::Bottom,
        PLTL::Bottom => PLTL::Top,
        PLTL::Atom(x) => PLTL::Not(Box::new(PLTL::Atom(x.clone()))),
        PLTL::Not(pltl) => pltl.normal_form(),
        PLTL::And(lhs, rhs) => PLTL::Or(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::Or(lhs, rhs) => PLTL::And(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::Next(pltl) => PLTL::Next(Box::new(PLTL::Not(pltl.clone()))).normal_form(),
        PLTL::Until(lhs, rhs) => PLTL::Release(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::Yesterday(pltl) => {
            PLTL::WeakYesterday(Box::new(PLTL::Not(pltl.clone()))).normal_form()
        }
        PLTL::Since(lhs, rhs) => PLTL::WeakBefore(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::Eventually(pltl) => {
            PLTL::Not(Box::new(PLTL::Until(Box::new(PLTL::Top), pltl.clone()))).normal_form()
        }
        PLTL::Once(pltl) => {
            PLTL::Not(Box::new(PLTL::Since(Box::new(PLTL::Top), pltl.clone()))).normal_form()
        }
        PLTL::Globally(pltl) => PLTL::Eventually(Box::new(PLTL::Not(pltl.clone()))).normal_form(),
        PLTL::Historically(pltl) => PLTL::Once(Box::new(PLTL::Not(pltl.clone()))).normal_form(),
        PLTL::WeakUntil(lhs, rhs) => PLTL::MightyRelease(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::WeakSince(lhs, rhs) => PLTL::Before(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::MightyRelease(lhs, rhs) => PLTL::WeakUntil(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::Before(lhs, rhs) => PLTL::WeakSince(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::Release(lhs, rhs) => PLTL::Until(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::WeakBefore(lhs, rhs) => PLTL::Since(
            Box::new(PLTL::Not(lhs.clone())),
            Box::new(PLTL::Not(rhs.clone())),
        )
        .normal_form(),
        PLTL::WeakYesterday(pltl) => {
            PLTL::Yesterday(Box::new(PLTL::Not(pltl.clone()))).normal_form()
        }
    }
}

impl PLTL {
    pub fn subformulaes(&self) -> HashSet<PLTL> {
        let mut result = HashSet::new();
        result.insert(self.clone());
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => (),
            PLTL::Not(box pltl)
            | PLTL::Next(box pltl)
            | PLTL::Yesterday(box pltl)
            | PLTL::Eventually(box pltl)
            | PLTL::Once(box pltl)
            | PLTL::Globally(box pltl)
            | PLTL::Historically(box pltl)
            | PLTL::WeakYesterday(box pltl) => {
                result.insert(pltl.clone());
            }
            PLTL::And(lhs, rhs)
            | PLTL::Or(lhs, rhs)
            | PLTL::Until(lhs, rhs)
            | PLTL::Since(lhs, rhs)
            | PLTL::WeakUntil(lhs, rhs)
            | PLTL::WeakSince(lhs, rhs)
            | PLTL::MightyRelease(lhs, rhs)
            | PLTL::Before(lhs, rhs)
            | PLTL::Release(lhs, rhs)
            | PLTL::WeakBefore(lhs, rhs) => {
                result = &result | &lhs.subformulaes();
                result = &result | &rhs.subformulaes();
            }
        }
        result
    }

    pub fn is_past_formula(&self) -> bool {
        matches!(
            self,
            PLTL::Yesterday(_)
                | PLTL::WeakYesterday(_)
                | PLTL::Since(_, _)
                | PLTL::WeakSince(_, _)
                | PLTL::Before(_, _)
                | PLTL::WeakBefore(_, _)
        )
    }

    pub fn past_subformulaes(&self) -> HashSet<PLTL> {
        self.subformulaes()
            .into_iter()
            .filter(|pltl| pltl.is_past_formula())
            .collect()
    }

    pub fn normal_form(&self) -> Self {
        match self {
            PLTL::Top => PLTL::Top,
            PLTL::Bottom => PLTL::Top,
            PLTL::Atom(x) => PLTL::Atom(x.clone()),
            PLTL::Not(box inner) => not_normal_form(inner),
            PLTL::And(box lhs, box rhs) => {
                PLTL::And(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::Or(box lhs, box rhs) => {
                PLTL::Or(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::Next(box pltl) => PLTL::Next(Box::new(pltl.normal_form())),
            PLTL::Until(box lhs, box rhs) => {
                PLTL::Until(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::Yesterday(box pltl) => PLTL::Yesterday(Box::new(pltl.normal_form())),
            PLTL::Since(box lhs, box rhs) => {
                PLTL::Since(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }

            PLTL::Eventually(pltl) => PLTL::Until(Box::new(PLTL::Top), pltl.clone()).normal_form(),
            PLTL::Once(pltl) => PLTL::Since(Box::new(PLTL::Top), pltl.clone()).normal_form(),
            PLTL::Globally(pltl) => PLTL::Not(Box::new(PLTL::Eventually(Box::new(PLTL::Not(
                pltl.clone(),
            )))))
            .normal_form(),
            PLTL::Historically(pltl) => {
                PLTL::Not(Box::new(PLTL::Once(Box::new(PLTL::Not(pltl.clone()))))).normal_form()
            }

            PLTL::WeakUntil(box lhs, box rhs) => {
                PLTL::WeakUntil(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::WeakSince(box lhs, box rhs) => {
                PLTL::WeakSince(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::MightyRelease(box lhs, box rhs) => {
                PLTL::MightyRelease(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::Before(box lhs, box rhs) => {
                PLTL::Before(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::Release(box lhs, box rhs) => {
                PLTL::Release(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::WeakBefore(box lhs, box rhs) => {
                PLTL::WeakBefore(Box::new(lhs.normal_form()), Box::new(rhs.normal_form()))
            }
            PLTL::WeakYesterday(box pltl) => PLTL::WeakYesterday(Box::new(pltl.normal_form())),
        }
    }

    pub fn weakening(&self) -> Self {
        match self {
            PLTL::Yesterday(pltl) => Self::WeakYesterday(pltl.clone()),
            PLTL::Since(lhs, rhs) => Self::WeakSince(lhs.clone(), rhs.clone()),
            PLTL::Before(lhs, rhs) => Self::WeakBefore(lhs.clone(), rhs.clone()),
            pltl => pltl.clone(),
        }
    }

    pub fn strengthening(&self) -> Self {
        match self {
            PLTL::WeakYesterday(pltl) => Self::Yesterday(pltl.clone()),
            PLTL::WeakSince(lhs, rhs) => Self::Since(lhs.clone(), rhs.clone()),
            PLTL::WeakBefore(lhs, rhs) => Self::Before(lhs.clone(), rhs.clone()),
            pltl => pltl.clone(),
        }
    }

    pub fn rewrite_under_sets(&self, set: &HashSet<PLTL>) -> Self {
        match self {
            PLTL::Top => PLTL::Top,
            PLTL::Bottom => PLTL::Bottom,
            PLTL::Atom(x) => PLTL::Atom(x.clone()),
            PLTL::Not(pltl) if set.contains(self) => {
                PLTL::Not(Box::new(pltl.rewrite_under_sets(set))).weakening()
            }
            PLTL::Not(pltl) => PLTL::Not(Box::new(pltl.rewrite_under_sets(set))).strengthening(),
            PLTL::Next(pltl) if set.contains(self) => {
                PLTL::Next(Box::new(pltl.rewrite_under_sets(set))).weakening()
            }
            PLTL::Next(pltl) => PLTL::Next(Box::new(pltl.rewrite_under_sets(set))).strengthening(),
            PLTL::Yesterday(pltl) if set.contains(self) => {
                PLTL::Yesterday(Box::new(pltl.rewrite_under_sets(set))).weakening()
            }
            PLTL::Yesterday(pltl) => {
                PLTL::Yesterday(Box::new(pltl.rewrite_under_sets(set))).strengthening()
            }
            PLTL::WeakYesterday(pltl) if set.contains(self) => {
                PLTL::WeakYesterday(Box::new(pltl.rewrite_under_sets(set))).weakening()
            }
            PLTL::WeakYesterday(pltl) => {
                PLTL::WeakYesterday(Box::new(pltl.rewrite_under_sets(set))).strengthening()
            }

            PLTL::And(lhs, rhs) if set.contains(&self) => PLTL::And(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::And(lhs, rhs) => PLTL::And(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::Or(lhs, rhs) if set.contains(&self) => PLTL::Or(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::Or(lhs, rhs) => PLTL::Or(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::Until(lhs, rhs) if set.contains(&self) => PLTL::Until(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::Until(lhs, rhs) => PLTL::Until(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::Since(lhs, rhs) if set.contains(&self) => PLTL::Since(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::Since(lhs, rhs) => PLTL::Since(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::WeakUntil(lhs, rhs) if set.contains(&self) => PLTL::WeakUntil(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::WeakUntil(lhs, rhs) => PLTL::WeakUntil(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::WeakSince(lhs, rhs) if set.contains(&self) => PLTL::WeakSince(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::WeakSince(lhs, rhs) => PLTL::WeakSince(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::MightyRelease(lhs, rhs) if set.contains(&self) => PLTL::MightyRelease(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::MightyRelease(lhs, rhs) => PLTL::MightyRelease(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::Before(lhs, rhs) if set.contains(&self) => PLTL::Before(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::Before(lhs, rhs) => PLTL::Before(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::Release(lhs, rhs) if set.contains(&self) => PLTL::Release(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::Release(lhs, rhs) => PLTL::Release(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),
            PLTL::WeakBefore(lhs, rhs) if set.contains(&self) => PLTL::WeakBefore(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .weakening(),
            PLTL::WeakBefore(lhs, rhs) => PLTL::WeakBefore(
                Box::new(lhs.rewrite_under_sets(set)),
                Box::new(rhs.rewrite_under_sets(set)),
            )
            .strengthening(),

            PLTL::Eventually(_) => unreachable!("Must be normal form"),
            PLTL::Once(_) => unreachable!("Must be normal form"),
            PLTL::Globally(_) => unreachable!("Must be normal form"),
            PLTL::Historically(_) => unreachable!("Must be normal form"),
        }
    }

    pub fn weakning_conditions(&self) -> Self {
        match self {
            PLTL::Yesterday(box pltl) => pltl.clone(),
            PLTL::Since(_, box rhs) => rhs.clone(),
            PLTL::Before(lhs, rhs) => PLTL::And(lhs.clone(), rhs.clone()),
            PLTL::WeakYesterday(box pltl) => pltl.clone(),
            PLTL::WeakSince(lhs, rhs) => PLTL::Or(lhs.clone(), rhs.clone()),
            PLTL::WeakBefore(_, box rhs) => rhs.clone(),
            _ => unreachable!("Must be past formula"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::parse::parse;

    #[test]
    fn test_normal_form() {
        let pltl = parse("(ψ∨ξ)").unwrap().1;
        println!("{}", pltl);
        println!("{}", pltl.normal_form());
        let pltl = parse("¬Oφ").unwrap().1;
        println!("{}", pltl.normal_form());
    }

    #[test]
    fn test_rewrite_under_sets() {
        let pltl_code = "Y(p ~S q)";
        let phi = parse(pltl_code).unwrap().1;
        let mut c = HashSet::new();
        c.insert(phi.clone());
        println!("{}", phi.rewrite_under_sets(&c));

        let mut c = HashSet::new();
        c.insert(parse("p ~S q").unwrap().1);
        println!("{}", phi.rewrite_under_sets(&c));
    }

    #[test]
    fn test_weakning_conditions() {
        let pltl_code = "p S q";
        let phi = parse(pltl_code).unwrap().1;
        println!("{}", phi.weakning_conditions());

        let pltl_code = "p ~S q";
        let phi = parse(pltl_code).unwrap().1;
        println!("{}", phi.weakning_conditions());
    }
}
