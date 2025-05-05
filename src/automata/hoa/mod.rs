pub mod body;
pub mod format;
pub mod header;
pub mod output;

use body::Body;
pub use body::State;
use format::{AcceptanceCondition, AcceptanceInfo, AcceptanceName, AliasName, StateConjunction};
use header::{Header, HeaderItem};
use itertools::Itertools;
use std::fmt::Display;

type Id = u32;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum AbstractLabelExpression {
    Boolean(bool),
    Integer(u16),
    Negated(Box<AbstractLabelExpression>),
    Conjunction(Vec<AbstractLabelExpression>),
    Disjunction(Vec<AbstractLabelExpression>),
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum LabelExpression {
    Abstract(AbstractLabelExpression),
}

/// Represents a parsed HOA automaton. It consists of a the version string,
/// a [`Header`] and a [`Body`].
/// The header contains all the information about the automaton (e.g. the number of states, the
/// acceptance condition, aliases etc.) and the body contains the actual transitions.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct HoaAutomaton {
    header: Header,
    body: Body,
}

/// Represents an acceptance condition as it is encoded in a HOA automaton.
pub type HoaAcceptance = (usize, AcceptanceCondition);

/// Stores information on aliases, it holds a vector of pairs of alias
/// names and label expression. This can be used to unalias an automaton.
pub type Aliases = Vec<(AliasName, LabelExpression)>;

impl HoaAutomaton {
    /// Adds the given state.
    pub fn add_state(&mut self, state: State) {
        self.body.push(state);
    }

    /// Returns the version of the HOA file.
    pub fn version(&self) -> String {
        self.header.get_version().expect("Version must be set!")
    }

    /// Returns the header of the HOA file.
    pub fn header(&self) -> &Header {
        &self.header
    }

    pub fn header_mut(&mut self) -> &mut Header {
        &mut self.header
    }

    /// Returns the body of the HOA file.
    pub fn body(&self) -> &Body {
        &self.body
    }

    pub fn body_mut(&mut self) -> &mut Body {
        &mut self.body
    }

    fn from_parsed((header, body): (Header, Body)) -> Self {
        Self::from_parts(header, body)
    }

    /// Creates a new HOA automaton from the given version, header and
    /// body. This function will also unalias the automaton.
    pub fn from_parts(header: Header, body: Body) -> Self {
        let mut out = Self { header, body };
        out.body.sort_by_key(|x| x.id());
        out
    }

    /// Verifies that the automaton is well-formed. This means that
    /// - the number of states is set correctly
    /// - all states are defined exactly once
    pub fn verify(&self) -> Result<(), String> {
        let mut errors = Vec::new();
        let mut states = Vec::new();
        for state in self.body().iter() {
            if states.contains(&state.id()) {
                errors.push(format!("State {} is defined more than once!", state.id()));
            }
            states.push(state.id());
        }
        if let Some(num_states) = self.num_states()
            && states.len() != num_states
        {
            errors.push(format!(
                "The number of states is set to {} but there are {} states!",
                num_states,
                states.len()
            ));
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.join("\n"))
        }
    }

    /// Returns the number of states in the automaton.
    pub fn num_states(&self) -> Option<usize> {
        debug_assert!(
            self.header()
                .iter()
                .filter(|item| matches!(item, HeaderItem::States(_)))
                .count()
                == 1,
            "The number of states must be set exactly once!"
        );
        self.header().iter().find_map(|item| match item {
            HeaderItem::States(id) => Some(*id as usize),
            _ => None,
        })
    }

    /// Returns the start states of the automaton.
    pub fn start(&self) -> Vec<&StateConjunction> {
        debug_assert!(
            self.header()
                .iter()
                .filter(|item| matches!(item, HeaderItem::Start(_)))
                .count()
                >= 1,
            "At least one initial state conjunction has to be present!"
        );
        self.header()
            .iter()
            .filter_map(|item| match item {
                HeaderItem::Start(start) => Some(start),
                _ => None,
            })
            .collect()
    }

    /// Returns the set of all atomic propositions in the automaton.
    pub fn aps(&self) -> &Vec<String> {
        let aps = self
            .header()
            .iter()
            .filter_map(|item| match item {
                HeaderItem::AP(ap) => Some(ap),
                _ => None,
            })
            .collect_vec();
        debug_assert!(aps.len() == 1, "There must be exactly one AP header!");
        aps.first().unwrap()
    }

    /// Counts the number of atomic propositions in the automaton.
    pub fn num_aps(&self) -> usize {
        self.aps().len()
    }

    /// Returns the acceptance condition of the automaton.
    pub fn acceptance(&self) -> HoaAcceptance {
        debug_assert!(
            self.header()
                .iter()
                .filter(|item| matches!(item, HeaderItem::Acceptance(..)))
                .count()
                == 1,
            "There must be exactly one Acceptance header!"
        );
        self.header()
            .iter()
            .find_map(|item| match item {
                HeaderItem::Acceptance(acceptance_sets, condition) => {
                    Some((*acceptance_sets as usize, condition.clone()))
                }
                _ => None,
            })
            .expect("Acceptance header is missing!")
    }

    /// Returns the aliases of the automaton.
    pub fn aliases(&self) -> Vec<(AliasName, AbstractLabelExpression)> {
        self.header()
            .iter()
            .filter_map(|item| match item {
                HeaderItem::Alias(name, expr) => Some((name.clone(), expr.clone())),
                _ => None,
            })
            .collect()
    }

    /// Returns the acceptance name of the automaton.
    pub fn acceptance_name(&self) -> Option<(&AcceptanceName, &Vec<AcceptanceInfo>)> {
        debug_assert!(
            self.header()
                .iter()
                .filter(|item| matches!(item, HeaderItem::AcceptanceName(..)))
                .count()
                == 1,
            "There must be exactly one AcceptanceName header!"
        );
        self.header().iter().find_map(|item| match item {
            HeaderItem::AcceptanceName(name, info) => Some((name, info)),
            _ => None,
        })
    }

    /// Adds a header item to the automaton.
    pub fn add_header_item(&mut self, item: HeaderItem) {
        self.header.push(item);
    }
}

impl Default for HoaAutomaton {
    fn default() -> Self {
        HoaAutomaton::from_parts(vec![HeaderItem::Version("v1".into())].into(), vec![].into())
    }
}

impl std::fmt::Display for AbstractLabelExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AbstractLabelExpression::Boolean(b) => match b {
                true => write!(f, "t"),
                false => write!(f, "f"),
            },
            AbstractLabelExpression::Integer(i) => write!(f, "{i}"),
            AbstractLabelExpression::Negated(expr) => {
                write!(f, "!{expr}")
            }
            AbstractLabelExpression::Conjunction(conjuncts) => {
                let mut it = conjuncts.iter();
                if let Some(first) = it.next() {
                    Display::fmt(first, f)?;
                }
                for succ in it {
                    write!(f, " & ")?;
                    Display::fmt(succ, f)?;
                }
                Ok(())
            }
            AbstractLabelExpression::Disjunction(disjuncts) => {
                let mut it = disjuncts.iter();
                if let Some(first) = it.next() {
                    Display::fmt(first, f)?;
                }
                for succ in it {
                    write!(f, " | ")?;
                    Display::fmt(succ, f)?;
                }
                Ok(())
            }
        }
    }
}

impl AbstractLabelExpression {
    pub fn format_with_vars(&self, vars: &[String]) -> String {
        match self {
            AbstractLabelExpression::Boolean(b) => b.to_string(),
            AbstractLabelExpression::Integer(i) => vars[*i as usize].clone(),
            AbstractLabelExpression::Negated(e) => format!("!{}", e.format_with_vars(vars)),
            AbstractLabelExpression::Conjunction(cs) => {
                cs.iter().map(|c| c.format_with_vars(vars)).join(" & ")
            }
            AbstractLabelExpression::Disjunction(ds) => {
                ds.iter().map(|c| c.format_with_vars(vars)).join(" | ")
            }
        }
    }
}
