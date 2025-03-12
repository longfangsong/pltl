use std::ops::{Deref, DerefMut};

use super::{format::{AcceptanceCondition, AcceptanceInfo, AcceptanceName, AliasName, AtomicProposition, Property, StateConjunction}, AbstractLabelExpression, Id};


/// Represents a header item in a HOA file, for more information on each
/// element, see the [HOA format specification](https://adl.github.io/hoaf/).
/// The multiplicity of each element is given in parenthesis.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum HeaderItem {
    /// The version of the HOA format.
    Version(String),
    /// (0|1) State header, gives the number of states in the automaton.
    States(Id),
    /// (>=0) Gives a conjunction of states that are the start states of the
    /// automaton. May be specified multiple times.
    Start(StateConjunction),
    /// (1) Gives the atomic propositions of the automaton.
    AP(Vec<AtomicProposition>),
    /// (>=0) Allows the introduction of an alias for a label expression.
    Alias(AliasName, AbstractLabelExpression),
    /// (1) Gives the acceptance condition of the automaton.
    Acceptance(Id, AcceptanceCondition),
    /// (>=0) Gives the acceptance sets of the automaton.
    AcceptanceName(AcceptanceName, Vec<AcceptanceInfo>),
    /// (0|1) Correspond to tool name and optional version number.
    Tool(String, Option<String>),
    /// (0|1) Correspond to the name of the automaton.
    Name(String),
    /// (>=0) Gives the properties of the automaton.
    Properties(Vec<Property>),
}

impl HeaderItem {
    pub fn count_states(&self) -> Option<usize> {
        if let HeaderItem::States(i) = self {
            Some(*i as usize)
        } else {
            None
        }
    }

    pub fn try_acceptance_name(&self) -> Option<(&AcceptanceName, &[AcceptanceInfo])> {
        if let HeaderItem::AcceptanceName(x, y) = self {
            Some((x, y))
        } else {
            None
        }
    }

    pub fn count_acceptance_sets(&self) -> Option<usize> {
        if let HeaderItem::Acceptance(n, _) = self {
            Some(*n as usize)
        } else {
            None
        }
    }
}

impl HeaderItem {
    /// Creates a new version 1 header item.
    pub fn v1() -> Self {
        HeaderItem::Version("v1".to_string())
    }
}

/// Represents the header of a HOA file, consists of a set of [`HeaderItem`]s.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Header(Vec<HeaderItem>);

impl From<Vec<HeaderItem>> for Header {
    fn from(value: Vec<HeaderItem>) -> Self {
        Self(value)
    }
}

impl<'a> IntoIterator for &'a Header {
    type Item = &'a HeaderItem;

    type IntoIter = std::slice::Iter<'a, HeaderItem>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl Header {
    /// Constructs a new header from a vector of header items.
    pub fn from_vec(value: Vec<HeaderItem>) -> Self {
        Self(value)
    }

    /// Returns the version of the format.
    pub fn get_version(&self) -> Option<String> {
        self.iter().find_map(|item| match item {
            HeaderItem::Version(version) => Some(version.clone()),
            _ => None,
        })
    }

    pub fn name(&self) -> Option<String> {
        self.iter().find_map(|item| match item {
            HeaderItem::Name(name) => Some(name.clone()),
            _ => None,
        })
    }

    pub fn start(&self) -> Option<StateConjunction> {
        self.iter().find_map(|item| match item {
            HeaderItem::Start(conjunction) => Some(conjunction.clone()),
            _ => None,
        })
    }

    pub fn acceptance_condition(&self) -> Option<AcceptanceCondition> {
        self.iter().find_map(|item| match item {
            HeaderItem::Acceptance(_, condition) => Some(condition.clone()),
            _ => None,
        })
    }

    pub fn acceptance_name(&self) -> Option<AcceptanceName> {
        self.iter().find_map(|item| match item {
            HeaderItem::AcceptanceName(name, _) => Some(name.clone()),
            _ => None,
        })
    }
    


    pub fn count_states(&self) -> Option<usize> {
        self.iter().find_map(|i| i.count_states())
    }
}

impl Deref for Header {
    type Target = Vec<HeaderItem>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Header {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
