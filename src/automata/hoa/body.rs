use std::ops::{Deref, DerefMut};

use super::{format::{AcceptanceSignature, AtomicProposition, StateConjunction}, AbstractLabelExpression, Id};
/// Newtype wrapper around a [`crate::LabelExpression`], implements [`Deref`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Label(pub AbstractLabelExpression);

impl Deref for Label {
    type Target = AbstractLabelExpression;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Alphabet(pub Vec<AtomicProposition>);

#[derive(Clone, Debug)]
pub struct RawState(
    Option<Label>,
    Id,
    Option<String>,
    Option<AcceptanceSignature>,
);

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExplicitEdge(Label, StateConjunction, Option<AcceptanceSignature>);

#[derive(Clone, Debug, PartialEq, Eq)]
struct ImplicitEdge(StateConjunction, Option<AcceptanceSignature>);

/// Represents an edge in a HOA automaton. It contains the [`crate::LabelExpression`], the
/// [`StateConjunction`] and the [`AcceptanceSignature`] of the edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge(
    pub(crate) Label,
    pub(crate) StateConjunction,
    pub(crate) AcceptanceSignature,
);

impl Edge {
    /// Returns the label of the edge.
    pub fn label(&self) -> &Label {
        &self.0
    }

    /// Gives mutable access to the label of the edge.
    pub fn label_mut(&mut self) -> &mut Label {
        &mut self.0
    }

    /// Returns the state conjunction of the edge.
    pub fn state_conjunction(&self) -> &StateConjunction {
        &self.1
    }

    /// Returns the acceptance signature of the edge.
    pub fn acceptance_signature(&self) -> &AcceptanceSignature {
        &self.2
    }

    /// Tries to get the target (singular) of the transition. Returns `None` if the
    /// transition does not have a singular target.
    pub fn target(&self) -> Option<Id> {
        self.1.get_singleton()
    }

    /// Builds an edge from its parts.
    pub fn from_parts(
        label_expression: Label,
        state_conjunction: StateConjunction,
        acceptance_signature: AcceptanceSignature,
    ) -> Self {
        Self(label_expression, state_conjunction, acceptance_signature)
    }
}

/// Represents a state in a HOA automaton. It contains the [`Id`] of the state, an optional
/// comment and a list of outgoing edges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    pub(crate) id: Id,
    pub(crate) label: Option<String>,
    pub(crate) accept_signature: AcceptanceSignature,
    pub(crate) edges: Vec<Edge>,
}

impl State {
    /// Constructs a new state from its parts.
    pub fn from_parts(id: Id, label: Option<String>, accept_signature: AcceptanceSignature, edges: Vec<Edge>) -> Self {
        Self {
            id,
            accept_signature,
            label,
            edges,
        }
    }

    /// Extracts the id of the state.
    pub fn id(&self) -> Id {
        self.id
    }

    /// Extracts the comment of the state, if present.
    pub fn label(&self) -> Option<&str> {
        self.label.as_deref()
    }

    /// Extracts the edges of the state.
    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }

    /// Gives mutable access to the edges of this state.
    pub fn edges_mut(&mut self) -> &mut [Edge] {
        &mut self.edges
    }
}

impl From<(Option<AcceptanceSignature>, ExplicitEdge)> for Edge {
    fn from((state_acc, edge): (Option<AcceptanceSignature>, ExplicitEdge)) -> Self {
        let acc = match (state_acc, &edge.2) {
            (None, None) => AcceptanceSignature(Vec::new()),
            (Some(acc), None) => acc,
            (None, Some(acc)) => acc.clone(),
            (Some(left), Some(right)) => {
                AcceptanceSignature(left.iter().cloned().chain(right.iter().cloned()).collect())
            }
        };
        Edge(edge.0, edge.1, acc)
    }
}

impl TryFrom<(RawState, Vec<ExplicitEdge>)> for State {
    type Error = String;

    fn try_from((state, edges): (RawState, Vec<ExplicitEdge>)) -> Result<Self, Self::Error> {
        let mut out_edges = vec![];
        let RawState(state_label, id, state_text, state_acc) = state;

        if state_label.is_some() {
            return Err("Transformation from state-based to transition-based requires adding a new initial state etc (see example 'non-deterministic state-based Büchi Automaton')".to_string());
        }

        for raw_edge in edges {
            out_edges.push(Edge::from((state_acc.clone(), raw_edge)));
        }

        Ok(State::from_parts(id, state_text, AcceptanceSignature(Vec::new()), out_edges))
    }
}

/// Represents the body of a HOA automaton. In essence, this is just a vector of [`State`]s.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Body(Vec<State>);

impl<'a> IntoIterator for &'a Body {
    type Item = &'a State;

    type IntoIter = std::slice::Iter<'a, State>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl Body {
    /// Constructs a new empty body.
    pub fn new() -> Self {
        Self(Vec::new())
    }
}

impl From<Vec<State>> for Body {
    fn from(value: Vec<State>) -> Self {
        Body(value)
    }
}

impl Deref for Body {
    type Target = Vec<State>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Body {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
