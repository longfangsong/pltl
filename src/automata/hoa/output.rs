use super::{
    body::{Edge, Label},
    format::{
        AcceptanceAtom, AcceptanceCondition, AcceptanceInfo, AcceptanceSignature, AliasName,
        HoaBool, StateConjunction,
    },
    header::HeaderItem,
    HoaAutomaton, State,
};
use crate::automata::hoa::format::{AcceptanceName, Property};
use itertools::Itertools;
use std::fmt::Display;

pub fn to_hoa(aut: &HoaAutomaton) -> String {
    aut.header()
        .into_iter()
        .map(|header_item| header_item.to_string())
        .chain(std::iter::once("--BODY--".to_string()))
        .chain(aut.body().into_iter().map(|state| state.to_string()))
        .chain(std::iter::once("--END--".to_string()))
        .join("\n")
}

pub fn to_dot(aut: &HoaAutomaton) -> String {
    let mut dot = String::new();
    dot.push_str(&format!(
        "digraph {} {{\n",
        aut.header().name().unwrap_or("".to_string())
    ));
    if let Some(acceptance_name) = aut.header().acceptance_name() {
        if acceptance_name == AcceptanceName::Buchi || acceptance_name == AcceptanceName::CoBuchi {
            dot.push_str(&format!("    label=\"[{}]\";\n", acceptance_name));
        } else {
            dot.push_str(&format!(
                "    label=\"{}\\n[{}]\";\n",
                aut.header()
                    .acceptance_condition()
                    .map(|it| it.to_string())
                    .unwrap_or("".to_string()),
                aut.header()
                    .acceptance_name()
                    .map(|it| it.to_string())
                    .unwrap_or("".to_string())
            ));
        }
    }
    dot.push_str("    rankdir=LR;\n");
    dot.push_str("    labelloc=\"t\";\n");
    dot.push_str("    node [shape=circle];\n");
    dot.push_str("    I [label=\"\", style=invis, width=0];\n");
    if let Some(start) = aut.header().start() {
        for state in start.0 {
            dot.push_str(&format!("    I -> {}\n", state));
        }
    }
    let aps = aut.aps();
    for state in aut.body() {
        dot.push_str(&format!("    {}", state.id));
        if let Some(label) = &state.label {
            if state.accept_signature.is_empty() {
                dot.push_str(&format!(" [label=\"{}\"]", label));
            } else if aut
                .header()
                .acceptance_name()
                .map(|it| it == AcceptanceName::Buchi || it == AcceptanceName::CoBuchi)
                .unwrap_or(false)
            {
                dot.push_str(&format!(" [label=\"{}\", shape=doublecircle]", label));
            } else {
                dot.push_str(&format!(
                    " [label=\"{}\\n{}\"]",
                    label, state.accept_signature
                ));
            }
        }
        dot.push('\n');
        for edge in &state.edges {
            if edge.2.is_empty() {
                dot.push_str(&format!(
                    "    {} -> {} [label=\"{}\"]\n",
                    state.id,
                    edge.1,
                    edge.0 .0.format_with_vars(aps)
                ));
            } else {
                dot.push_str(&format!(
                    "    {} -> {} [label=\"{}\\n{}\"]\n",
                    state.id,
                    edge.1,
                    edge.0 .0.format_with_vars(aps),
                    edge.2
                ));
            }
        }
        dot.push('\n');
    }
    dot.push_str("}\n");
    dot
}

impl Display for HeaderItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HeaderItem::Version(version) => write!(f, "HOA: {}", version),
            HeaderItem::States(number) => write!(f, "States: {}", number),
            HeaderItem::Start(state_conj) => write!(f, "Start: {}", state_conj),
            HeaderItem::AP(aps) => write!(
                f,
                "AP: {} {}",
                aps.len(),
                aps.iter().map(|ap| format!("\"{}\"", ap)).join(" ")
            ),
            HeaderItem::Alias(alias_name, alias_expression) => {
                write!(f, "Alias: {} {}", alias_name, alias_expression)
            }
            HeaderItem::Acceptance(number_sets, condition) => {
                write!(f, "Acceptance: {} {}", number_sets, condition)
            }
            HeaderItem::AcceptanceName(identifier, vec_info) => {
                write!(f, "acc-name: {} {}", identifier, vec_info.iter().join(" "))
            }
            HeaderItem::Tool(name, options) => {
                write!(f, "tool: {} {}", name, options.iter().join(" "))
            }
            HeaderItem::Name(name) => write!(f, "name: \"{}\"", name),
            HeaderItem::Properties(properties) => {
                write!(f, "properties: {}", properties.iter().join(" "))
            }
        }
    }
}

impl Display for AcceptanceInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AcceptanceInfo::Int(integer) => write!(f, "{}", integer),
            AcceptanceInfo::Identifier(identifier) => write!(f, "{}", identifier),
        }
    }
}

impl Display for Property {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Property::StateLabels => "state-labels",
                Property::TransLabels => "trans-labels",
                Property::ImplicitLabels => "implicit-labels",
                Property::ExplicitLabels => "explicit-labels",
                Property::StateAcceptance => "state-acc",
                Property::TransitionAcceptance => "trans-acc",
                Property::UniversalBranching => "univ-branch",
                Property::NoUniversalBranching => "no-univ-branch",
                Property::Deterministic => "deterministic",
                Property::Complete => "complete",
                Property::Unambiguous => "unabmiguous",
                Property::StutterInvariant => "stutter-invariant",
                Property::Weak => "weak",
                Property::VeryWeak => "very-weak",
                Property::InherentlyWeak => "inherently-weak",
                Property::Terminal => "terminal",
                Property::Tight => "tight",
                Property::Colored => "colored",
            }
        )
    }
}

impl Display for AcceptanceName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                AcceptanceName::Buchi => "Buchi",
                AcceptanceName::GeneralizedBuchi => "generalized-Buchi",
                AcceptanceName::CoBuchi => "co-Buchi",
                AcceptanceName::GeneralizedCoBuchi => "generalized-co-Buchi",
                AcceptanceName::Streett => "Streett",
                AcceptanceName::Rabin => "Rabin",
                AcceptanceName::GeneralizedRabin => "generalized-Rabin",
                AcceptanceName::Parity => "parity",
                AcceptanceName::All => "all",
                AcceptanceName::None => "none",
            }
        )
    }
}

impl Display for AcceptanceAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AcceptanceAtom::Positive(id) => write!(f, "{}", id),
            AcceptanceAtom::Negative(id) => write!(f, "!{}", id),
        }
    }
}

impl Display for HoaBool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.0 { "t" } else { "f" })
    }
}

impl Display for AcceptanceCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AcceptanceCondition::Fin(id) => write!(f, "Fin({})", id),
            AcceptanceCondition::Inf(id) => write!(f, "Inf({})", id),
            AcceptanceCondition::And(left, right) => write!(f, "({} & {})", left, right),
            AcceptanceCondition::Or(left, right) => write!(f, "({} | {})", left, right),
            AcceptanceCondition::Boolean(val) => write!(f, "{}", val),
        }
    }
}

impl Display for AliasName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl Display for StateConjunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.iter().map(|s| s.to_string()).join(" & "))
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.0)
    }
}

impl Display for AcceptanceSignature {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return Ok(());
        }
        write!(f, "{{{}}}", self.0.iter().join(" "))
    }
}

impl Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.0, self.1, self.2)
    }
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "State: {}", self.id)?;
        if let Some(label) = &self.label {
            write!(f, " \"{}\"", label)?;
        }
        writeln!(f, " {}", self.accept_signature)?;

        for edge in &self.edges {
            writeln!(f, "{}", edge)?;
        }
        Ok(())
    }
}
