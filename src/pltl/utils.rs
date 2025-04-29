use super::{labeled::LabeledPLTL, BinaryOp, PLTL};

pub fn conjunction(content: impl Iterator<Item = PLTL>) -> PLTL {
    content
        .reduce(|acc, item| PLTL::new_binary(BinaryOp::And, acc, item))
        .unwrap()
}

pub fn disjunction(content: impl Iterator<Item = PLTL>) -> PLTL {
    content
        .reduce(|acc, item| PLTL::new_binary(BinaryOp::Or, acc, item))
        .unwrap()
}

pub fn disjunction_labeled(content: impl Iterator<Item = LabeledPLTL>) -> LabeledPLTL {
    content.reduce(|acc, item| acc | item).unwrap()
}
