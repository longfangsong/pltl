use super::{BinaryOp, PLTL};

pub fn conjunction(mut content: impl Iterator<Item = PLTL>) -> PLTL {
    let first = content.next().unwrap();
    content.fold(first, |acc, item| {
        PLTL::new_binary(BinaryOp::And, acc, item)
    })
}

pub fn disjunction(mut content: impl Iterator<Item = PLTL>) -> PLTL {
    let first = content.next().unwrap();
    content.fold(first, |acc, item| PLTL::new_binary(BinaryOp::Or, acc, item))
}
