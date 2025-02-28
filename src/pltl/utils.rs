use std::collections::HashSet;

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

pub fn powerset<T: Clone + std::cmp::Eq + std::hash::Hash>(origin: &HashSet<T>) -> Vec<HashSet<T>> {
    let mut result = vec![HashSet::new()];
    for elem in origin.iter() {
        let mut new_subsets = Vec::new();
        for subset in &result {
            let mut new_subset = subset.clone();
            new_subset.insert(elem.clone());
            new_subsets.push(new_subset);
        }
        result.extend(new_subsets);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_powerset() {
        let set = HashSet::from(["a", "b"]);
        let expected = vec![
            HashSet::new(),
            HashSet::from(["a"]),
            HashSet::from(["b"]),
            HashSet::from(["a", "b"]),
        ];
        assert_eq!(powerset(&set), expected);
    }
}
