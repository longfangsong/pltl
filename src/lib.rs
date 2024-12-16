#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(assert_matches)]

use std::collections::HashSet;

use pltl::PLTL;
use word::WordAtTime;
mod pltl;
mod word;

pub fn entailed_subformulae(f: &PLTL, word: WordAtTime) -> HashSet<PLTL> {
    if word.time == 0 {
        let psf = f.past_subformulaes();
        psf.into_iter().filter(|it| it == &it.weakening()).collect()
    } else {
        let last = entailed_subformulae(
            f,
            WordAtTime {
                word: word.word,
                time: word.time - 1,
            },
        );
        let psf_last = f.rewrite_under_sets(&last).past_subformulaes();
        psf_last
            .into_iter()
            .filter(|it| {
                let w = WordAtTime {
                    word: word.word,
                    time: word.time - 1,
                };
                w.models(&it.weakning_conditions())
            })
            .collect()
    }
}

pub fn entailed_subformulae_set(f: &PLTL, cs: &[HashSet<PLTL>]) -> HashSet<PLTL> {
    let psf = f.past_subformulaes();
    let o_vec_c = psf
        .into_iter()
        .filter(|it| {
            let mut result = it.clone();
            for c in cs {
                result = result.rewrite_under_sets(c);
            }
            result == result.weakening()
        })
        .collect();
    o_vec_c
}

// pub fn after_local(f: &PLTL, letter: &HashSet<String>, c: &HashSet<PLTL>) -> PLTL {}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{
        entailed_subformulae,
        pltl::parse,
        word::{gen_word, WordAtTime},
    };

    #[test]
    fn test_sx() {
        let pltl_code = "(p ~S q) ∧ (r B s)";
        let phi = parse(pltl_code).unwrap().1.normal_form();
        println!("{}", phi);
        gen_word!(w, 0 => [], 1 => [r], 2 => [s], 3 => [p, q], 4 => [q], 5 => [q, r, s], 6 => [p]);
        for i in 0..=6 {
            let word = WordAtTime { word: w, time: i };
            println!("{i}: {:?}", entailed_subformulae(&phi, word));
        }
    }

    #[test]
    fn test_sss() {
        let pltl_code = "(p ~S q) ∧ (r B s)";
        let phi = parse(pltl_code).unwrap().1.normal_form();
        println!("{}", phi);
        gen_word!(w, 0 => [], 1 => [r], 2 => [s], 3 => [p, q], 4 => [q], 5 => [p, r, s], 6 => [p]);
        for i in 0..=6 {
            let word = WordAtTime { word: w, time: i };
            println!("{i}: {:?}", entailed_subformulae(&phi, word));
        }
    }

    #[test]
    fn test_xxx() {
        let pltl_code = "Y x";
        let phi = parse(pltl_code).unwrap().1.normal_form();
        println!("{}", phi);
        gen_word!(w, 0 => [], 1 => [x], 2 => [x], 3 => [x], 4 => [x], 5 => [x], 6 => [x]);
        for i in 0..=6 {
            let word = WordAtTime { word: w, time: i };
            println!("{i}: {:?}", entailed_subformulae(&phi, word));
        }
    }
}
