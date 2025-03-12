#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(assert_matches)]

use automata::hoa::output::to_dot;
use pltl::PLTL;
use wasm_bindgen::prelude::*;

pub mod automata;
pub mod pltl;
pub mod utils;


#[wasm_bindgen]
pub fn to_dots(input: &str) -> JsValue {
    let (pltl_formula, atom_map) = PLTL::from_string(input);
    let pltl_formula = pltl_formula.normal_form();
    let context = automata::Context::new(&pltl_formula, atom_map);
    let all_sub_automatas = automata::AllSubAutomatas::new(&context);
    let result: Vec<Vec<String>> = vec![
        all_sub_automatas.guarantee_automatas.values().map(|automata| to_dot(automata)).collect(),
        all_sub_automatas.safety_automatas.values().map(|automata| to_dot(automata)).collect(),
        all_sub_automatas.stable_automatas.iter().map(|automata| to_dot(automata)).collect(),
    ];
    serde_wasm_bindgen::to_value(&result).unwrap()
}
