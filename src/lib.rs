#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(assert_matches)]

// use automata::hoa::output::to_dot;
use pltl::PLTL;
use wasm_bindgen::prelude::*;

pub mod automata;
pub mod pltl;
pub mod utils;

#[wasm_bindgen]
pub fn to_dots(input: &str) -> JsValue {
    let (pltl_formula, ctx) = PLTL::from_string(input).unwrap();
    let pltl_formula = pltl_formula.to_no_fgoh().to_negation_normal_form().simplify();
    let context = automata::Context::new(&pltl_formula, ctx);
    let all_sub_automatas = automata::AllSubAutomatas::new(&context);
    let result = all_sub_automatas.to_dots(&context);
    serde_wasm_bindgen::to_value(&result).unwrap()
}
