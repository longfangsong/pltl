#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(assert_matches)]

use pltl::PLTL;
use wasm_bindgen::prelude::*;

pub mod automata;
pub mod pltl;
pub mod utils;

#[wasm_bindgen]
pub fn to_dots(input: &str) -> JsValue {
    console_error_panic_hook::set_once();
    let (pltl_formula, pltl_ctx) = PLTL::from_string(input).unwrap();
    let pltl_formula = pltl_formula
        .to_no_fgoh()
        .to_negation_normal_form()
        .simplify();
    let context = automata::Context::new(&pltl_formula, &pltl_ctx);
    let all_sub_automatas = automata::AllSubAutomatas::new(&context, &pltl_ctx);
    let result = all_sub_automatas.to_dots(&context, &pltl_ctx);
    serde_wasm_bindgen::to_value(&result).unwrap()
}

#[wasm_bindgen]
pub fn to_files(input: &str) -> JsValue {
    let (pltl_formula, pltl_ctx) = PLTL::from_string(input).unwrap();
    let pltl_formula = pltl_formula
        .to_no_fgoh()
        .to_negation_normal_form()
        .simplify();
    let context = automata::Context::new(&pltl_formula, &pltl_ctx);
    let all_sub_automatas = automata::AllSubAutomatas::new(&context, &pltl_ctx);
    let result = all_sub_automatas.to_files();
    serde_wasm_bindgen::to_value(&result).unwrap()
}
