use std::fmt;

use crate::{
    pltl::{BinaryOp, UnaryOp, PLTL},
    utils::{BitSet, BitSet32},
};

#[derive(Debug, Clone)]
pub struct PastSubformularSetContext<'a> {
    pub(crate) origin: &'a PLTL,
    /// All past subformulars in `origin`
    /// psf_id -> psf
    pub(crate) past_subformulas: Vec<&'a PLTL>,
    /// Which past subformulars are convered by another past subformula
    /// For example, `Y(a S Yb)` covers `Yb` and `a S Yb`, and `a S Yb` covers `Yb`
    /// If `Yb`'s id is 0, `a S Yb`'s id is 1, `Y(a S Yb)`'s id is 2
    /// Then `masks[0] = 0b001`, `masks[1] = 0b011`, `masks[2] = 0b111`
    /// psf_id -> mask
    pub(crate) masks: Vec<BitSet32>,
    /// We say formulas with the same shape if they are equivalent without considering the strength
    /// For example, `a S b` and `a ~S b` have the same shape
    /// psf_id -> same shape psf_id set
    pub(crate) same_shape_formulas: Vec<BitSet32>,
    /// The initial state for each past subformula's root
    /// psf_id -> state (weaken=1)
    pub(crate) initial_state: BitSet32,
}

/// Init part for PastSubformularSetContext
impl<'a> PastSubformularSetContext<'a> {
    fn collect_initial_values(
        current: &'a PLTL,
        past_subformulas: &mut Vec<&'a PLTL>,
        masks: &mut Vec<BitSet32>,
        // psf_id -> canonical psf_id
        canonical_formulas: &mut Vec<u32>,
        state: &mut BitSet32,
    ) -> BitSet32 {
        match current {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => 0,
            PLTL::Unary(op @ (UnaryOp::Yesterday | UnaryOp::WeakYesterday), box content) => {
                let mut mask = Self::collect_initial_values(
                    content,
                    past_subformulas,
                    masks,
                    canonical_formulas,
                    state,
                );
                let current_id = past_subformulas.len() as u32;
                mask.set_bit(current_id);
                state.set(current_id, matches!(op, UnaryOp::WeakYesterday));
                if let Some(shape_id) = past_subformulas
                    .iter()
                    .position(|&it| PLTL::eq_without_strength(current, it))
                {
                    canonical_formulas.push(shape_id as u32);
                } else {
                    canonical_formulas.push(current_id);
                }
                past_subformulas.push(current);
                masks.push(mask);
                mask
            }
            PLTL::Unary(_, box content) => Self::collect_initial_values(
                content,
                past_subformulas,
                masks,
                canonical_formulas,
                state,
            ),
            PLTL::Binary(
                op @ (BinaryOp::Since
                | BinaryOp::WeakSince
                | BinaryOp::Before
                | BinaryOp::WeakBefore),
                box lhs,
                box rhs,
            ) => {
                let lhs_mask = Self::collect_initial_values(
                    lhs,
                    past_subformulas,
                    masks,
                    canonical_formulas,
                    state,
                );
                let rhs_mask = Self::collect_initial_values(
                    rhs,
                    past_subformulas,
                    masks,
                    canonical_formulas,
                    state,
                );
                let current_id = past_subformulas.len() as u32;
                let mut mask = lhs_mask | rhs_mask;
                mask.set_bit(current_id);
                state.set(
                    current_id,
                    matches!(op, BinaryOp::WeakSince | BinaryOp::WeakBefore),
                );
                if let Some(shape_id) = past_subformulas
                    .iter()
                    .position(|&it| PLTL::eq_without_strength(current, it))
                {
                    canonical_formulas.push(shape_id as u32);
                } else {
                    canonical_formulas.push(current_id);
                }
                past_subformulas.push(current);
                masks.push(mask);
                mask
            }
            PLTL::Binary(_, box lhs, box rhs) => {
                let lhs_mask = Self::collect_initial_values(
                    lhs,
                    past_subformulas,
                    masks,
                    canonical_formulas,
                    state,
                );
                let rhs_mask = Self::collect_initial_values(
                    rhs,
                    past_subformulas,
                    masks,
                    canonical_formulas,
                    state,
                );
                lhs_mask | rhs_mask
            }
        }
    }

    // todo: we can optimize this out by collecting the same canonical formula directly in collect_initial_values
    fn collect_same_canonical_formula(canonical_formula: &[u32]) -> Vec<BitSet32> {
        let mut result = vec![0; canonical_formula.len()];
        for (psf_id, &canonical_formula_id) in canonical_formula.iter().enumerate() {
            result[canonical_formula_id as usize].set_bit(psf_id as u32);
        }
        for (psf_id, &canonical_formula_id) in canonical_formula.iter().enumerate() {
            result[psf_id] = result[canonical_formula_id as usize];
        }
        result
    }

    pub fn new(origin: &'a PLTL) -> Self {
        let mut past_subformulas = Vec::with_capacity(16);
        let mut masks = Vec::with_capacity(16);
        let mut canonical_formula = Vec::with_capacity(16);
        let mut initial_state = 0;
        Self::collect_initial_values(
            origin,
            &mut past_subformulas,
            &mut masks,
            &mut canonical_formula,
            &mut initial_state,
        );
        let same_canonical_formulas = Self::collect_same_canonical_formula(&canonical_formula);
        Self {
            origin,
            past_subformulas,
            masks,
            same_shape_formulas: same_canonical_formulas,
            initial_state,
        }
    }
}

impl fmt::Display for PastSubformularSetContext<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let w = self.past_subformulas.len();
        let max_f_w = format!("{}", self.origin).len();
        writeln!(f, "Id\t{:w$}\tMask\tEquiv\tState", "Formula", w = max_f_w)?;
        for (psf_id, psf) in self.past_subformulas.iter().enumerate() {
            write!(f, "{}\t", psf_id)?;
            // idk why write!(f, "{psf:w$}\t", w=max_f_w) is not padded correctly
            write!(f, "{:w$}\t", format!("{psf}"), w = max_f_w)?;
            write!(f, "{:0w$b}\t", self.masks[psf_id], w = w)?;
            write!(f, "{}\t", self.same_shape_formulas[psf_id].trailing_zeros())?;
            writeln!(
                f,
                "{}",
                if self.initial_state.get(psf_id as u32) {
                    "W"
                } else {
                    "S"
                }
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_init() {
        let pltl: PLTL = "((Y a) S (~Y a)) B ((Y a) ~S (Y a))".parse().unwrap();
        let context = PastSubformularSetContext::new(&pltl);
        assert_eq!(context.past_subformulas.len(), 7);
        assert_eq!(context.masks.len(), 7);
        assert_eq!(context.same_shape_formulas.len(), 7);
        // two formulas are weakened
        assert_eq!(context.initial_state.count_ones(), 2);
        assert_eq!(context.masks[0], 0b0000001);
        assert_eq!(context.masks[2], 0b0000111);
        assert_eq!(context.same_shape_formulas[0], 0b0011011);

        let pltl: PLTL = "((Y a) S (~Y b)) & ((Y a) ~S (Y b))".parse().unwrap();
        let context = PastSubformularSetContext::new(&pltl);
        assert_eq!(context.past_subformulas.len(), 6);
        assert_eq!(context.masks.len(), 6);
        assert_eq!(context.same_shape_formulas.len(), 6);
        assert_eq!(context.initial_state.count_ones(), 2);
        assert_eq!(context.masks[0], 0b000001);
        assert_eq!(context.masks[2], 0b000111);
        assert_eq!(context.same_shape_formulas[0], 0b001001);
        assert_eq!(context.same_shape_formulas[2], 0b100100);

        let pltl: PLTL = "(Y (a & b)) S (Y a) | (Y a) B (Y b)".parse().unwrap();
        let context = PastSubformularSetContext::new(&pltl);
        println!("{}", context);
        assert_eq!(context.past_subformulas.len(), 6);
        assert_eq!(context.masks.len(), 6);
        assert_eq!(context.initial_state.count_ones(), 0);
        assert_eq!(context.masks[0], 0b000001);
        assert_eq!(context.masks[5], 0b111000);
        assert_eq!(context.same_shape_formulas[0], 0b000001);
        assert_eq!(context.same_shape_formulas[1], 0b001010);
    }
}
