use std::collections::HashSet;

use crate::{pltl::{annotated::Annotated, BinaryOp, UnaryOp, PLTL}, utils::{BitSet, BitSet32}};

use super::{context::PastSubformularSetContext, set::PastSubformulaSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PastSubformula {
    pub(crate) id: u32,
    pub(crate) state: BitSet32,
}

impl PastSubformula {
    pub fn rewrite(&self, ctx: &PastSubformularSetContext<'_>, set: &PastSubformulaSet) -> Self {
        let mut new_weaken = 0;
        // todo: this may be optimized further
        // say, mask & set.existence is the part of the set exists in the set
        // but I'm not sure how to handle the same_shape_psfs
        for part_id in ctx.masks[self.id as usize].iter() {
            let contains_part = set.contains(
                ctx,
                &PastSubformula {
                    id: part_id,
                    state: self.state,
                },
            );
            new_weaken.set(part_id, contains_part);
        }
        Self {
            id: self.id,
            state: new_weaken,
        }
    }

    fn set_weaken(&self, root: &mut PLTL, psf_id: u32, ctx: &PastSubformularSetContext<'_>) -> u32 {
        let weak = self.state.get(psf_id);
        if root.is_temporal() {
            root.inplace_rewrite(weak);
            if psf_id == 0 {
                return psf_id;
            }
            match root {
                PLTL::Unary(_, box inner) => self.set_weaken(inner, psf_id - 1, ctx),
                PLTL::Binary(_, box lhs, box rhs) => {
                    let rhs_id = self.set_weaken(rhs, psf_id - 1, ctx);
                    self.set_weaken(lhs, rhs_id, ctx)
                }
                _ => unreachable!(),
            }
        } else {
            match root {
                PLTL::Unary(_, box inner) => self.set_weaken(inner, psf_id, ctx),
                PLTL::Binary(_, box lhs, box rhs) => {
                    let lhs_id = self.set_weaken(lhs, psf_id, ctx);
                    self.set_weaken(rhs, lhs_id, ctx)
                }
                _ => psf_id,
            }
        }
    }

    pub fn to_pltl(&self, ctx: &PastSubformularSetContext<'_>) -> PLTL {
        let mut result = ctx.past_subformulas[self.id as usize].clone();
        self.set_weaken(&mut result, self.id, ctx);
        result
    }

    pub fn weaken_condition(&self, ctx: &PastSubformularSetContext<'_>) -> Annotated {
        let op = ctx.past_subformulas[self.id as usize];
        match (op, self.state.get(self.id)) {
            (PLTL::Unary(UnaryOp::Yesterday | UnaryOp::WeakYesterday, box content), _) => {
                // todo: optimize this like:
                // if content.is_temporal() {
                //     Annotated::PastSubformula(PastSubformula {
                //         id: self.id - 1,
                //         state: self.state,
                //     })
                // } else {
                    Annotated::from_pltl(content, ctx)
                // }
            },
            (PLTL::Binary(BinaryOp::Since | BinaryOp::WeakSince, _, box rhs), false) => {
                // if rhs.is_temporal() {
                //     Annotated::PastSubformula(PastSubformula {
                //         id: self.id - 1,
                //         state: self.state,
                //     })
                // } else {
                Annotated::from_pltl(rhs, ctx)
                // }
            },
            (PLTL::Binary(BinaryOp::Since | BinaryOp::WeakSince, box lhs, box rhs), true) => {
                let new_rhs = 
                    Annotated::from_pltl(rhs, ctx);
                let new_lhs =
                    Annotated::from_pltl(lhs, ctx);
                Annotated::Binary(BinaryOp::Or, Box::new(new_lhs), Box::new(new_rhs))
            }
            (PLTL::Binary(BinaryOp::Before | BinaryOp::WeakBefore, box lhs, box rhs), false) => {
                let new_rhs = 
                    Annotated::from_pltl(rhs, ctx);
                let new_lhs = 
                    Annotated::from_pltl(lhs, ctx);
                Annotated::Binary(BinaryOp::And, Box::new(new_lhs), Box::new(new_rhs))
            },
            (PLTL::Binary(BinaryOp::Before | BinaryOp::WeakBefore, _, box rhs), true) => {
                    Annotated::from_pltl(rhs, ctx)
            },
            _ => unreachable!("Must be past formula"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::pltl::PLTL;

    use super::*;

    #[test]
    fn test_rewrite() {
        let ltl: PLTL = "((Y a) S (~Y a)) B ((Y a) ~S (Y a))".parse().unwrap();
        let ctx = PastSubformularSetContext::new(&ltl);
        // Ya<{Ya}> = ~Ya
        let set = PastSubformulaSet {
            existence: 0b0000001,
            state: 0b0000000,
        };
        let psf = PastSubformula {
            id: 0,
            state: 0b0000000,
        };
        let rewritten = psf.rewrite(&ctx, &set);
        assert_eq!(format!("{}", rewritten.to_pltl(&ctx)), "~Ya");
        // Ya<{}> = Ya
        let set = PastSubformulaSet {
            existence: 0b0000000,
            state: 0b0000000,
        };
        let psf = PastSubformula {
            id: 0,
            state: 0b0000000,
        };
        let rewritten = psf.rewrite(&ctx, &set);
        assert_eq!(format!("{}", rewritten.to_pltl(&ctx)), "Ya");
        // ~Ya<{}> = Ya
        let psf = PastSubformula {
            id: 1,
            state: 0b0000010,
        };
        let rewritten = psf.rewrite(&ctx, &set);
        assert_eq!(format!("{}", rewritten.to_pltl(&ctx)), "Ya");
        // ~Ya<{~Ya}> = Ya
        let set = PastSubformulaSet {
            existence: 0b0000010,
            state: 0b0000010,
        };
        let psf = PastSubformula {
            id: 1,
            state: 0b0000010,
        };
        let rewritten = psf.rewrite(&ctx, &set);
        assert_eq!(format!("{}", rewritten.to_pltl(&ctx)), "~Ya");
        // (Y a) S (~Y a) <{Ya}> = (~Y a) S (Y a)
        let set = PastSubformulaSet {
            existence: 0b0000001,
            state: 0b0000000,
        };
        let psf = PastSubformula {
            id: 2,
            state: 0b0000010,
        };
        let rewritten = psf.rewrite(&ctx, &set);
        assert_eq!(format!("{}", rewritten.to_pltl(&ctx)), "~Ya S Ya");
        // (Y a) S (~Y a) <{Ya, ~Y a}> = (~Y a) S (~Y a)
        let set = PastSubformulaSet {
            existence: 0b0000011,
            state: 0b0000010,
        };
        let psf = PastSubformula {
            id: 2,
            state: 0b0000010,
        };
        let rewritten = psf.rewrite(&ctx, &set);
        assert_eq!(format!("{}", rewritten.to_pltl(&ctx)), "~Ya S ~Ya");
        // (Y a) S (~Y a) <{Ya, ~Y a, (Y a) S (~Y a)}> = (~Y a) ~S (~Y a)
        let set = PastSubformulaSet {
            existence: 0b0000111,
            state: 0b0000010,
        };
        let psf = PastSubformula {
            id: 2,
            state: 0b0000010,
        };
        let rewritten = psf.rewrite(&ctx, &set);
        assert_eq!(format!("{}", rewritten.to_pltl(&ctx)), "~Ya ~S ~Ya");

        let pltl: PLTL = "((Y a) S (~Y a)) & ((Y a) ~S (Y a))".parse().unwrap();
        let ctx = PastSubformularSetContext::new(&pltl);
        // (Y a) S (~Y a) <{Ya}> = (~Y a) S (Y a)
        // The Ya in the set is from the second part of the formula
        let set = PastSubformulaSet {
            existence: 0b010000,
            state: 0b000000,
        };
        let psf = PastSubformula {
            id: 2,
            state: 0b0000010,
        };
        let rewritten = psf.rewrite(&ctx, &set);
        assert_eq!(format!("{}", rewritten.to_pltl(&ctx)), "~Ya S Ya");
    }

    #[test]
    fn test_weaken_condition() {
        // Test Yesterday operator
        let pltl: PLTL = "Y a".parse().unwrap();
        let ctx = PastSubformularSetContext::new(&pltl);
        let psf = PastSubformula {
            id: 0,
            state: 0b0,
        };
        let condition = psf.weaken_condition(&ctx);
        assert_eq!(format!("{}", condition.to_pltl(&ctx)), "a");

        // Test Since operator with weak=false
        let pltl: PLTL = "a S (Y b)".parse().unwrap();
        let ctx = PastSubformularSetContext::new(&pltl);
        let psf = PastSubformula {
            id: 1,
            state: 0b00,
        };
        let condition = psf.weaken_condition(&ctx);
        assert_eq!(format!("{}", condition.to_pltl(&ctx)), "Yb");

        // Test Since operator with weak=true
        let pltl: PLTL = "a S (Y b)".parse().unwrap();
        let ctx = PastSubformularSetContext::new(&pltl);
        let psf = PastSubformula {
            id: 1,
            state: 0b10,
        };
        let condition = psf.weaken_condition(&ctx);
        assert_eq!(format!("{}", condition.to_pltl(&ctx)), "a ∨ Yb");

        // Test Before operator with weak=false
        let pltl: PLTL = "a B (Y b)".parse().unwrap();
        let ctx = PastSubformularSetContext::new(&pltl);
        let psf = PastSubformula {
            id: 1,
            state: 0b00,
        };
        let condition = psf.weaken_condition(&ctx);
        assert_eq!(format!("{}", condition.to_pltl(&ctx)), "a ∧ Yb");

        // Test Before operator with weak=true
        let pltl: PLTL = "a B (Y b)".parse().unwrap();
        let ctx = PastSubformularSetContext::new(&pltl);
        let psf = PastSubformula {
            id: 1,
            state: 0b10,
        };
        let condition = psf.weaken_condition(&ctx);
        assert_eq!(format!("{}", condition.to_pltl(&ctx)), "Yb");

        // Test nested temporal formulas
        let pltl: PLTL = "(Y a) S (Y (b S c))".parse().unwrap();
        let ctx = PastSubformularSetContext::new(&pltl);
        let psf = PastSubformula {
            id: 3,
            state: 0b1000,
        };
        let condition = psf.weaken_condition(&ctx);
        assert_eq!(format!("{}", condition.to_pltl(&ctx)), "Ya ∨ Y(b S c)");
    }
}
