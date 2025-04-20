use crate::pltl::PLTL; 
use rand::{seq::IndexedRandom, Rng};
use crate::pltl::{UnaryOp, BinaryOp};

fn generate_formula_rec(remaining_ops: usize, atom_count: usize, rng: &mut impl Rng) -> PLTL {
    if remaining_ops == 0 {
        let choice = rng.random_range(0..=atom_count);
        if choice == atom_count {
            if rng.random_bool(0.5) {
                PLTL::Top
            } else {
                PLTL::Bottom
            }
        } else {
            PLTL::Atom(choice as u32)
        }
    } else if rng.random_bool(0.4) || remaining_ops == 1 {
        let op = UnaryOp::all_variants().choose(rng).unwrap();
        
        let sub_formula = generate_formula_rec(remaining_ops - 1, atom_count, rng);
        PLTL::new_unary(*op, sub_formula)
    } else {
        let op = BinaryOp::all_variants().choose(rng).unwrap();
        
        let left_ops = rng.random_range(0..remaining_ops);
        let right_ops = remaining_ops - 1 - left_ops;
        
        let left = generate_formula_rec(left_ops, atom_count, rng);
        let right = generate_formula_rec(right_ops, atom_count, rng);
        
        PLTL::new_binary(*op, left, right)
    }
}

pub fn generate_formula(tree_size: usize, atom_count: usize) -> PLTL {
    let mut rng = rand::rng();
    generate_formula_rec(tree_size, atom_count, &mut rng)
}
