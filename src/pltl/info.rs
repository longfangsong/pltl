use super::{BinaryOp, UnaryOp, PLTL};

impl UnaryOp {
    pub fn is_temporal(&self) -> bool {
        matches!(
            self,
            UnaryOp::Next
                | UnaryOp::Yesterday
                | UnaryOp::WeakYesterday
                | UnaryOp::Globally
                | UnaryOp::Eventually
                | UnaryOp::Historically
                | UnaryOp::Once
        )
    }
    pub fn is_past(&self) -> bool {
        matches!(self, UnaryOp::Yesterday | UnaryOp::WeakYesterday)
    }
    pub fn is_u_type(&self) -> bool {
        matches!(self, UnaryOp::Next)
    }
    pub fn is_v_type(&self) -> bool {
        matches!(self, UnaryOp::Next)
    }
    pub fn is_weak_past(&self) -> bool {
        *self == UnaryOp::WeakYesterday
    }
}

impl BinaryOp {
    pub fn is_temporal(&self) -> bool {
        matches!(
            self,
            BinaryOp::Until
                | BinaryOp::Since
                | BinaryOp::WeakUntil
                | BinaryOp::WeakSince
                | BinaryOp::BackTo
                | BinaryOp::WeakBackTo
                | BinaryOp::Release
                | BinaryOp::MightyRelease
        )
    }
    pub fn is_past(&self) -> bool {
        matches!(
            self,
            BinaryOp::BackTo | BinaryOp::WeakBackTo | BinaryOp::Since | BinaryOp::WeakSince
        )
    }
    pub fn is_u_type(&self) -> bool {
        matches!(self, BinaryOp::Until | BinaryOp::MightyRelease)
    }
    pub fn is_v_type(&self) -> bool {
        matches!(self, BinaryOp::WeakUntil | BinaryOp::Release)
    }
    pub fn is_weak_past(&self) -> bool {
        *self == BinaryOp::WeakBackTo || *self == BinaryOp::WeakSince
    }
}

impl PLTL {
    pub fn subformulas(&self) -> Vec<&PLTL> {
        let mut result = Vec::new();
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => (),
            PLTL::Unary(_, box content) => {
                result.extend_from_slice(&content.subformulas());
            }
            PLTL::Binary(_, box lhs, box rhs) => {
                result.extend_from_slice(&lhs.subformulas());
                result.extend_from_slice(&rhs.subformulas());
            }
        }
        result.push(self);
        result
    }

    pub fn is_temporal(&self) -> bool {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => false,
            PLTL::Unary(op, _) => op.is_temporal(),
            PLTL::Binary(op, _, _) => op.is_temporal(),
        }
    }

    pub fn is_u_type(&self) -> bool {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => false,
            PLTL::Unary(op, _) => op.is_u_type(),
            PLTL::Binary(op, _, _) => op.is_u_type(),
        }
    }

    fn should_in_u_set(&self) -> bool {
        match self {
            PLTL::Binary(op, _, _) => op.is_u_type(),
            _ => false,
        }
    }

    pub fn is_v_type(&self) -> bool {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => false,
            PLTL::Unary(op, _) => op.is_v_type(),
            PLTL::Binary(op, _, _) => op.is_v_type(),
        }
    }

    fn should_in_v_set(&self) -> bool {
        match self {
            PLTL::Binary(op, _, _) => op.is_v_type(),
            _ => false,
        }
    }

    pub fn is_past(&self) -> bool {
        match self {
            PLTL::Top | PLTL::Bottom | PLTL::Atom(_) => false,
            PLTL::Unary(op, _) => op.is_past(),
            PLTL::Binary(op, _, _) => op.is_past(),
        }
    }

    pub fn u_set(&self) -> Vec<&PLTL> {
        self.subformulas()
            .into_iter()
            .filter(|f| f.should_in_u_set())
            .collect()
    }

    pub fn v_set(&self) -> Vec<&PLTL> {
        self.subformulas()
            .into_iter()
            .filter(|f| f.should_in_v_set())
            .collect()
    }

    pub fn past_subformulas(&self) -> Vec<&PLTL> {
        self.subformulas()
            .into_iter()
            .filter(|f| f.is_past())
            .collect()
    }
}
