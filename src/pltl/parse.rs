use std::{cell::RefCell, collections::HashMap, fmt, rc::Rc, str::FromStr};

use super::{BinaryOp, UnaryOp};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, char, multispace0, one_of},
    combinator::{map, recognize},
    multi::{fold_many1, many0, many1},
    sequence::{delimited, pair, preceded},
    Finish, IResult, Input, Parser,
};
use std::borrow::BorrowMut;

#[derive(Debug, Clone)]
pub struct Error {
    offset: usize,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum PLTLParseTree {
    Top,
    Bottom,
    Atom(String),
    Unary(UnaryOp, Box<PLTLParseTree>),
    Binary(BinaryOp, Box<PLTLParseTree>, Box<PLTLParseTree>),
}

#[derive(Debug, Clone)]
pub struct ParserInput<'a> {
    input: &'a str,
    cache: Rc<RefCell<HashMap<&'a str, (&'a str, PLTLParseTree)>>>,
}

impl<'a> ParserInput<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            cache: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn get_cached(&self, key: &str) -> Option<(Self, PLTLParseTree)> {
        self.cache.borrow().get(key).map(|(rest, result)| {
            (
                Self {
                    input: rest,
                    cache: Rc::clone(&self.cache),
                },
                result.clone(),
            )
        })
    }

    fn cache(&self, key: &'a str, rest: &'a str, value: PLTLParseTree) {
        RefCell::borrow_mut(&self.cache).insert(key, (rest, value));
    }

    fn as_str(&self) -> &'a str {
        self.input
    }
}

impl<'a> Input for ParserInput<'a> {
    type Item = char;

    type Iter = <&'a str as Input>::Iter;

    type IterIndices = <&'a str as Input>::IterIndices;

    fn input_len(&self) -> usize {
        self.input.input_len()
    }

    fn take(&self, index: usize) -> Self {
        Self {
            input: self.input.take(index),
            cache: Rc::clone(&self.cache),
        }
    }

    fn take_from(&self, index: usize) -> Self {
        Self {
            input: self.input.take_from(index),
            cache: Rc::clone(&self.cache),
        }
    }

    fn take_split(&self, index: usize) -> (Self, Self) {
        let (fst, snd) = self.input.take_split(index);
        (
            Self {
                input: fst,
                cache: Rc::clone(&self.cache),
            },
            Self {
                input: snd,
                cache: Rc::clone(&self.cache),
            },
        )
    }

    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.input.position(predicate)
    }

    fn iter_elements(&self) -> Self::Iter {
        self.input.iter_elements()
    }

    fn iter_indices(&self) -> Self::IterIndices {
        self.input.iter_indices()
    }

    fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
        self.input.slice_index(count)
    }
}

fn lift_parser<'a, F, O>(
    mut parser: F,
) -> impl Parser<ParserInput<'a>, Output = O, Error = nom::error::Error<ParserInput<'a>>>
where
    F: Parser<&'a str, Output = O, Error = nom::error::Error<&'a str>>,
    O: Clone,
{
    move |input: ParserInput<'a>| {
        let (remaining, result) = parser.parse(input.as_str()).map_err(|e| match e {
            nom::Err::Incomplete(needed) => nom::Err::Incomplete(needed),
            nom::Err::Error(error) => nom::Err::Error(nom::error::Error {
                input: ParserInput {
                    input: error.input,
                    cache: Rc::clone(&input.cache),
                },
                code: error.code,
            }),
            _ => unimplemented!(),
        })?;
        Ok((
            ParserInput {
                input: remaining,
                cache: Rc::clone(&input.cache),
            },
            result,
        ))
    }
}

fn not_op(input: &str) -> IResult<&str, UnaryOp> {
    map(alt((tag("!"), tag("¬"), tag("\\neg"))), |_| UnaryOp::Not).parse(input)
}

fn temporal_unary_op(input: &str) -> IResult<&str, UnaryOp> {
    const OPS: [(&str, UnaryOp); 8] = [
        ("X", UnaryOp::Next),
        ("Y", UnaryOp::Yesterday),
        ("~Y", UnaryOp::WeakYesterday),
        ("\\widetilde{Y}", UnaryOp::WeakYesterday),
        ("F", UnaryOp::Eventually),
        ("O", UnaryOp::Once),
        ("G", UnaryOp::Globally),
        ("H", UnaryOp::Historically),
    ];

    for (symbol, op) in OPS.iter() {
        if let Ok((remaining, _)) = tag::<_, _, nom::error::Error<_>>(*symbol).parse(input) {
            return Ok((remaining, *op));
        }
    }

    Err(nom::Err::Error(nom::error::Error::new(
        input,
        nom::error::ErrorKind::Alt,
    )))
}

fn and_op(input: &str) -> IResult<&str, BinaryOp> {
    map(
        alt((tag("∧"), tag("&"), tag("\\wedge"), tag("\\land"))),
        |_| BinaryOp::And,
    )
    .parse(input)
}

fn or_op(input: &str) -> IResult<&str, BinaryOp> {
    map(
        alt((tag("∨"), tag("|"), tag("\\vee"), tag("\\lor"))),
        |_| BinaryOp::Or,
    )
    .parse(input)
}

fn implies_op(input: &str) -> IResult<&str, &str> {
    recognize(alt((tag("→"), tag("->")))).parse(input)
}

fn equiv_op(input: &str) -> IResult<&str, &str> {
    recognize(alt((tag("↔"), tag("<->")))).parse(input)
}

fn temporal_binary_op(input: &str) -> IResult<&str, BinaryOp> {
    const OPS: [(&str, BinaryOp); 10] = [
        ("U", BinaryOp::Until),
        ("S", BinaryOp::Since),
        ("W", BinaryOp::WeakUntil),
        ("~S", BinaryOp::WeakSince),
        ("\\widetilde{S}", BinaryOp::WeakSince),
        ("M", BinaryOp::MightyRelease),
        ("B", BinaryOp::BackTo),
        ("R", BinaryOp::Release),
        ("~B", BinaryOp::WeakBackTo),
        ("\\widetilde{B}", BinaryOp::WeakBackTo),
    ];

    for (symbol, op) in OPS.iter() {
        if let Ok((remaining, _)) = tag::<_, _, nom::error::Error<&str>>(*symbol).parse(input) {
            return Ok((remaining, *op));
        }
    }

    Err(nom::Err::Error(nom::error::Error::new(
        input,
        nom::error::ErrorKind::Alt,
    )))
}

fn top(input: &str) -> IResult<&str, PLTLParseTree> {
    map(alt((tag("⊤"), tag("\\top"), tag("1"))), |_| {
        PLTLParseTree::Top
    })
    .parse(input)
}

fn bottom(input: &str) -> IResult<&str, PLTLParseTree> {
    map(alt((tag("⊥"), tag("\\bot"), tag("0"))), |_| {
        PLTLParseTree::Bottom
    })
    .parse(input)
}

fn atom(input: &str) -> IResult<&str, PLTLParseTree> {
    let first = one_of("abcdefghijklmnopqrstuvwxyz_αβγδεζηθικλμνξοπρστυφϕχψω");
    let rest = recognize(many0(alt((
        alphanumeric1,
        recognize(one_of("_αβγδεζηθικλμνξοπρστυφχψω")),
    ))));
    map(pair(first, rest), |(f, r): (char, &str)| {
        PLTLParseTree::Atom(format!("{f}{r}"))
    })
    .parse(input)
}

fn in_parantheses<'a>(input: ParserInput<'a>) -> IResult<ParserInput<'a>, PLTLParseTree> {
    delimited(
        lift_parser(preceded(multispace0, char('('))),
        preceded(lift_parser(multispace0), parse),
        lift_parser(preceded(multispace0, char(')'))),
    )
    .parse(input)
}

fn higher_than_not(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    alt((
        in_parantheses,
        lift_parser(atom),
        lift_parser(top),
        lift_parser(bottom),
    ))
    .parse(input)
}

fn parse_not(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    map(
        pair(
            lift_parser(many1(preceded(multispace0, not_op))),
            preceded(lift_parser(multispace0), higher_than_not),
        ),
        |(mut unary_ops, mut r)| {
            while let Some(op) = unary_ops.pop() {
                r = PLTLParseTree::new_unary(op, r)
            }
            r
        },
    )
    .parse(input)
}

fn higher_than_temporal_unary(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    alt((parse_not, higher_than_not)).parse(input)
}

fn temporal_unary(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    map(
        pair(
            lift_parser(many1(preceded(multispace0, temporal_unary_op))),
            preceded(lift_parser(multispace0), higher_than_temporal_unary),
        ),
        |(mut unary_ops, mut r)| {
            while let Some(op) = unary_ops.pop() {
                r = PLTLParseTree::new_unary(op, r)
            }
            r
        },
    )
    .parse(input)
}

fn higher_than_temporal_binary(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    alt((temporal_unary, higher_than_temporal_unary)).parse(input)
}

fn temporal_binary(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    let (input, first) = higher_than_temporal_binary(input)?;
    fold_many1(
        pair(
            lift_parser(preceded(multispace0, temporal_binary_op)),
            preceded(lift_parser(multispace0), higher_than_temporal_binary),
        ),
        move || first.clone(),
        |init, (op, g)| PLTLParseTree::new_binary(op, init, g),
    )
    .parse(input)
}

fn higher_than_and(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    alt((temporal_binary, higher_than_temporal_binary)).parse(input)
}

fn and(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    let (input, first) = higher_than_and(input)?;
    fold_many1(
        pair(
            lift_parser(preceded(multispace0, and_op)),
            preceded(lift_parser(multispace0), higher_than_and),
        ),
        move || first.clone(),
        |init, (op, g)| PLTLParseTree::new_binary(op, init, g),
    )
    .parse(input)
}

fn higher_than_or(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    alt((and, higher_than_and)).parse(input)
}

fn or(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    let (input, first) = higher_than_or(input)?;
    fold_many1(
        pair(
            lift_parser(preceded(multispace0, or_op)),
            preceded(lift_parser(multispace0), higher_than_or),
        ),
        move || first.clone(),
        |init, (op, g)| PLTLParseTree::new_binary(op, init, g),
    )
    .parse(input)
}

pub fn higher_than_implies(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    alt((or, higher_than_or)).parse(input)
}

pub fn implies(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    let (input, first) = higher_than_implies(input)?;
    fold_many1(
        pair(
            preceded(multispace0, lift_parser(implies_op)),
            preceded(multispace0, higher_than_implies),
        ),
        move || first.clone(),
        |init, (_, g)| {
            PLTLParseTree::new_binary(
                BinaryOp::Or,
                PLTLParseTree::new_unary(UnaryOp::Not, init),
                g,
            )
        },
    )
    .parse(input)
}

pub fn higher_than_equiv(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    alt((implies, higher_than_implies)).parse(input)
}

pub fn equiv(input: ParserInput) -> IResult<ParserInput, PLTLParseTree> {
    let (input, first) = higher_than_equiv(input)?;
    fold_many1(
        pair(
            lift_parser(preceded(multispace0, equiv_op)),
            preceded(lift_parser(multispace0), higher_than_equiv),
        ),
        move || first.clone(),
        |init, (_, g)| {
            PLTLParseTree::new_binary(
                BinaryOp::Or,
                PLTLParseTree::new_binary(BinaryOp::And, init.clone(), g.clone()),
                PLTLParseTree::new_binary(
                    BinaryOp::And,
                    PLTLParseTree::new_unary(UnaryOp::Not, init.clone()),
                    PLTLParseTree::new_unary(UnaryOp::Not, g.clone()),
                ),
            )
        },
    )
    .parse(input)
}

pub fn parse<'a>(input: ParserInput<'a>) -> IResult<ParserInput<'a>, PLTLParseTree> {
    if let Some((remaining, result)) = input.get_cached(input.as_str()) {
        return Ok((remaining, result));
    }

    let (mut remaining, result) = alt((equiv, higher_than_equiv)).parse(input.clone())?;
    let new_input = remaining.input;
    remaining
        .borrow_mut()
        .cache(input.as_str(), new_input, result.clone());
    Ok((remaining, result))
}

impl FromStr for PLTLParseTree {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let input = ParserInput::new(s);
        match parse(input).finish() {
            Ok(result) => {
                if result.0.input.is_empty() {
                    Ok(result.1)
                } else {
                    Err(Error {
                        offset: s.len() - result.0.input.len(),
                    })
                }
            }
            Err(err) => Err(Error {
                offset: s.len() - err.input.input.len(),
            }),
        }
    }
}

impl PLTLParseTree {
    pub fn new_atom(s: impl Into<String>) -> Self {
        Self::Atom(s.into())
    }

    pub fn new_unary(op: UnaryOp, r: Self) -> Self {
        Self::Unary(op, Box::new(r))
    }

    pub fn new_binary(op: BinaryOp, l: Self, r: Self) -> Self {
        Self::Binary(op, Box::new(l), Box::new(r))
    }
}

impl fmt::Display for PLTLParseTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PLTLParseTree::Top => write!(f, "⊤"),
            PLTLParseTree::Bottom => write!(f, "⊥"),
            PLTLParseTree::Atom(s) => write!(f, "{s}"),
            PLTLParseTree::Unary(
                UnaryOp::Not,
                box content @ PLTLParseTree::Unary(UnaryOp::Not, _),
            ) => {
                write!(f, "{}{}", UnaryOp::Not, content)
            }
            PLTLParseTree::Unary(op, box content @ PLTLParseTree::Binary(_, _, _)) => {
                write!(f, "{op}({content})")
            }
            PLTLParseTree::Unary(op, box content) => write!(f, "{op}{content}"),
            PLTLParseTree::Binary(op, box lhs, box rhs) => {
                let lhs = match (op, lhs) {
                    (BinaryOp::And, PLTLParseTree::Binary(BinaryOp::And, _, _)) => {
                        format!("{lhs}")
                    }
                    (BinaryOp::Or, PLTLParseTree::Binary(BinaryOp::Or, _, _)) => format!("{lhs}"),
                    (_, PLTLParseTree::Binary(_, _, _)) => {
                        format!("({lhs})")
                    }
                    _ => format!("{lhs}"),
                };
                let rhs = match (op, rhs) {
                    (BinaryOp::And, PLTLParseTree::Binary(BinaryOp::And, _, _)) => {
                        format!("{rhs}")
                    }
                    (BinaryOp::Or, PLTLParseTree::Binary(BinaryOp::Or, _, _)) => format!("{rhs}"),
                    (_, PLTLParseTree::Binary(_, _, _)) => {
                        format!("({rhs})")
                    }
                    _ => format!("{rhs}"),
                };
                write!(f, "{lhs} {op} {rhs}")
            }
        }
    }
}

impl From<PLTLParseTree> for UnaryOp {
    fn from(value: PLTLParseTree) -> Self {
        match value {
            PLTLParseTree::Unary(op, _) => op,
            _ => panic!("Expected UnaryOp"),
        }
    }
}

impl From<PLTLParseTree> for BinaryOp {
    fn from(value: PLTLParseTree) -> Self {
        match value {
            PLTLParseTree::Binary(op, _, _) => op,
            _ => panic!("Expected BinaryOp"),
        }
    }
}

impl From<UnaryOp> for PLTLParseTree {
    fn from(value: UnaryOp) -> Self {
        PLTLParseTree::new_unary(value, PLTLParseTree::Bottom)
    }
}

impl From<BinaryOp> for PLTLParseTree {
    fn from(value: BinaryOp) -> Self {
        PLTLParseTree::new_binary(value, PLTLParseTree::Bottom, PLTLParseTree::Bottom)
    }
}

#[cfg(test)]
mod tests {
    

    use super::*;

    #[test]
    fn test_parse_with_cache() {
        let input = r"G (F (p ->  X (X q) | (r & (p S (r S (Y p)))) ))";
        let parser_input = ParserInput::new(input);
        let result = parse(parser_input).unwrap().1;
        assert_eq!("GF(¬p ∨ XXq ∨ (r ∧ (p S (r S Yp))))", result.to_string());
    }
    #[test]
    fn test_parse() {
        let input = r"a \lor b \lor c";
        let parser_input = ParserInput::new(input);
        let result = parse(parser_input).unwrap().1;
        assert_eq!(
            result,
            PLTLParseTree::new_binary(
                BinaryOp::Or,
                PLTLParseTree::new_binary(
                    BinaryOp::Or,
                    PLTLParseTree::new_atom("a"),
                    PLTLParseTree::new_atom("b")
                ),
                PLTLParseTree::new_atom("c")
            )
        );

        let input = r"\neg \bot";
        let parser_input = ParserInput::new(input);
        let result = parse(parser_input).unwrap().1;
        assert_eq!(
            result,
            PLTLParseTree::new_unary(UnaryOp::Not, PLTLParseTree::Bottom)
        );

        let input = r"X a \land \top";
        let parser_input = ParserInput::new(input);
        let result = parse(parser_input).unwrap().1;
        assert_eq!(
            result,
            PLTLParseTree::new_binary(
                BinaryOp::And,
                PLTLParseTree::new_unary(UnaryOp::Next, PLTLParseTree::new_atom("a")),
                PLTLParseTree::Top
            )
        );

        let input = r"a U Y b U c";
        let parser_input = ParserInput::new(input);
        let result = parse(parser_input).unwrap().1;
        assert_eq!(
            result,
            PLTLParseTree::new_binary(
                BinaryOp::Until,
                PLTLParseTree::new_binary(
                    BinaryOp::Until,
                    PLTLParseTree::new_atom("a"),
                    PLTLParseTree::new_unary(UnaryOp::Yesterday, PLTLParseTree::new_atom("b")),
                ),
                PLTLParseTree::new_atom("c")
            )
        );

        let input = r"a <-> b";
        let parser_input = ParserInput::new(input);
        let result = parse(parser_input).unwrap().1;
        assert_eq!(
            result,
            PLTLParseTree::new_binary(
                BinaryOp::Or,
                PLTLParseTree::new_binary(
                    BinaryOp::And,
                    PLTLParseTree::new_atom("a"),
                    PLTLParseTree::new_atom("b")
                ),
                PLTLParseTree::new_binary(
                    BinaryOp::And,
                    PLTLParseTree::new_unary(UnaryOp::Not, PLTLParseTree::new_atom("a")),
                    PLTLParseTree::new_unary(UnaryOp::Not, PLTLParseTree::new_atom("b"))
                )
            )
        );

        let input = r"a -> b";
        let parser_input = ParserInput::new(input);
        let result = parse(parser_input).unwrap().1;
        assert_eq!(
            result,
            PLTLParseTree::new_binary(
                BinaryOp::Or,
                PLTLParseTree::new_unary(UnaryOp::Not, PLTLParseTree::new_atom("a")),
                PLTLParseTree::new_atom("b")
            )
        );

        // let input = r"a U ";
        // let result = PLTL::from_string(input).unwrap_err();
        // assert_eq!(&input[result.offset..], " U ");
    }
}
