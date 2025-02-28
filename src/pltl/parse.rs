use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, char, multispace0, one_of},
    combinator::{map, recognize},
    multi::{fold_many1, many0, many1},
    sequence::{delimited, pair, preceded},
    IResult, Parser,
};

use super::{BinaryOp, UnaryOp, PLTL};

fn not_op(input: &str) -> IResult<&str, UnaryOp> {
    map(alt((tag("!"), tag("¬"), tag("\\neg"))), |_| UnaryOp::Not).parse(input)
}

fn temporal_unary_op(input: &str) -> IResult<&str, UnaryOp> {
    const OPS: [(&'static str, UnaryOp); 8] = [
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

fn temporal_binary_op(input: &str) -> IResult<&str, BinaryOp> {
    const OPS: [(&'static str, BinaryOp); 10] = [
        ("U", BinaryOp::Until),
        ("S", BinaryOp::Since),
        ("W", BinaryOp::WeakUntil),
        ("~S", BinaryOp::WeakSince),
        ("\\widetilde{S}", BinaryOp::WeakSince),
        ("M", BinaryOp::MightyRelease),
        ("B", BinaryOp::Before),
        ("R", BinaryOp::Release),
        ("~B", BinaryOp::WeakBefore),
        ("\\widetilde{B}", BinaryOp::WeakBefore),
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

fn top(input: &str) -> IResult<&str, PLTL> {
    map(alt((tag("⊤"), tag("\\top"), tag("1"))), |_| PLTL::Top).parse(input)
}

fn bottom(input: &str) -> IResult<&str, PLTL> {
    map(alt((tag("⊥"), tag("\\bot"), tag("0"))), |_| PLTL::Bottom).parse(input)
}

fn atom(input: &str) -> IResult<&str, PLTL> {
    let first = one_of("abcdefghijklmnopqrstuvwxyz_αβγδεζηθικλμνξοπρστυφϕχψω");
    let rest = recognize(many0(alt((
        alphanumeric1,
        recognize(one_of("_αβγδεζηθικλμνξοπρστυφχψω")),
    ))));
    map(pair(first, rest), |(f, r): (char, &str)| {
        PLTL::Atom(format!("{}{}", f, r))
    })
    .parse(input)
}

fn in_parantheses(input: &str) -> IResult<&str, PLTL> {
    delimited(
        preceded(multispace0, char('(')),
        parse,
        preceded(multispace0, char(')')),
    )
    .parse(input)
}

fn higher_than_not(input: &str) -> IResult<&str, PLTL> {
    alt((in_parantheses, atom, top, bottom)).parse(input)
}

fn parse_not(input: &str) -> IResult<&str, PLTL> {
    map(
        pair(
            many1(preceded(multispace0, not_op)),
            preceded(multispace0, higher_than_not),
        ),
        |(mut unary_ops, mut r)| {
            while let Some(op) = unary_ops.pop() {
                r = PLTL::new_unary(op, r)
            }
            r
        },
    )
    .parse(input)
}

fn higher_than_temporal_unary(input: &str) -> IResult<&str, PLTL> {
    alt((parse_not, higher_than_not)).parse(input)
}

fn temporal_unary(input: &str) -> IResult<&str, PLTL> {
    map(
        pair(
            many1(preceded(multispace0, temporal_unary_op)),
            preceded(multispace0, higher_than_temporal_unary),
        ),
        |(mut unary_ops, mut r)| {
            while let Some(op) = unary_ops.pop() {
                r = PLTL::new_unary(op, r)
            }
            r
        },
    )
    .parse(input)
}

fn higher_than_temporal_binary(input: &str) -> IResult<&str, PLTL> {
    alt((temporal_unary, higher_than_temporal_unary)).parse(input)
}

fn temporal_binary(input: &str) -> IResult<&str, PLTL> {
    let (input, first) = higher_than_temporal_binary(input)?;
    fold_many1(
        pair(
            preceded(multispace0, temporal_binary_op),
            preceded(multispace0, higher_than_temporal_binary),
        ),
        move || first.clone(),
        |init, (op, g)| PLTL::new_binary(op, init, g),
    )
    .parse(input)
}

fn higher_than_and(input: &str) -> IResult<&str, PLTL> {
    alt((temporal_binary, higher_than_temporal_binary)).parse(input)
}

fn and(input: &str) -> IResult<&str, PLTL> {
    let (input, first) = higher_than_and(input)?;
    fold_many1(
        pair(
            preceded(multispace0, and_op),
            preceded(multispace0, higher_than_and),
        ),
        move || first.clone(),
        |init, (op, g)| PLTL::new_binary(op, init, g),
    )
    .parse(input)
}

fn higher_than_or(input: &str) -> IResult<&str, PLTL> {
    alt((and, higher_than_and)).parse(input)
}

fn or(input: &str) -> IResult<&str, PLTL> {
    let (input, first) = higher_than_or(input)?;
    fold_many1(
        pair(
            preceded(multispace0, or_op),
            preceded(multispace0, higher_than_or),
        ),
        move || first.clone(),
        |init, (op, g)| PLTL::new_binary(op, init, g),
    )
    .parse(input)
}

pub fn parse(input: &str) -> IResult<&str, PLTL> {
    alt((or, higher_than_or)).parse(input)
}

impl FromStr for PLTL {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let result = parse(s).map_err(|_| ())?;
        if result.0.is_empty() {
            Ok(result.1)
        } else {
            Err(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        let input = r"a \lor b \lor c";
        let result = parse(input).unwrap().1;
        assert_eq!(
            result,
            PLTL::new_binary(
                BinaryOp::Or,
                PLTL::new_binary(BinaryOp::Or, PLTL::new_atom("a"), PLTL::new_atom("b")),
                PLTL::new_atom("c")
            )
        );

        let input = r"\neg \bot";
        let result = parse(input).unwrap().1;
        assert_eq!(result, PLTL::new_unary(UnaryOp::Not, PLTL::Bottom));

        let input = r"X a \land \top";
        let result = parse(input).unwrap().1;
        assert_eq!(
            result,
            PLTL::new_binary(
                BinaryOp::And,
                PLTL::new_unary(UnaryOp::Next, PLTL::new_atom("a")),
                PLTL::Top
            )
        );

        let input = r"a U Y b U c";
        let result = parse(input).unwrap().1;
        assert_eq!(
            result,
            PLTL::new_binary(
                BinaryOp::Until,
                PLTL::new_binary(
                    BinaryOp::Until,
                    PLTL::new_atom("a"),
                    PLTL::new_unary(UnaryOp::Yesterday, PLTL::new_atom("b")),
                ),
                PLTL::new_atom("c")
            )
        );
    }
}
