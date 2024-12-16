// mod basic;
// mod extended;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, char, multispace0, one_of},
    combinator::{map, recognize},
    multi::{many0, many1},
    sequence::{delimited, pair, preceded, tuple},
    IResult,
};

use super::PLTL;

fn top(input: &str) -> IResult<&str, PLTL> {
    map(alt((tag("⊤"), tag("1"))), |_| PLTL::Top)(input)
}

fn bottom(input: &str) -> IResult<&str, PLTL> {
    map(alt((tag("⊥"), tag("0"))), |_| PLTL::Bottom)(input)
}

fn atom(input: &str) -> IResult<&str, PLTL> {
    let first = one_of("abcdefghijklmnopqrstuvwxyz_αβγδεζηθικλμνξοπρστυφϕχψω");
    let rest = recognize(many0(alt((
        alphanumeric1,
        recognize(one_of("_αβγδεζηθικλμνξοπρστυφχψω")),
    ))));

    map(pair(first, rest), |(f, r): (char, &str)| {
        PLTL::Atom(format!("{}{}", f, r))
    })(input)
}

fn parse_in_parantheses(input: &str) -> IResult<&str, PLTL> {
    delimited(
        preceded(multispace0, char('(')),
        parse,
        preceded(multispace0, char(')')),
    )(input)
}

fn higher_than_unary(input: &str) -> IResult<&str, PLTL> {
    alt((parse_in_parantheses, atom, top, bottom))(input)
}

fn parse_unary(input: &str) -> IResult<&str, PLTL> {
    let unary_op = alt((
        tag("!"),
        tag("¬"),
        tag("X"),
        tag("Y"),
        tag("~Y"),
        tag("F"),
        tag("O"),
        tag("G"),
        tag("H"),
    ));
    map(
        pair(
            many1(preceded(multispace0, unary_op)),
            preceded(multispace0, higher_than_unary),
        ),
        |(mut unary_ops, mut r)| {
            while let Some(op) = unary_ops.pop() {
                r = match op {
                    "!" | "¬" => PLTL::Not(Box::new(r)),
                    "X" => PLTL::Eventually(Box::new(r)),
                    "Y" => PLTL::Yesterday(Box::new(r)),
                    "~Y" => PLTL::WeakYesterday(Box::new(r)),
                    "F" => PLTL::Eventually(Box::new(r)),
                    "O" => PLTL::Once(Box::new(r)),
                    "G" => PLTL::Globally(Box::new(r)),
                    "H" => PLTL::Historically(Box::new(r)),
                    _ => unreachable!(),
                };
            }
            r
        },
    )(input)
}

fn higher_than_binary(input: &str) -> IResult<&str, PLTL> {
    alt((parse_unary, higher_than_unary))(input)
}

fn parse_binary(input: &str) -> IResult<&str, PLTL> {
    let binary_op = alt((
        tag("∧"),
        tag("&"),
        tag("∨"),
        tag("|"),
        tag("U"),
        tag("S"),
        tag("W"),
        tag("~S"),
        tag("M"),
        tag("B"),
        tag("R"),
        tag("~B"),
    ));
    let (input, first) = higher_than_binary(input)?;
    let (input, rest) = many1(pair(
        preceded(multispace0, binary_op),
        preceded(multispace0, higher_than_binary),
    ))(input)?;
    let mut result = first;
    for (op, r) in rest {
        result = match op {
            "∧" | "&" => PLTL::And(Box::new(result), Box::new(r)),
            "∨" | "|" => PLTL::Or(Box::new(result), Box::new(r)),
            "U" => PLTL::Until(Box::new(result), Box::new(r)),
            "W" => PLTL::WeakUntil(Box::new(result), Box::new(r)),
            "S" => PLTL::Since(Box::new(result), Box::new(r)),
            "~S" => PLTL::WeakSince(Box::new(result), Box::new(r)),
            "M" => PLTL::MightyRelease(Box::new(result), Box::new(r)),
            "B" => PLTL::Before(Box::new(result), Box::new(r)),
            "R" => PLTL::Release(Box::new(result), Box::new(r)),
            "~B" => PLTL::WeakBefore(Box::new(result), Box::new(r)),
            _ => unreachable!(),
        };
    }
    Ok((input, result))
}

pub fn parse(input: &str) -> IResult<&str, PLTL> {
    alt((parse_binary, parse_unary, higher_than_unary))(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pltl::PLTL;

    #[test]
    fn test_parse() {
        let input = "⊥";
        let result = parse(input).unwrap().1;
        assert_eq!(result, PLTL::Bottom);

        let input = "F ϕ";
        let result = parse(input).unwrap().1;
        assert_eq!(
            result,
            PLTL::Eventually(Box::new(PLTL::Atom("ϕ".to_string())))
        );

        let input = "~Y a M b ∨ ¬c";
        let result = parse(input).unwrap().1;
        assert_eq!(format!("{}", result), r#"~Y a M b ∨ ¬c"#);

        let input = "(a∨b)";
        let result = parse(input).unwrap().1;
        assert_eq!(format!("{}", result), r#"a ∨ b"#);
    }
}
