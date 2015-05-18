extern crate parser_combinators;

use std::cell::RefCell;
use std::marker::PhantomData;
use std::borrow::Cow;
use parser_combinators::*;
use parser_combinators::char as pc;
use parser_combinators::combinator::{Between, FnParser, NotFollowedBy, Skip, Try};
use parser_combinators::primitives::{Consumed, Error, Stream, State};


pub struct EnvParser<'a: 'b, 'b, I: 'b, T> {
    env: &'b Env<'a, I>,
    parser: fn (&Env<'a, I>, State<I>) -> ParseResult<T, I>
}

impl <'a, 'b, I, O> Parser for EnvParser<'a, 'b, I, O>
    where I: Stream<Item=char> {
    type Output = O;
    type Input = I;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        (self.parser)(self.env, input)
    }
}

#[derive(Clone)]
pub struct Lex<'a: 'b, 'b, P>
    where P: Parser
        , P::Input: Stream<Item=char> + 'b {
    parser: Skip<P, WhiteSpace<'a, 'b, P::Input>>
}

impl <'a, 'b, P> Parser for Lex<'a, 'b, P>
    where P: Parser
        , P::Input: Stream<Item=char> + 'b {
    type Output = P::Output;
    type Input = P::Input;
    fn parse_state(&mut self, input: State<P::Input>) -> ParseResult<P::Output, P::Input> {
        self.parser.parse_state(input)
    }
}

#[derive(Clone)]
pub struct WhiteSpace<'a: 'b, 'b, I>
    where I: Stream<Item=char> + 'b {
    env: &'b Env<'a, I>
}

impl <'a, 'b, I> Parser for WhiteSpace<'a, 'b, I>
    where I: Stream<Item=char> + 'b {
    type Output = ();
    type Input = I;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<(), I> {
        let comment_start = self.env.comment_start;
        let comment_end = self.env.comment_end;
        let comment_line = self.env.comment_line;
        let first_char = comment_start.chars().next().unwrap();
        let linecomment = try(string(comment_line)).and(skip_many(satisfy(|c| c != '\n'))).map(|_| ());
        let blockcomment: &mut Parser<Input=I, Output=()> = &mut try(string(comment_start)).then(|_| parser(|input| {
            let mut input = Consumed::Empty(input);
            loop {
                match input.clone().combine(|input| satisfy(|c| c != first_char).parse_state(input)) {
                    Ok((_, rest)) => input = rest,
                    Err(_) => match input.clone().combine(|input| try(string(comment_end)).parse_state(input)) {
                        Ok((_, input)) => return Ok(((), input)),
                        Err(_) => match input.combine(|input| parser(any_char).parse_state(input)) {
                            Ok((_, rest)) => input = rest,
                            Err(err) => return Err(err)
                        }
                    }
                }
            }
        }));
        let whitespace = skip_many1(space()).or(linecomment).or(blockcomment);
        skip_many(whitespace)
            .parse_state(input)
    }
}

pub type Reserved<'a, 'b, I> = Lex<'a, 'b, Try<Skip<pc::String<I>, NotFollowedBy<EnvParser<'a, 'b, I, char>>>>>;

pub struct Identifier<PS, P>
    where PS: Parser<Output=char>
        , P: Parser<Input=PS::Input, Output=char> {
    pub start: PS,
    pub rest: P,
    pub reserved: Vec<Cow<'static, str>>
}

pub struct LanguageDef<IS, I, OS, O>
    where I: Parser<Output=char>
        , IS: Parser<Input=I::Input, Output=char>
        , O: Parser<Input=I::Input, Output=char>
        , OS: Parser<Input=I::Input, Output=char> {
    pub ident: Identifier<IS, I>,
    pub op: Identifier<OS, O>,
    pub comment_line: &'static str,
    pub comment_start: &'static str,
    pub comment_end: &'static str
}

pub struct Env<'a, I> {
    ident_start: RefCell<Box<Parser<Input=I, Output=char> + 'a>>,
    ident: RefCell<Box<Parser<Input=I, Output=char> + 'a>>,
    reserved: Vec<Cow<'static, str>>,
    op_start: RefCell<Box<Parser<Input=I, Output=char> + 'a>>,
    op: RefCell<Box<Parser<Input=I, Output=char> + 'a>>,
    op_reserved: Vec<Cow<'static, str>>,
    comment_line: &'static str,
    comment_start: &'static str,
    comment_end: &'static str,
    _marker: PhantomData<fn (I) -> I>
}

impl <'a, I> Env<'a, I>
    where I: Stream<Item=char> {

    pub fn new<A, B, C, D>(def: LanguageDef<A, B, C, D>) -> Env<'a, I>
        where A: Parser<Input=I, Output=char> + 'a
            , B: Parser<Input=I, Output=char> + 'a
            , C: Parser<Input=I, Output=char> + 'a
            , D: Parser<Input=I, Output=char> + 'a {
        let LanguageDef {
            ident: Identifier { start: ident_start, rest: ident_rest, reserved: ident_reserved },
            op: Identifier { start: op_start, rest: op_rest, reserved: op_reserved },
            comment_line,
            comment_start,
            comment_end
        } = def;
        Env {
            ident_start: RefCell::new(Box::new(ident_start)),
            ident: RefCell::new(Box::new(ident_rest)),
            reserved: ident_reserved,
            op_start: RefCell::new(Box::new(op_start)),
            op: RefCell::new(Box::new(op_rest)),
            op_reserved: op_reserved,
            comment_line: comment_line,
            comment_start: comment_start,
            comment_end: comment_end,
            _marker: PhantomData
        }
    }

    fn parser<'b, T>(&'b self, parser: fn (&Env<'a, I>, State<I>) -> ParseResult<T, I>) -> EnvParser<'a, 'b, I, T> {
        EnvParser { env: self, parser: parser }
    }

    pub fn lex<'b, P>(&'b self, p: P) -> Lex<'a, 'b, P>
        where P: Parser<Input=I> + 'b {
        Lex { parser: p.skip(self.white_space()) }
    }
    pub fn white_space<'b>(&'b self) -> WhiteSpace<'a, 'b, I> {
        WhiteSpace { env: self }
    }

    pub fn symbol<'b>(&'b self, name: &'static str) -> Lex<'a, 'b, pc::String<I>> {
        self.lex(string(name))
    }

    pub fn ident<'b>(&'b self) -> EnvParser<'a, 'b, I, String> {
        self.parser(Env::<I>::parse_ident)
    }

    fn parse_ident(&self, input: State<I>) -> ParseResult<String, I> {
        let mut start = self.ident_start.borrow_mut();
        let mut rest = self.ident.borrow_mut();
        let mut ident_parser = self.lex((&mut *start).and(many(&mut *rest)))
            .map(|(c, mut s): (char, String)| { s.insert(0, c); s });
        let (s, input) = try!(ident_parser.parse_state(input));
        match self.reserved.iter().find(|r| **r == s) {
            Some(ref _reserved) => {
                Err(input.map(|input| ParseError::new(input.position, Error::Expected("identifier".into()))))
            }
            None => Ok((s, input))
        }
    }

    pub fn reserved<'b>(&'b self, name: &'static str) -> Reserved<'a, 'b, I> {
        self.lex(try(string(name).skip(not_followed_by(self.parser(Env::<I>::ident_letter)))))
    }

    fn ident_letter(&self, input: State<I>) -> ParseResult<char, I> {
        self.ident.borrow_mut()
            .parse_state(input)
    }

    pub fn op<'b>(&'b self) -> EnvParser<'a, 'b, I, String> {
        self.parser(Env::<I>::parse_op)
    }

    fn parse_op(&self, input: State<I>) -> ParseResult<String, I> {
        let mut start = self.op_start.borrow_mut();
        let mut rest = self.op.borrow_mut();
        let mut op_parser = self.lex((&mut *start).and(many(&mut *rest)))
            .map(|(c, mut s): (char, String)| { s.insert(0, c); s });
        let (s, input) = try!(op_parser.parse_state(input));
        match self.op_reserved.iter().find(|r| **r == s) {
            Some(ref _reserved) => {
                Err(input.map(|input| ParseError::new(input.position, Error::Expected("operator".into()))))
            }
            None => Ok((s, input))
        }
    }

    pub fn reserved_op<'b>(&'b self, name: &'static str) -> Reserved<'a, 'b, I> {
        self.lex(try(string(name).skip(not_followed_by(self.parser(Env::<I>::op_letter)))))
    }

    fn op_letter(&self, input: State<I>) -> ParseResult<char, I> {
        self.op.borrow_mut()
            .parse_state(input)
    }

    pub fn char_literal<'b>(&'b self) -> EnvParser<'a, 'b, I, char> {
        self.parser(Env::<I>::char_literal_parser)
    }

    fn char_literal_parser(&self, input: State<I>) -> ParseResult<char, I> {
        self.lex(between(string("\'"), string("\'"), parser(Env::<I>::char)))
            .expected("character")
            .parse_state(input)
    }

    fn char(input: State<I>) -> ParseResult<char, I> {
        let (c, input) = try!(parser(any_char).parse_state(input));
        let mut back_slash_char = satisfy(|c| "'\\/bfnrt".chars().find(|x| *x == c).is_some()).map(escape_char);
        match c {
            '\\' => input.combine(|input| back_slash_char.parse_state(input)),
            '\''  => unexpected("'").parse_state(input.into_inner()).map(|_| unreachable!()),
            _    => Ok((c, input))
        }
    }

    pub fn string_literal<'b>(&'b self) -> EnvParser<'a, 'b, I, String> {
        self.parser(Env::<I>::string_literal_parser)
    }

    fn string_literal_parser(&self, input: State<I>) -> ParseResult<String, I> {
        self.lex(between(string("\""), string("\""), many(parser(Env::<I>::string_char))))
            .parse_state(input)
    }

    fn string_char(input: State<I>) -> ParseResult<char, I> {
        let (c, input) = try!(parser(any_char).parse_state(input));
        let mut back_slash_char = satisfy(|c| "\"\\/bfnrt".chars().find(|x| *x == c).is_some()).map(escape_char);
        match c {
            '\\' => input.combine(|input| back_slash_char.parse_state(input)),
            '"'  => unexpected("\"").parse_state(input.into_inner()).map(|_| unreachable!()),
            _    => Ok((c, input))
        }
    }

    pub fn angles<'b, P>(&'b self, parser: P) -> Between<Lex<'a, 'b, pc::String<I>>, Lex<'a, 'b, pc::String<I>>, P>
        where P: Parser<Input=I> {
        self.between("<", ">", parser)
    }
    pub fn braces<'b, P>(&'b self, parser: P) -> Between<Lex<'a, 'b, pc::String<I>>, Lex<'a, 'b, pc::String<I>>, P>
        where P: Parser<Input=I> {
        self.between("{", "}", parser)
    }
    
    pub fn brackets<'b, P>(&'b self, parser: P) -> Between<Lex<'a, 'b, pc::String<I>>, Lex<'a, 'b, pc::String<I>>, P>
        where P: Parser<Input=I> {
        self.between("[", "]", parser)
    }

    pub fn parens<'b, P>(&'b self, parser: P) -> Between<Lex<'a, 'b, pc::String<I>>, Lex<'a, 'b, pc::String<I>>, P>
        where P: Parser<Input=I> {
        self.between("(", ")", parser)
    }

    fn between<'b, P>(&'b self, start: &'static str, end: &'static str, parser: P)
        -> Between<Lex<'a, 'b, pc::String<I>>, Lex<'a, 'b, pc::String<I>>, P>
        where P: Parser<Input=I> {
        between(self.lex(string(start)), self.lex(string(end)), parser)
    }

    pub fn integer<'b>(&'b self) -> Lex<'a, 'b, FnParser<I, fn (State<I>) -> ParseResult<i64, I>>> {
        self.lex(parser(Env::integer_parser))
    }
    fn integer_parser(input: State<I>) -> ParseResult<i64, I> {
        let (s, input) = try!(many1::<String, _>(digit())
            .expected("integer")
            .parse_state(input));
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    pub fn float<'b>(&'b self) -> Lex<'a, 'b, FnParser<I, fn (State<I>) -> ParseResult<f64, I>>> {
        self.lex(parser(Env::float_parser))
    }

    fn float_parser(input: State<I>) -> ParseResult<f64, I> {
        let i = parser(Env::<I>::integer_parser).map(|x| x as f64);
        let fractional = many(digit())
            .map(|digits: String| {
                let mut magnitude = 1.0;
                digits.chars().fold(0.0, |acc, d| {
                    magnitude /= 10.0;
                    match d.to_digit(10) {
                        Some(d) => acc + (d as f64) * magnitude,
                        None => panic!("Not a digit")
                    }
                })
            });

        let exp = satisfy(|c| c == 'e' || c == 'E')
            .with(optional(string("-")).and(parser(Env::<I>::integer_parser)));
        optional(string("-"))
            .and(i)
            .map(|(sign, n)| if sign.is_some() { -n } else { n })
            .and(optional(string(".")).with(fractional))
            .map(|(x, y)| if x > 0.0 { x + y } else { x - y })
            .and(optional(exp))
            .map(|(n, exp_option)| {
                match exp_option {
                    Some((sign, e)) => {
                        let e = if sign.is_some() { -e } else { e };
                        n * 10.0f64.powi(e as i32)
                    }
                    None => n
                }
            })
            .expected("float")
            .parse_state(input)
    }
}

fn escape_char(c: char) -> char {
    match c {
        '\'' => '\'',
        '"' => '"',
        '\\' => '\\',
        '/' => '/',
        'b' => '\u{0008}',
        'f' => '\u{000c}',
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        c => c//Should never happen
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser_combinators::*;
    
    fn env() -> Env<'static, &'static str> {
        Env::new(LanguageDef { 
            ident: Identifier {
                start: letter(),
                rest: alpha_num(),
                reserved: ["if", "then", "else", "let", "in", "type"].iter().map(|x| (*x).into()).collect()
            },
            op: Identifier {
                start: satisfy(|c| "+-*/".chars().find(|x| *x == c).is_some()),
                rest: satisfy(|c| "+-*/".chars().find(|x| *x == c).is_some()),
                reserved: ["+", "-", "*", "/"].iter().map(|x| (*x).into()).collect()
            },
            comment_start: "/*",
            comment_end: "*/",
            comment_line: "//"
        })
    }

    #[test]
    fn string_literal() {
        let result = env().string_literal()
            .parse(r#""abc\n\r213" "#);
        assert_eq!(result, Ok(("abc\n\r213".to_string(), "")));
    }

    #[test]
    fn char_literal() {
        let e = env();
        let mut parser = e.char_literal();
        assert_eq!(parser.parse("'a'"), Ok(('a', "")));
        assert_eq!(parser.parse(r#"'\n'"#), Ok(('\n', "")));
        assert_eq!(parser.parse(r#"'\\'"#), Ok(('\\', "")));
        assert!(parser.parse(r#"'\1'"#).is_err());
        assert_eq!(parser.parse(r#"'"'"#), Ok(('"', "")));
        assert!(parser.parse(r#"'\"'"#).is_err());
    }

    #[test]
    fn integer_literal() {
        let result = env().integer()
            .parse("213  ");
        assert_eq!(result, Ok((213, "")));
    }

    #[test]
    fn identifier() {
        let e = env();
        let result = e.ident()
            .parse("a12bc");
        assert_eq!(result, Ok(("a12bc".to_string(), "")));
        assert!(e.ident().parse("1bcv").is_err());
        assert!(e.ident().parse("if").is_err());
        assert_eq!(e.reserved("if").parse("if"), Ok(("if", "")));
        assert!(e.reserved("if").parse("ifx").is_err());
    }

    #[test]
    fn operator() {
        let e = env();
        let result = e.op()
            .parse("++  ");
        assert_eq!(result, Ok(("++".to_string(), "")));
        assert!(e.ident().parse("+").is_err());
        assert_eq!(e.reserved_op("-").parse("-       "), Ok(("-", "")));
        assert!(e.reserved_op("-").parse("--       ").is_err());
    }
}
