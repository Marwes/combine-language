extern crate parser_combinators;

use std::cell::RefCell;
use std::marker::PhantomData;
use std::borrow::Cow;
use parser_combinators::*;
use parser_combinators::char as pc;
use parser_combinators::combinator::{Between, FnParser, Skip};
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

pub struct LanguageDef<IS, I>
    where I: Parser<Output=char>
        , IS: Parser<Input=I::Input, Output=char> {
    pub ident_start: IS,
    pub ident: I,
    pub reserved: Vec<Cow<'static, str>>,
    pub comment_line: &'static str,
    pub comment_start: &'static str,
    pub comment_end: &'static str
}

pub struct Env<'a, I> {
    ident_start: RefCell<Box<Parser<Input=I, Output=char> + 'a>>,
    ident: RefCell<Box<Parser<Input=I, Output=char> + 'a>>,
    reserved: Vec<Cow<'static, str>>,
    comment_line: &'static str,
    comment_start: &'static str,
    comment_end: &'static str,
    _marker: PhantomData<fn (I) -> I>
}

impl <'a, I> Env<'a, I>
    where I: Stream<Item=char> {

    pub fn new<A, B>(def: LanguageDef<A, B>) -> Env<'a, I>
        where A: Parser<Input=I, Output=char> + 'a
            , B: Parser<Input=I, Output=char> + 'a {
        let LanguageDef {
            ident_start,
            ident,
            reserved,
            comment_line,
            comment_start,
            comment_end
        } = def;
        Env {
            ident_start: RefCell::new(Box::new(ident_start)),
            ident: RefCell::new(Box::new(ident)),
            reserved: reserved,
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

    pub fn ident<'b>(&'b self) -> EnvParser<'a, 'b, I, String> {
        self.parser(Env::<I>::parse_ident)
    }
    pub fn symbol<'b>(&'b self, name: &'static str) -> Lex<'a, 'b, pc::String<I>> {
        self.lex(string(name))
    }

    pub fn parse_ident(&self, input: State<I>) -> ParseResult<String, I> {
        let mut start = self.ident_start.borrow_mut();
        let mut rest = self.ident.borrow_mut();
        let mut ident_parser = self.lex((&mut *start).and(many(&mut *rest)))
            .map(|(c, mut s): (char, ::std::string::String)| { s.insert(0, c); s });
        let (s, input) = try!(ident_parser.parse_state(input));
        match self.reserved.iter().find(|r| **r == s) {
            Some(ref _reserved) => {
                Err(input.map(|input| ParseError::new(input.position, Error::Expected("identifier".into()))))
            }
            None => Ok((s, input))
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
        let mut back_slash_char = satisfy(|c| "\"\\/bfnrt".chars().find(|x| *x == c).is_some()).map(|c| {
            match c {
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
        });
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
        let (s, input) = try!(many1::<::std::string::String, _>(digit())
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
            .map(|digits: ::std::string::String| {
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

#[cfg(test)]
mod tests {
    use super::*;
    use parser_combinators::*;
    
    fn env() -> Env<'static, &'static str> {
        Env::new(LanguageDef { 
            ident_start: letter(),
            ident: alpha_num(),
            reserved: ["if", "then", "else", "let", "in", "type"].iter().map(|x| (*x).into()).collect(),
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
    fn integer_literal() {
        let result = env().integer()
            .parse("213  ");
        assert_eq!(result, Ok((213, "")));
    }
}
