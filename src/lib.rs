//! # Example
//!
//! ```
//! # extern crate combine;
//! # extern crate combine_language;
//! # use combine::{satisfy, Parser};
//! # use combine::char::{alpha_num, letter, string};
//! # use combine_language::{Identifier, LanguageEnv, LanguageDef};
//! # fn main() {
//! let env = LanguageEnv::new(LanguageDef {
//!     ident: Identifier {
//!         start: letter(),
//!         rest: alpha_num(),
//!         reserved: ["if", "then", "else", "let", "in", "type"].iter()
//!                                                              .map(|x| (*x).into())
//!                                                              .collect(),
//!     },
//!     op: Identifier {
//!         start: satisfy(|c| "+-*/".chars().any(|x| x == c)),
//!         rest: satisfy(|c| "+-*/".chars().any(|x| x == c)),
//!         reserved: ["+", "-", "*", "/"].iter().map(|x| (*x).into()).collect()
//!     },
//!     comment_start: string("/*").map(|_| ()),
//!     comment_end: string("*/").map(|_| ()),
//!     comment_line: string("//").map(|_| ()),
//! });
//! let id = env.identifier();//An identifier parser
//! let integer = env.integer();//An integer parser
//! let result = (id, integer).easy_parse("this /* Skips comments */ 42");
//! assert_eq!(result, Ok(((String::from("this"), 42), "")));
//! # }
//! ```

#[macro_use]
extern crate combine;

use combine::char::{char, digit, space, string, Str};
use combine::error::FastResult::*;
use combine::error::{Consumed, StreamError, Tracked};
use combine::parser::combinator::{no_partial, recognize, NotFollowedBy, Try};
use combine::parser::error::Expected;
use combine::parser::function::EnvParser;
use combine::parser::item::Token;
use combine::parser::sequence::{Between, Skip};
use combine::stream::{RangeStream, Resetable, Stream, StreamOnce};
use combine::{
    any, between, char, env_parser, from_str, many, not_followed_by, one_of, optional, parser,
    satisfy, skip_many, skip_many1, token, try, unexpected, ConsumedResult, ParseError,
    ParseResult, Parser,
};
use std::borrow::Cow;
use std::cell::RefCell;
use std::marker::PhantomData;

use combine::range::take;

pub type LanguageParser<'a, 'b, I, T> = Expected<EnvParser<&'b LanguageEnv<'a, I>, I, T>>;
pub type LexLanguageParser<'a, 'b, I, T> = Lex<'a, 'b, LanguageParser<'a, 'b, I, T>>;

/// A lexing parser for a language
pub struct Lex<'a: 'b, 'b, P>
where
    P: Parser,
    P::Input: Stream<Item = char> + 'b,
    <P::Input as StreamOnce>::Error:
        ParseError<char, <P::Input as StreamOnce>::Range, <P::Input as StreamOnce>::Position>,
{
    parser: Skip<P, WhiteSpace<'a, 'b, P::Input>>,
}

impl<'a, 'b, P> Parser for Lex<'a, 'b, P>
where
    P: Parser,
    P::Input: Stream<Item = char> + 'b,
    <P::Input as StreamOnce>::Error:
        ParseError<char, <P::Input as StreamOnce>::Range, <P::Input as StreamOnce>::Position>,
{
    type Input = P::Input;
    type Output = P::Output;
    type PartialState = ();

    fn parse_stream(&mut self, input: &mut P::Input) -> ParseResult<P::Output, P::Input> {
        self.parser.parse_stream(input)
    }
    fn parse_stream_consumed(
        &mut self,
        input: &mut P::Input,
    ) -> ConsumedResult<P::Output, P::Input> {
        self.parser.parse_stream_consumed(input)
    }
    fn parse_lazy(&mut self, input: &mut P::Input) -> ConsumedResult<P::Output, P::Input> {
        self.parser.parse_lazy(input).into()
    }
    fn add_error(&mut self, errors: &mut Tracked<<P::Input as StreamOnce>::Error>) {
        self.parser.add_error(errors);
    }
}

/// A whitespace parser for a language
#[derive(Clone)]
pub struct WhiteSpace<'a: 'b, 'b, I>
where
    I: Stream<Item = char> + 'b,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    env: &'b LanguageEnv<'a, I>,
}

impl<'a, 'b, I> Parser for WhiteSpace<'a, 'b, I>
where
    I: Stream<Item = char> + 'b,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    type Input = I;
    type Output = ();
    type PartialState = ();

    fn parse_lazy(&mut self, input: &mut I) -> ConsumedResult<(), I> {
        let mut comment_start = self.env.comment_start.borrow_mut();
        let mut comment_end = self.env.comment_end.borrow_mut();
        let mut comment_line = self.env.comment_line.borrow_mut();
        parse_comment(
            &mut **comment_start,
            &mut **comment_end,
            &mut **comment_line,
            input,
        ).into()
    }
}

fn parse_comment<I, P>(
    mut comment_start: P,
    mut comment_end: P,
    comment_line: P,
    input: &mut I,
) -> ParseResult<(), I>
where
    I: Stream<Item = char>,
    P: Parser<Input = I, Output = ()>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let linecomment: &mut (Parser<Input = I, Output = (), PartialState = _>) =
        &mut try(comment_line)
            .and(skip_many(satisfy(|c| c != '\n')))
            .map(|_| ());
    let blockcomment = parser(|input| {
        let (_, mut consumed) = try!(try(&mut comment_start).parse_lazy(input).into());
        loop {
            match consumed.combine(|_| try(&mut comment_end).parse_lazy(input).into()) {
                Ok((_, consumed)) => return Ok(((), consumed)),
                Err(_) => match consumed.combine(|_| any().parse_stream(input)) {
                    Ok((_, rest)) => consumed = rest,
                    Err(err) => return Err(err),
                },
            }
        }
    });
    let whitespace = skip_many1(space()).or(linecomment).or(blockcomment);
    skip_many(whitespace).parse_stream(input)
}

/// Parses a reserved word
pub struct Reserved<'a: 'b, 'b, I>
where
    I: Stream<Item = char> + 'b,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    parser: Lex<'a, 'b, Try<Skip<Str<I>, NotFollowedBy<LanguageParser<'a, 'b, I, char>>>>>,
}

impl<'a, 'b, I> Parser for Reserved<'a, 'b, I>
where
    I: Stream<Item = char> + 'b,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    type Input = I;
    type Output = &'static str;
    type PartialState = ();

    fn parse_stream(&mut self, input: &mut I) -> ParseResult<&'static str, I> {
        self.parser.parse_stream(input)
    }

    fn parse_stream_consumed(&mut self, input: &mut I) -> ConsumedResult<&'static str, I> {
        self.parser.parse_stream_consumed(input)
    }

    fn parse_lazy(&mut self, input: &mut I) -> ConsumedResult<&'static str, I> {
        self.parser.parse_lazy(input).into()
    }

    fn add_error(&mut self, errors: &mut Tracked<I::Error>) {
        self.parser.add_error(errors);
    }
}

/// Parses `P` between two delimiter characters
pub struct BetweenChar<'a: 'b, 'b, P>
where
    P: Parser,
    P::Input: Stream<Item = char> + 'b,
    <P::Input as StreamOnce>::Error:
        ParseError<char, <P::Input as StreamOnce>::Range, <P::Input as StreamOnce>::Position>,
{
    parser: Between<Lex<'a, 'b, Token<P::Input>>, Lex<'a, 'b, Token<P::Input>>, P>,
}

impl<'a, 'b, I, P> Parser for BetweenChar<'a, 'b, P>
where
    I: Stream<Item = char> + 'b,
    P: Parser<Input = I>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    type Input = I;
    type Output = P::Output;
    type PartialState = ();

    fn parse_stream(&mut self, input: &mut I) -> ParseResult<P::Output, I> {
        self.parser.parse_stream(input)
    }

    fn parse_stream_consumed(&mut self, input: &mut I) -> ConsumedResult<P::Output, I> {
        self.parser.parse_stream_consumed(input)
    }

    fn parse_lazy(&mut self, input: &mut I) -> ConsumedResult<P::Output, I> {
        self.parser.parse_lazy(input).into()
    }

    fn add_error(&mut self, errors: &mut Tracked<<P::Input as StreamOnce>::Error>) {
        self.parser.add_error(errors);
    }
}

/// Defines how to define an identifier (or operator)
pub struct Identifier<PS, P>
where
    PS: Parser<Output = char>,
    P: Parser<Input = PS::Input, Output = char>,
{
    /// Parses a valid starting character for an identifier
    pub start: PS,
    /// Parses the rest of the characthers in a valid identifier
    pub rest: P,
    /// A number of reserved words which cannot be identifiers
    pub reserved: Vec<Cow<'static, str>>,
}

/// A struct type which contains the necessary definitions to construct a language parser
pub struct LanguageDef<IS, I, OS, O, CL, CS, CE>
where
    I: Parser<Output = char>,
    IS: Parser<Input = I::Input, Output = char>,
    O: Parser<Input = I::Input, Output = char>,
    OS: Parser<Input = I::Input, Output = char>,
    CL: Parser<Input = I::Input, Output = ()>,
    CS: Parser<Input = I::Input, Output = ()>,
    CE: Parser<Input = I::Input, Output = ()>,
{
    /// How to parse an identifier
    pub ident: Identifier<IS, I>,
    /// How to parse an operator
    pub op: Identifier<OS, O>,
    /// Describes the start of a line comment
    pub comment_line: CL,
    /// Describes the start of a block comment
    pub comment_start: CS,
    /// Describes the end of a block comment
    pub comment_end: CE,
}

type IdentParser<'a, I> = (
    Box<Parser<Input = I, Output = char, PartialState = ()> + 'a>,
    Box<Parser<Input = I, Output = char, PartialState = ()> + 'a>,
);

/// A type containing parsers for a specific language.
/// For some parsers there are two version where the parser which ends with a `_` is a variant
/// which does not skip whitespace and comments after parsing the token itself.
pub struct LanguageEnv<'a, I> {
    ident: RefCell<IdentParser<'a, I>>,
    reserved: Vec<Cow<'static, str>>,
    op: RefCell<IdentParser<'a, I>>,
    op_reserved: Vec<Cow<'static, str>>,
    comment_line: RefCell<Box<Parser<Input = I, Output = (), PartialState = ()> + 'a>>,
    comment_start: RefCell<Box<Parser<Input = I, Output = (), PartialState = ()> + 'a>>,
    comment_end: RefCell<Box<Parser<Input = I, Output = (), PartialState = ()> + 'a>>,
    /// A buffer for storing characters when parsing numbers
    buffer: RefCell<String>,
    _marker: PhantomData<fn(I) -> I>,
}

impl<'a, I> LanguageEnv<'a, I>
where
    I: Stream<Item = char>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    /// Constructs a new parser from a language defintion
    pub fn new<A, B, C, D, E, F, G>(def: LanguageDef<A, B, C, D, E, F, G>) -> LanguageEnv<'a, I>
    where
        A: Parser<Input = I, Output = char> + 'a,
        B: Parser<Input = I, Output = char> + 'a,
        C: Parser<Input = I, Output = char> + 'a,
        D: Parser<Input = I, Output = char> + 'a,
        E: Parser<Input = I, Output = ()> + 'a,
        F: Parser<Input = I, Output = ()> + 'a,
        G: Parser<Input = I, Output = ()> + 'a,
    {
        let LanguageDef {
            ident:
                Identifier {
                    start: ident_start,
                    rest: ident_rest,
                    reserved: ident_reserved,
                },
            op:
                Identifier {
                    start: op_start,
                    rest: op_rest,
                    reserved: op_reserved,
                },
            comment_line,
            comment_start,
            comment_end,
        } = def;
        LanguageEnv {
            ident: RefCell::new((
                Box::new(no_partial(ident_start)),
                Box::new(no_partial(ident_rest)),
            )),
            reserved: ident_reserved,
            op: RefCell::new((
                Box::new(no_partial(op_start)),
                Box::new(no_partial(op_rest)),
            )),
            op_reserved: op_reserved,
            comment_line: RefCell::new(Box::new(no_partial(comment_line))),
            comment_start: RefCell::new(Box::new(no_partial(comment_start))),
            comment_end: RefCell::new(Box::new(no_partial(comment_end))),
            buffer: RefCell::new(String::new()),
            _marker: PhantomData,
        }
    }

    fn parser<'b, T>(
        &'b self,
        parser: fn(&LanguageEnv<'a, I>, &mut I) -> ParseResult<T, I>,
        expected: &'static str,
    ) -> LanguageParser<'a, 'b, I, T> {
        env_parser(self, parser).expected(expected)
    }

    /// Creates a lexing parser from `p`
    pub fn lex<'b, P>(&'b self, p: P) -> Lex<'a, 'b, P>
    where
        P: Parser<Input = I> + 'b,
    {
        Lex {
            parser: p.skip(self.white_space()),
        }
    }

    /// Skips spaces and comments
    pub fn white_space<'b>(&'b self) -> WhiteSpace<'a, 'b, I> {
        WhiteSpace { env: self }
    }

    /// Parses a symbol, lexing the stream if it is successful
    pub fn symbol<'b>(&'b self, name: &'static str) -> Lex<'a, 'b, Str<I>> {
        self.lex(string(name))
    }

    /// Parses an identifier, failing if it parses something that is a reserved identifier
    pub fn identifier<'b>(&'b self) -> LexLanguageParser<'a, 'b, I, String> {
        self.lex(self.identifier_())
    }

    pub fn identifier_<'b>(&'b self) -> LanguageParser<'a, 'b, I, String> {
        self.parser(LanguageEnv::<I>::parse_ident, "identifier")
    }

    fn parse_ident(&self, input: &mut I) -> ParseResult<String, I> {
        let mut ident = self.ident.borrow_mut();
        let (first, _) = try!(ident.0.parse_lazy(input).into());
        let mut buffer = String::new();
        buffer.push(first);
        let (s, consumed) = {
            let mut iter = (&mut *ident.1).iter(input);
            buffer.extend(iter.by_ref());
            // We definitely consumed the char `first` so make sure that the input is consumed
            try!(Consumed::Consumed(()).combine(|_| iter.into_result(buffer)))
        };
        match self.reserved.iter().find(|r| **r == s) {
            Some(ref _reserved) => Err(consumed.map(|_| {
                I::Error::from_error(
                    input.position(),
                    StreamError::expected_static_message("identifier"),
                ).into()
            })),
            None => Ok((s, consumed)),
        }
    }

    /// Parses an identifier, failing if it parses something that is a reserved identifier
    pub fn range_identifier<'b>(&'b self) -> LexLanguageParser<'a, 'b, I, &'a str>
    where
        I: RangeStream<Range = &'a str>,
    {
        self.lex(self.range_identifier_())
    }

    pub fn range_identifier_<'b>(&'b self) -> LanguageParser<'a, 'b, I, &'a str>
    where
        I: RangeStream<Range = &'a str>,
    {
        self.parser(LanguageEnv::<I>::parse_range_ident, "identifier")
    }

    fn parse_range_ident(&self, input: &mut I) -> ParseResult<&'a str, I>
    where
        I: RangeStream<Range = &'a str>,
    {
        let mut ident = self.ident.borrow_mut();
        let checkpoint = input.checkpoint();
        let (first, _) = try!(ident.0.parse_lazy(input).into());
        let len = {
            let mut iter = (&mut *ident.1).iter(input);
            iter.by_ref()
                .fold(first.len_utf8(), |acc, c| c.len_utf8() + acc)
        };
        input.reset(checkpoint);
        let (s, consumed) = try!(take(len).parse_lazy(input).into());
        match self.reserved.iter().find(|r| **r == s) {
            Some(ref _reserved) => Err(consumed.map(|_| {
                I::Error::from_error(
                    input.position(),
                    StreamError::expected_static_message("identifier"),
                ).into()
            })),
            None => Ok((s, consumed)),
        }
    }

    /// Parses the reserved identifier `name`
    pub fn reserved<'b>(&'b self, name: &'static str) -> Reserved<'a, 'b, I>
    where
        I::Range: 'b,
    {
        let ident_letter = self.parser(LanguageEnv::<I>::ident_letter, "identifier letter");
        Reserved {
            parser: self.lex(try(string(name).skip(not_followed_by(ident_letter)))),
        }
    }

    fn ident_letter(&self, input: &mut I) -> ParseResult<char, I> {
        self.ident.borrow_mut().1.parse_lazy(input).into()
    }

    /// Parses an operator, failing if it parses something that is a reserved operator
    pub fn op<'b>(&'b self) -> LexLanguageParser<'a, 'b, I, String> {
        self.lex(self.op_())
    }

    pub fn op_<'b>(&'b self) -> LanguageParser<'a, 'b, I, String> {
        self.parser(LanguageEnv::<I>::parse_op, "operator")
    }

    fn parse_op(&self, input: &mut I) -> ParseResult<String, I> {
        let mut op = self.op.borrow_mut();
        let (first, _) = try!(op.0.parse_lazy(input).into());
        let mut buffer = String::new();
        buffer.push(first);
        let (s, consumed) = {
            let mut iter = (&mut *op.1).iter(input);
            buffer.extend(iter.by_ref());
            // We definitely consumed the char `first` so make sure that the input is consumed
            try!(Consumed::Consumed(()).combine(|_| iter.into_result(buffer)))
        };
        match self.op_reserved.iter().find(|r| **r == s) {
            Some(ref _reserved) => Err(consumed.map(|_| {
                I::Error::from_error(
                    input.position(),
                    StreamError::expected_static_message("operator"),
                ).into()
            })),
            None => Ok((s, consumed)),
        }
    }

    /// Parses an identifier, failing if it parses something that is a reserved identifier
    pub fn range_op<'b>(&'b self) -> LexLanguageParser<'a, 'b, I, &'a str>
    where
        I: RangeStream<Range = &'a str>,
    {
        self.lex(self.range_op_())
    }

    pub fn range_op_<'b>(&'b self) -> LanguageParser<'a, 'b, I, &'a str>
    where
        I: RangeStream<Range = &'a str>,
    {
        self.parser(LanguageEnv::<I>::parse_range_op, "operator")
    }

    fn parse_range_op(&self, input: &mut I) -> ParseResult<&'a str, I>
    where
        I: RangeStream<Range = &'a str>,
    {
        let mut op = self.op.borrow_mut();
        let checkpoint = input.checkpoint();
        let (first, _) = try!(op.0.parse_lazy(input).into());
        let len = {
            let mut iter = (&mut *op.1).iter(input);
            iter.by_ref()
                .fold(first.len_utf8(), |acc, c| c.len_utf8() + acc)
        };
        input.reset(checkpoint);
        let (s, consumed) = try!(take(len).parse_lazy(input).into());
        match self.op_reserved.iter().find(|r| **r == s) {
            Some(ref _reserved) => Err(consumed.map(|_| {
                I::Error::from_error(
                    input.position(),
                    StreamError::expected_static_message("identifier"),
                ).into()
            })),
            None => Ok((s, consumed)),
        }
    }

    /// Parses the reserved operator `name`
    pub fn reserved_op<'b>(&'b self, name: &'static str) -> Lex<'a, 'b, Reserved<'a, 'b, I>>
    where
        I::Range: 'b,
    {
        self.lex(self.reserved_op_(name))
    }

    pub fn reserved_op_<'b>(&'b self, name: &'static str) -> Reserved<'a, 'b, I>
    where
        I::Range: 'b,
    {
        let op_letter = self.parser(LanguageEnv::<I>::op_letter, "operator letter");
        Reserved {
            parser: self.lex(try(string(name).skip(not_followed_by(op_letter)))),
        }
    }

    fn op_letter(&self, input: &mut I) -> ParseResult<char, I> {
        self.op.borrow_mut().1.parse_lazy(input).into()
    }

    /// Parses a character literal taking escape sequences into account
    pub fn char_literal<'b>(&'b self) -> LexLanguageParser<'a, 'b, I, char> {
        self.lex(self.char_literal_())
    }

    pub fn char_literal_<'b>(&'b self) -> LanguageParser<'a, 'b, I, char> {
        self.parser(LanguageEnv::<I>::char_literal_parser, "character")
    }

    fn char_literal_parser(&self, input: &mut I) -> ParseResult<char, I> {
        between(string("\'"), string("\'"), parser(LanguageEnv::<I>::char))
            .expected("character")
            .parse_lazy(input)
            .into()
    }

    fn char(input: &mut I) -> ParseResult<char, I> {
        let (c, consumed) = try!(any().parse_lazy(input).into());
        let mut back_slash_char =
            satisfy(|c| "'\\/bfnrt".chars().find(|x| *x == c).is_some()).map(escape_char);
        match c {
            '\\' => consumed.combine(|_| back_slash_char.parse_stream(input)),
            '\'' => unexpected("'").parse_stream(input).map(|_| unreachable!()),
            _ => Ok((c, consumed)),
        }
    }

    /// Parses a string literal taking character escapes into account
    pub fn string_literal<'b>(&'b self) -> LexLanguageParser<'a, 'b, I, String> {
        self.lex(self.string_literal_())
    }

    pub fn string_literal_<'b>(&'b self) -> LanguageParser<'a, 'b, I, String> {
        self.parser(LanguageEnv::<I>::string_literal_parser, "string")
    }

    fn string_literal_parser(&self, input: &mut I) -> ParseResult<String, I> {
        between(
            string("\""),
            string("\""),
            many(parser(LanguageEnv::<I>::string_char)),
        ).parse_lazy(input)
        .into()
    }

    fn string_char(input: &mut I) -> ParseResult<char, I> {
        let (c, consumed) = try!(any().parse_lazy(input).into());
        let mut back_slash_char =
            satisfy(|c| "\"\\/bfnrt".chars().find(|x| *x == c).is_some()).map(escape_char);
        match c {
            '\\' => consumed.combine(|_| back_slash_char.parse_stream(input)),
            '"' => unexpected("\"").parse_stream(input).map(|_| unreachable!()),
            _ => Ok((c, consumed)),
        }
    }

    /// Parses `p` inside angle brackets
    /// `< p >`
    pub fn angles<'b, P>(&'b self, parser: P) -> BetweenChar<'a, 'b, P>
    where
        P: Parser<Input = I>,
        I::Range: 'b,
    {
        self.between('<', '>', parser)
    }

    /// Parses `p` inside braces
    /// `{ p }`
    pub fn braces<'b, P>(&'b self, parser: P) -> BetweenChar<'a, 'b, P>
    where
        P: Parser<Input = I>,
        I::Range: 'b,
    {
        self.between('{', '}', parser)
    }

    /// Parses `p` inside brackets
    /// `[ p ]`
    pub fn brackets<'b, P>(&'b self, parser: P) -> BetweenChar<'a, 'b, P>
    where
        P: Parser<Input = I>,
        I::Range: 'b,
    {
        self.between('[', ']', parser)
    }

    /// Parses `p` inside parentheses
    /// `( p )`
    pub fn parens<'b, P>(&'b self, parser: P) -> BetweenChar<'a, 'b, P>
    where
        P: Parser<Input = I>,
        I::Range: 'b,
    {
        self.between('(', ')', parser)
    }

    fn between<'b, P>(&'b self, start: char, end: char, parser: P) -> BetweenChar<'a, 'b, P>
    where
        P: Parser<Input = I>,
        I::Range: 'b,
    {
        BetweenChar {
            parser: between(self.lex(char(start)), self.lex(char(end)), parser),
        }
    }

    /// Parses an integer
    pub fn integer<'b>(&'b self) -> LexLanguageParser<'a, 'b, I, i64> {
        self.lex(self.integer_())
    }

    pub fn integer_<'b>(&'b self) -> LanguageParser<'a, 'b, I, i64> {
        self.parser(LanguageEnv::integer_parser, "integer")
    }

    fn integer_parser(&self, input: &mut I) -> ParseResult<i64, I> {
        let mut buffer = self.buffer.borrow_mut();
        buffer.clear();
        let ((), consumed) = try!(LanguageEnv::push_digits(&mut buffer, input));
        match buffer.parse() {
            Ok(i) => Ok((i, consumed)),
            Err(_) => Err(consumed.map(|()| I::Error::empty(input.position()).into())),
        }
    }

    fn push_digits(buffer: &mut String, input: &mut I) -> ParseResult<(), I> {
        let mut iter = digit().iter(input);
        buffer.extend(&mut iter);
        iter.into_result(())
    }

    /// Parses a floating point number
    pub fn float<'b>(&'b self) -> LexLanguageParser<'a, 'b, I, f64> {
        self.lex(self.float_())
    }

    pub fn float_<'b>(&'b self) -> LanguageParser<'a, 'b, I, f64> {
        self.parser(|_, input| float().parse_stream(input), "float")
    }
}

pub fn float<I>() -> impl Parser<Input = I, Output = f64>
where
    I: Stream<Item = char>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    from_str(recognize::<String, _>((
        optional(token('-')),
        (token('.').and(skip_many1(digit())).map(|_| '0')).or((
            token('0').skip(not_followed_by(digit())).or((
                one_of("123456789".chars()),
                skip_many(digit()),
            )
                .map(|_| '0')),
            optional((token('.'), skip_many(digit()))),
        )
            .map(|_| '0')),
        optional((
            (one_of("eE".chars()), optional(one_of("+-".chars()))),
            skip_many1(digit()),
        )),
    ))).expected("float")
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
        c => c, //Should never happen
    }
}

/// Enumeration on fixities for the expression parser
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum Fixity {
    Left,
    Right,
}

/// Struct for encompassing the associativity of an operator
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct Assoc {
    /// Operator fixity
    pub fixity: Fixity,
    /// Operator precedence
    pub precedence: i32,
}

/// Expression parser which handles binary operators
#[derive(Clone, Debug)]
pub struct Expression<O, P, F> {
    term: P,
    op: O,
    f: F,
}

// Macro which breaks on empty consumed instead of returning
macro_rules! tryb {
    ($e: expr) => {
        match $e {
            EmptyOk(x) => (x, Consumed::Empty(())),
            ConsumedOk(x) => (x, Consumed::Consumed(())),
            EmptyErr(_) => break,
            ConsumedErr(err) => return Err(Consumed::Consumed(err.into())),
        }
    };
}

impl<O, P, F, T> Expression<O, P, F>
where
    O: Parser<Output = (T, Assoc)>,
    P: Parser<Input = O::Input>,
    F: Fn(P::Output, T, P::Output) -> P::Output,
{
    fn parse_expr(
        &mut self,
        min_precedence: i32,
        mut l: P::Output,
        mut consumed: Consumed<()>,
        input: &mut P::Input,
    ) -> ParseResult<P::Output, P::Input> {
        loop {
            let checkpoint = input.checkpoint();
            let ((op, op_assoc), rest) = tryb!(self.op.parse_lazy(input));

            if op_assoc.precedence < min_precedence {
                input.reset(checkpoint);
                return Ok((l, consumed));
            }

            let (mut r, rest) = try!(rest.combine(|_| self.term.parse_stream(input)));
            consumed = rest;

            loop {
                let checkpoint = input.checkpoint();
                let ((_, assoc), _) = tryb!(self.op.parse_lazy(input));
                input.reset(checkpoint);

                let proceed = assoc.precedence > op_assoc.precedence
                    || assoc.fixity == Fixity::Right && assoc.precedence == op_assoc.precedence;
                if !proceed {
                    break;
                }

                let (new_r, rest) = try!(self.parse_expr(assoc.precedence, r, consumed, input));
                r = new_r;
                consumed = rest;
            }
            l = (self.f)(l, op, r);
        }
        Ok((l, consumed))
    }
}

impl<O, P, F, T> Parser for Expression<O, P, F>
where
    O: Parser<Output = (T, Assoc)>,
    P: Parser<Input = O::Input>,
    F: Fn(P::Output, T, P::Output) -> P::Output,
{
    type Input = P::Input;
    type Output = P::Output;
    type PartialState = ();

    fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
        let (l, consumed) = ctry!(self.term.parse_lazy(input));
        self.parse_expr(0, l, consumed, input).into()
    }
    fn add_error(&mut self, errors: &mut Tracked<<P::Input as StreamOnce>::Error>) {
        self.term.add_error(errors);
    }
}

/// Constructs an expression parser out of a term parser, an operator parser and a function which
/// combines a binary expression to new expressions.
///
/// ```
/// # extern crate combine;
/// # extern crate combine_language;
/// # use combine::{many, Parser};
/// # use combine::char::{letter, spaces, string};
/// # use combine_language::{expression_parser, Assoc, Fixity};
/// use self::Expr::*;
/// #[derive(PartialEq, Debug)]
/// enum Expr {
///      Id(String),
///      Op(Box<Expr>, &'static str, Box<Expr>)
/// }
/// fn op(l: Expr, o: &'static str, r: Expr) -> Expr {
///     Op(Box::new(l), o, Box::new(r))
/// }
/// fn id(s: &str) -> Expr {
///     Id(String::from(s))
/// }
/// # fn main() {
/// let op_parser = string("+").or(string("*"))
///     .map(|op| {
///         let prec = match op {
///             "+" => 6,
///             "*" => 7,
///             _ => unreachable!()
///         };
///         (op, Assoc { precedence: prec, fixity: Fixity::Left })
///     })
///     .skip(spaces());
/// let term = many(letter())
///     .map(Id)
///     .skip(spaces());
/// let mut parser = expression_parser(term, op_parser, op);
/// let result = parser.easy_parse("a + b * c + d");
/// assert_eq!(result, Ok((op(op(id("a"), "+", op(id("b"), "*", id("c"))), "+", id("d")), "")));
/// # }
/// ```
pub fn expression_parser<O, P, F, T>(term: P, op: O, f: F) -> Expression<O, P, F>
where
    O: Parser<Output = (T, Assoc)>,
    P: Parser<Input = O::Input>,
    F: Fn(P::Output, T, P::Output) -> P::Output,
{
    Expression {
        term: term,
        op: op,
        f: f,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use combine::char::{alpha_num, letter, string};
    use combine::easy::Error;
    use combine::parser::combinator::opaque;
    use combine::*;

    fn env<I>() -> LanguageEnv<'static, I>
    where
        I: Stream<Item = char> + 'static,
        I::Error: ParseError<I::Item, I::Range, I::Position>,
    {
        LanguageEnv::new(LanguageDef {
            ident: Identifier {
                start: letter(),
                rest: alpha_num(),
                reserved: ["if", "then", "else", "let", "in", "type"]
                    .iter()
                    .map(|x| (*x).into())
                    .collect(),
            },
            op: Identifier {
                start: satisfy(|c| "+-*/".chars().find(|x| *x == c).is_some()),
                rest: satisfy(|c| "+-*/".chars().find(|x| *x == c).is_some()),
                reserved: ["+", "-", "*", "/"].iter().map(|x| (*x).into()).collect(),
            },
            comment_start: string("/*").map(|_| ()),
            comment_end: string("*/").map(|_| ()),
            comment_line: string("//").map(|_| ()),
        })
    }

    #[test]
    fn string_literal() {
        let result = env().string_literal().easy_parse(r#""abc\n\r213" "#);
        assert_eq!(result, Ok(("abc\n\r213".to_string(), "")));
    }

    #[test]
    fn char_literal() {
        let e = env();
        let mut parser = e.char_literal();
        assert_eq!(parser.easy_parse("'a'"), Ok(('a', "")));
        assert_eq!(parser.easy_parse(r#"'\n'"#), Ok(('\n', "")));
        assert_eq!(parser.easy_parse(r#"'\\'"#), Ok(('\\', "")));
        assert!(parser.easy_parse(r#"'\1'"#).is_err());
        assert_eq!(parser.easy_parse(r#"'"'"#), Ok(('"', "")));
        assert!(parser.easy_parse(r#"'\"'"#).is_err());
    }

    #[test]
    fn integer_literal() {
        let result = env().integer().easy_parse("213  ");
        assert_eq!(result, Ok((213, "")));
    }

    #[test]
    fn float_literal() {
        let result = env().float().easy_parse("123.456  ");
        assert_eq!(result, Ok((123.456, "")));

        let result = env().float().easy_parse("123.456e10  ");
        assert_eq!(result, Ok((123.456e10, "")));

        let result = env().float().easy_parse("123.456E-10  ");
        assert_eq!(result, Ok((123.456E-10, "")));

        let result = env().float().easy_parse("123e1 ");
        assert_eq!(result, Ok((123e1, "")));

        let result = env().float().easy_parse("0.1  ");
        assert_eq!(result, Ok((0.1, "")));

        let result = env().float().easy_parse(".1  ");
        assert_eq!(result, Ok((0.1, "")));

        let result = env().float().easy_parse("1.  ");
        assert_eq!(result, Ok((1.0, "")));

        let result = env().float().easy_parse("1e+0  ");
        assert_eq!(result, Ok((1.0, "")));

        let result = env().float().easy_parse("  ");
        assert!(result.is_err());

        let result = env().float().easy_parse(". ");
        assert!(result.is_err());

        let result = env().float().easy_parse("000.1  ");
        assert!(result.is_err());
    }

    #[test]
    fn identifier() {
        let e = env();
        let result = e.identifier().easy_parse("a12bc");
        assert_eq!(result, Ok(("a12bc".to_string(), "")));
        assert!(e.identifier().easy_parse("1bcv").is_err());
        assert!(e.identifier().easy_parse("if").is_err());
        assert_eq!(e.reserved("if").easy_parse("if"), Ok(("if", "")));
        assert!(e.reserved("if").easy_parse("ifx").is_err());
    }

    #[test]
    fn operator() {
        let e = env();
        let result = e.op().easy_parse("++  ");
        assert_eq!(result, Ok(("++".to_string(), "")));
        assert!(e.identifier().easy_parse("+").is_err());
        assert_eq!(e.reserved_op("-").easy_parse("-       "), Ok(("-", "")));
        assert!(e.reserved_op("-").easy_parse("--       ").is_err());
    }

    use self::Expr::*;
    #[derive(PartialEq, Debug)]
    enum Expr {
        Int(i64),
        Op(Box<Expr>, &'static str, Box<Expr>),
    }

    fn op(l: Expr, op: &'static str, r: Expr) -> Expr {
        Expr::Op(Box::new(l), op, Box::new(r))
    }

    fn test_expr1() -> (&'static str, Expr) {
        let mul_2_3 = op(Int(2), "*", Int(3));
        let div_4_5 = op(Int(4), "/", Int(5));
        (
            "1 + 2 * 3 - 4 / 5",
            op(op(Int(1), "+", mul_2_3), "-", div_4_5),
        )
    }
    fn test_expr2() -> (&'static str, Expr) {
        let mul_2_3_4 = op(op(Int(2), "*", Int(3)), "/", Int(4));
        let add_1_mul = op(Int(1), "+", mul_2_3_4);
        (
            "1 + 2 * 3 / 4 - 5 + 6",
            op(op(add_1_mul, "-", Int(5)), "+", Int(6)),
        )
    }

    parser!{
    fn op_parser[I]()(I) -> (&'static str, Assoc)
        where [I: Stream<Item = char>,]
    {
        opaque(|f| {
            let mut ops = ["*", "/", "+", "-", "^", "&&", "||", "!!"]
                .iter()
                .cloned()
                .map(string)
                .collect::<Vec<_>>();
            f(&mut choice(&mut ops[..])
                .map(|s| {
                    let prec = match s {
                        "||" => 2,
                        "&&" => 3,
                        "+" | "-" => 6,
                        "*" | "/" => 7,
                        "^" => 8,
                        "!!" => 9,
                        _ => panic!("Impossible"),
                    };
                    let fixity = match s {
                        "+" | "-" | "*" | "/" => Fixity::Left,
                        "^" | "&&" | "||" => Fixity::Right,
                        _ => panic!("Impossible"),
                    };
                    (
                        s,
                        Assoc {
                            fixity: fixity,
                            precedence: prec,
                        },
                    )
                }))
        })
    }
    }

    #[test]
    fn expression() {
        let e = env();
        let mut expr = expression_parser(e.integer().map(Expr::Int), e.lex(op_parser()), op);
        let (s1, e1) = test_expr1();
        let result = expr.easy_parse(s1);
        assert_eq!(result, Ok((e1, "")));
        let (s2, e2) = test_expr2();
        let result = expr.easy_parse(s2);
        assert_eq!(result, Ok((e2, "")));
    }
    #[test]
    fn right_assoc_expression() {
        let e = env();
        let mut expr = expression_parser(e.integer().map(Expr::Int), e.lex(op_parser()), op);
        let result = expr.easy_parse("1 + 2 * 3 ^ 4 / 5");
        let power_3_4 = op(Int(3), "^", Int(4));
        let mul_2_3_5 = op(op(Int(2), "*", power_3_4), "/", Int(5));
        let add_1_mul = op(Int(1), "+", mul_2_3_5);
        assert_eq!(result, Ok((add_1_mul, "")));
        let result = expr.easy_parse("1 ^ 2 && 3 ^ 4");
        let e_1_2 = op(Int(1), "^", Int(2));
        let e_3_4 = op(Int(3), "^", Int(4));
        assert_eq!(result, Ok((op(e_1_2, "&&", e_3_4), "")));
    }
    #[test]
    fn expression_error() {
        let e = env();
        let mut expr = expression_parser(e.integer().map(Expr::Int), e.lex(op_parser()), op);
        let errors = expr.easy_parse("+ 1").map_err(|err| err.errors);
        assert_eq!(
            errors,
            Err(vec![
                Error::Unexpected('+'.into()),
                Error::Expected("integer".into()),
            ])
        );
    }

    #[test]
    fn range_identifier() {
        let e = env();
        let mut id = e.range_identifier();
        assert_eq!(id.easy_parse("t"), Ok(("t", "")));
        assert_eq!(id.easy_parse("test123 123"), Ok(("test123", "123")));
        assert_eq!(
            id.easy_parse("123").map_err(|err| err.errors),
            Err(vec![
                Error::Unexpected('1'.into()),
                Error::Expected("identifier".into()),
            ])
        );
    }

    #[test]
    fn range_operator() {
        let e = env();
        let mut id = e.range_op();
        assert_eq!(id.easy_parse("+-+ 123"), Ok(("+-+", "123")));
        assert_eq!(
            id.easy_parse("abc").map_err(|err| err.errors),
            Err(vec![
                Error::Unexpected('a'.into()),
                Error::Expected("operator".into()),
            ])
        );
    }
}
