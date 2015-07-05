extern crate parser_combinators;

use std::cell::RefCell;
use std::marker::PhantomData;
use std::borrow::Cow;
use parser_combinators::*;
use parser_combinators::primitives as prim;
use parser_combinators::char as pc;
use parser_combinators::combinator::{Between, FnParser, NotFollowedBy, Skip, Try, Token};
use parser_combinators::primitives::{Consumed, Error, Stream, State};

///A language parser
pub struct LanguageParser<'a: 'b, 'b, I: 'b, T>
    where I: Stream<Item=char> {
    env: &'b LanguageEnv<'a, I>,
    parser: fn (&LanguageEnv<'a, I>, State<I>) -> ParseResult<T, I>
}

impl <'a, 'b, I, O> Parser for LanguageParser<'a, 'b, I, O>
    where I: Stream<Item=char> {
    type Output = O;
    type Input = I;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        (self.parser)(self.env, input)
    }
}

///A lexing parser for a language
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

///A whitespace parser for a language
#[derive(Clone)]
pub struct WhiteSpace<'a: 'b, 'b, I>
    where I: Stream<Item=char> + 'b {
    env: &'b LanguageEnv<'a, I>
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
        let linecomment: &mut Parser<Input=I, Output=()> = &mut try(string(comment_line))
            .and(skip_many(satisfy(|c| c != '\n')))
            .map(|_| ());
        let blockcomment: &mut Parser<Input=I, Output=()> = &mut try(string(comment_start))
            .then(|_| parser(|input| {
            let mut input = Consumed::Empty(input);
            loop {
                match input.clone().combine(|input| satisfy(|c| c != first_char).parse_state(input)) {
                    Ok((_, rest)) => input = rest,
                    Err(_) => match input.clone().combine(|input| try(string(comment_end)).parse_state(input)) {
                        Ok((_, input)) => return Ok(((), input)),
                        Err(_) => match input.combine(|input| any().parse_state(input)) {
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

pub type Reserved<'a, 'b, I> = Lex<'a, 'b, Try<Skip<pc::String<I>, NotFollowedBy<LanguageParser<'a, 'b, I, char>>>>>;

pub type BetweenChar<'a, 'b, I, P> = Between<Lex<'a, 'b, Token<I>>, Lex<'a, 'b, Token<I>>, P>;

/// Defines how to define an identifier (or operator)
pub struct Identifier<PS, P>
    where PS: Parser<Output=char>
        , P: Parser<Input=PS::Input, Output=char> {
    ///Parses a valid starting character for an identifier
    pub start: PS,
    ///Parses the rest of the characthers in a valid identifier
    pub rest: P,
    ///A number of reserved words which cannot be identifiers
    pub reserved: Vec<Cow<'static, str>>
}

/// A struct type which contains the necessary definitions to construct a language parser
pub struct LanguageDef<IS, I, OS, O>
    where I: Parser<Output=char>
        , IS: Parser<Input=I::Input, Output=char>
        , O: Parser<Input=I::Input, Output=char>
        , OS: Parser<Input=I::Input, Output=char> {
    ///How to parse an identifier
    pub ident: Identifier<IS, I>,
    ///How to parse an operator
    pub op: Identifier<OS, O>,
    ///Describes the start of a line comment
    pub comment_line: &'static str,
    ///Describes the start of a block comment
    pub comment_start: &'static str,
    ///Describes the end of a block comment
    pub comment_end: &'static str
}

///A type containing parsers for a specific language.
pub struct LanguageEnv<'a, I> {
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

impl <'a, I> LanguageEnv<'a, I>
    where I: Stream<Item=char> {

    ///Constructs a new parser from a language defintion
    pub fn new<A, B, C, D>(def: LanguageDef<A, B, C, D>) -> LanguageEnv<'a, I>
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
        LanguageEnv {
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

    fn parser<'b, T>(&'b self, parser: fn (&LanguageEnv<'a, I>, State<I>) -> ParseResult<T, I>) -> LanguageParser<'a, 'b, I, T> {
        LanguageParser { env: self, parser: parser }
    }

    ///Creates a lexing parser from `p`
    pub fn lex<'b, P>(&'b self, p: P) -> Lex<'a, 'b, P>
        where P: Parser<Input=I> + 'b {
        Lex { parser: p.skip(self.white_space()) }
    }

    ///Skips spaces and comments
    pub fn white_space<'b>(&'b self) -> WhiteSpace<'a, 'b, I> {
        WhiteSpace { env: self }
    }

    ///Parses a symbol, lexing the stream if it is successful
    pub fn symbol<'b>(&'b self, name: &'static str) -> Lex<'a, 'b, pc::String<I>> {
        self.lex(string(name))
    }

    ///Parses an identifier, failing if it parses something that is a reserved identifier
    pub fn identifier<'b>(&'b self) -> LanguageParser<'a, 'b, I, String> {
        self.parser(LanguageEnv::<I>::parse_ident)
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

    ///Parses the reserved identifier `name`
    pub fn reserved<'b>(&'b self, name: &'static str) -> Reserved<'a, 'b, I> {
        self.lex(try(string(name).skip(not_followed_by(self.parser(LanguageEnv::<I>::ident_letter)))))
    }

    fn ident_letter(&self, input: State<I>) -> ParseResult<char, I> {
        self.ident.borrow_mut()
            .parse_state(input)
    }

    ///Parses an operator, failing if it parses something that is a reserved operator
    pub fn op<'b>(&'b self) -> LanguageParser<'a, 'b, I, String> {
        self.parser(LanguageEnv::<I>::parse_op)
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

    ///Parses the reserved operator `name`
    pub fn reserved_op<'b>(&'b self, name: &'static str) -> Reserved<'a, 'b, I> {
        self.lex(try(string(name).skip(not_followed_by(self.parser(LanguageEnv::<I>::op_letter)))))
    }

    fn op_letter(&self, input: State<I>) -> ParseResult<char, I> {
        self.op.borrow_mut()
            .parse_state(input)
    }

    ///Parses a character literal taking escape sequences into account
    pub fn char_literal<'b>(&'b self) -> LanguageParser<'a, 'b, I, char> {
        self.parser(LanguageEnv::<I>::char_literal_parser)
    }

    fn char_literal_parser(&self, input: State<I>) -> ParseResult<char, I> {
        self.lex(between(string("\'"), string("\'"), parser(LanguageEnv::<I>::char)))
            .expected("character")
            .parse_state(input)
    }

    fn char(input: State<I>) -> ParseResult<char, I> {
        let (c, input) = try!(any().parse_state(input));
        let mut back_slash_char = satisfy(|c| "'\\/bfnrt".chars().find(|x| *x == c).is_some()).map(escape_char);
        match c {
            '\\' => input.combine(|input| back_slash_char.parse_state(input)),
            '\''  => unexpected("'").parse_state(input.into_inner()).map(|_| unreachable!()),
            _    => Ok((c, input))
        }
    }

    ///Parses a string literal taking character escapes into account
    pub fn string_literal<'b>(&'b self) -> LanguageParser<'a, 'b, I, String> {
        self.parser(LanguageEnv::<I>::string_literal_parser)
    }

    fn string_literal_parser(&self, input: State<I>) -> ParseResult<String, I> {
        self.lex(between(string("\""), string("\""), many(parser(LanguageEnv::<I>::string_char))))
            .parse_state(input)
    }

    fn string_char(input: State<I>) -> ParseResult<char, I> {
        let (c, input) = try!(any().parse_state(input));
        let mut back_slash_char = satisfy(|c| "\"\\/bfnrt".chars().find(|x| *x == c).is_some()).map(escape_char);
        match c {
            '\\' => input.combine(|input| back_slash_char.parse_state(input)),
            '"'  => unexpected("\"").parse_state(input.into_inner()).map(|_| unreachable!()),
            _    => Ok((c, input))
        }
    }

    ///Parses `p` inside angle brackets
    ///`< p >`
    pub fn angles<'b, P>(&'b self, parser: P) -> BetweenChar<'a, 'b, I, P>
        where P: Parser<Input=I> {
        self.between('<', '>', parser)
    }

    ///Parses `p` inside braces
    ///`{ p }`
    pub fn braces<'b, P>(&'b self, parser: P) -> BetweenChar<'a, 'b, I, P>
        where P: Parser<Input=I> {
        self.between('{', '}', parser)
    }
    
    ///Parses `p` inside brackets
    ///`[ p ]`
    pub fn brackets<'b, P>(&'b self, parser: P) -> BetweenChar<'a, 'b, I, P>
        where P: Parser<Input=I> {
        self.between('[', ']', parser)
    }

    ///Parses `p` inside parentheses
    ///`( p )`
    pub fn parens<'b, P>(&'b self, parser: P) -> BetweenChar<'a, 'b, I, P>
        where P: Parser<Input=I> {
        self.between('(', ')', parser)
    }

    fn between<'b, P>(&'b self, start: char, end: char, parser: P) -> BetweenChar<'a, 'b, I, P>
        where P: Parser<Input=I> {
        between(self.lex(char(start)), self.lex(char(end)), parser)
    }

    ///Parses an integer
    pub fn integer<'b>(&'b self) -> Lex<'a, 'b, FnParser<I, fn (State<I>) -> ParseResult<i64, I>>> {
        self.lex(parser(LanguageEnv::integer_parser))
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

    ///Parses a floating point number
    pub fn float<'b>(&'b self) -> Lex<'a, 'b, FnParser<I, fn (State<I>) -> ParseResult<f64, I>>> {
        self.lex(parser(LanguageEnv::float_parser))
    }

    fn float_parser(input: State<I>) -> ParseResult<f64, I> {
        let i = parser(LanguageEnv::<I>::integer_parser).map(|x| x as f64);
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

        optional(string("-"))
            .and(i)
            .map(|(sign, n)| if sign.is_some() { -n } else { n })
            .and(optional(string(".")).with(fractional))
            .then(|(x, y)| parser(move |input| {
                let n = if x > 0.0 { x + y } else { x - y };
                let exp = satisfy(|c| c == 'e' || c == 'E')
                    .with(optional(string("-")).and(parser(LanguageEnv::<I>::integer_parser)));
                    optional(exp)
                    .map(|exp_option| {
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
            }))
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

///Enumeration on fixities for the expression parser
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum Fixity {
    Left,
    Right
}

///Struct for encompassing the associativity of an operator
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct Assoc {
    ///Operator fixity
    pub fixity: Fixity,
    ///Operator precedence
    pub precedence: i32
}


///Expression parser which handles binary operators
#[derive(Clone, Debug)]
pub struct Expression<O, P, F> {
    term: P,
    op: O,
    f: F
}

//Macro which breaks on empty consumed instead of returning
macro_rules! tryb {
    ($e: expr) => {
        match $e {
            Ok(x) => x,
            Err(Consumed::Empty(_)) => break,
            Err(err@Consumed::Consumed(_)) => return Err(err)
        }
    }
}

impl <O, P, F, T> Expression<O, P, F>
    where O: Parser<Output=(T, Assoc)>
        , P: Parser<Input=O::Input>
        , F: Fn(P::Output, T, P::Output) -> P::Output {

    fn parse_expr(&mut self, min_precedence: i32, mut l: P::Output, mut input: Consumed<State<P::Input>>)
        -> prim::ParseResult<P::Output, P::Input, <P::Input as Stream>::Item> {

        loop {
            let ((op, op_assoc), rest) = tryb!(self.op.parse_state(input.clone().into_inner()));
            if op_assoc.precedence < min_precedence {
                return Ok((l, input))
            }
            let (mut r, rest) = try!(rest.combine(|rest| self.term.parse_state(rest)));
            input = rest;
            loop {
                let ((lookahead, assoc), _) = tryb!(self.op.parse_state(input.clone().into_inner()));
                let proceed = assoc.precedence > op_assoc.precedence
                    || assoc.fixity == Fixity::Right && assoc.precedence == op_assoc.precedence;
                if !proceed {
                    break
                }
                let (new_r, rest) = try!(self.parse_expr(assoc.precedence, r, input));
                r = new_r;
                input = rest;
            }
            l = (self.f)(l, op, r);
        }
        Ok((l, input))
    }
}

impl <O, P, F, T> Parser for Expression<O, P, F> 
    where O: Parser<Output=(T, Assoc)>
        , P: Parser<Input=O::Input>
        , F: Fn(P::Output, T, P::Output) -> P::Output {
    type Input = P::Input;
    type Output = P::Output;
    fn parse_state(&mut self, input: State<Self::Input>) -> prim::ParseResult<Self::Output, Self::Input, <Self::Input as Stream>::Item> {
        let (l, input) = try!(self.term.parse_state(input));
        self.parse_expr(0, l, input)
    }
}

///Constructs an expression parser out of a term parser an operator parser and a function which
///combines a binary expression to a new expression
///
/// ```
/// # extern crate parser_combinators as pc;
/// # extern crate parser_combinators_language as pcl;
/// # use pc::*;
/// # use pcl::*;
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
/// let result = parser.parse("a + b * c + d");
/// assert_eq!(result, Ok((op(op(id("a"), "+", op(id("b"), "*", id("c"))), "+", id("d")), "")));
/// # }
/// ```
pub fn expression_parser<O, P, F, T>(term: P, op: O, f: F) -> Expression<O, P, F>
    where O: Parser<Output=(T, Assoc)>
        , P: Parser<Input=O::Input>
        , F: Fn(P::Output, T, P::Output) -> P::Output {
    Expression { term: term, op: op, f: f }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser_combinators::*;
    use parser_combinators::primitives::State;
    
    fn env() -> LanguageEnv<'static, &'static str> {
        LanguageEnv::new(LanguageDef { 
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
        let result = e.identifier()
            .parse("a12bc");
        assert_eq!(result, Ok(("a12bc".to_string(), "")));
        assert!(e.identifier().parse("1bcv").is_err());
        assert!(e.identifier().parse("if").is_err());
        assert_eq!(e.reserved("if").parse("if"), Ok(("if", "")));
        assert!(e.reserved("if").parse("ifx").is_err());
    }

    #[test]
    fn operator() {
        let e = env();
        let result = e.op()
            .parse("++  ");
        assert_eq!(result, Ok(("++".to_string(), "")));
        assert!(e.identifier().parse("+").is_err());
        assert_eq!(e.reserved_op("-").parse("-       "), Ok(("-", "")));
        assert!(e.reserved_op("-").parse("--       ").is_err());
    }

    use self::Expr::*;
    #[derive(PartialEq, Debug)]
    enum Expr {
        Int(i64),
        Op(Box<Expr>, &'static str, Box<Expr>)
    }

    fn op(l: Expr, op: &'static str, r: Expr) -> Expr {
        Expr::Op(Box::new(l), op, Box::new(r))
    }


    fn test_expr1() -> (&'static str, Expr) {
        let mul_2_3 = op(Int(2), "*", Int(3));
        let div_4_5 = op(Int(4), "/", Int(5));
        ("1 + 2 * 3 - 4 / 5", op(op(Int(1), "+", mul_2_3), "-", div_4_5))
    }
    fn test_expr2() -> (&'static str, Expr) {
        let mul_2_3_4 = op(op(Int(2), "*", Int(3)), "/", Int(4));
        let add_1_mul = op(Int(1), "+", mul_2_3_4);
        ("1 + 2 * 3 / 4 - 5 + 6", op(op(add_1_mul, "-", Int(5)), "+", Int(6)))
    }


    fn op_parser(input: State<&'static str>) -> ParseResult<(&'static str, Assoc), &'static str> {
        let mut ops = ["*", "/", "+", "-", "^", "&&", "||", "!!"]
            .iter()
            .cloned()
            .map(string)
            .collect::<Vec<_>>();
        choice(&mut ops[..])
            .map(|s| {
                let prec = match s {
                    "||" => 2,
                    "&&" => 3,
                    "+" | "-" => 6,
                    "*" | "/" => 7,
                    "^" => 8,
                    "!!" => 9,
                    _ => panic!("Impossible")
                };
                let fixity = match s {
                    "+" | "-" |"*" | "/" => Fixity::Left,
                    "^" | "&&" | "||"  => Fixity::Right,
                    _ => panic!("Impossible")
                };
                (s, Assoc { fixity: fixity, precedence: prec })
            })
            .parse_state(input)
    }

    #[test]
    fn expression() {
        let e = env();
        let mut expr = expression_parser(e.integer().map(Expr::Int), e.lex(parser(op_parser)), op);
        let (s1, e1) = test_expr1();
        let result = expr.parse(s1);
        assert_eq!(result, Ok((e1, "")));
        let (s2, e2) = test_expr2();
        let result = expr.parse(s2);
        assert_eq!(result, Ok((e2, "")));
    }
    #[test]
    fn right_assoc_expression() {
        let e = env();
        let mut expr = expression_parser(e.integer().map(Expr::Int), e.lex(parser(op_parser)), op);
        let result = expr.parse("1 + 2 * 3 ^ 4 / 5");
        let power_3_4 = op(Int(3), "^", Int(4));
        let mul_2_3_5 = op(op(Int(2), "*", power_3_4), "/", Int(5));
        let add_1_mul = op(Int(1), "+", mul_2_3_5);
        assert_eq!(result, Ok((add_1_mul, "")));
        let result = expr.parse("1 ^ 2 && 3 ^ 4");
        let e_1_2 = op(Int(1), "^", Int(2));
        let e_3_4 = op(Int(3), "^", Int(4));
        assert_eq!(result, Ok((op(e_1_2, "&&", e_3_4), "")));
    }
}
