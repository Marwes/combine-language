# combine-language
This a crate providing an easy way of constructing parsers which can easily parse various programming languages. It has much of the same API as [Text.Parsec.Token](http://hackage.haskell.org/package/parsec-3.1.9/docs/Text-Parsec-Token.html) but are otherwise a bit different to fit in to the ownership model of rust. The crate is an extension of the [combine](https://github.com/Marwes/combine) crate.

## Example
```rust
extern crate combine;
extern crate combine_language;
use combine::{satisfy, Parser};
use combine::char::{alpha_num, letter, string};
use combine_language::{Identifier, LanguageEnv, LanguageDef};
fn main() {
    let env = LanguageEnv::new(LanguageDef {
        ident: Identifier {
            start: letter(),
            rest: alpha_num(),
            reserved: ["if", "then", "else", "let", "in", "type"].iter()
                                                                 .map(|x| (*x).into())
                                                                 .collect(),
        },
        op: Identifier {
            start: satisfy(|c| "+-*/".chars().any(|x| x == c)),
            rest: satisfy(|c| "+-*/".chars().any(|x| x == c)),
            reserved: ["+", "-", "*", "/"].iter().map(|x| (*x).into()).collect()
        },
        comment_start: string("/*").map(|_| ()),
        comment_end: string("*/").map(|_| ()),
        comment_line: string("//").map(|_| ()),
    });
    let id = env.identifier();//An identifier parser
    let integer = env.integer();//An integer parser
    let result = (id, integer).easy_parse("this /* Skips comments */ 42");
    assert_eq!(result, Ok(((String::from("this"), 42), "")));
}
```

## Links

[Documentation](https://marwes.github.io/combine-language/combine_language/index.html)

[combine](https://github.com/Marwes/combine)

## Unstable Features


* __range_stream__ Enables the `range_stream` feature in combine, allows some parsers exposed in this crate to be zero-copy
