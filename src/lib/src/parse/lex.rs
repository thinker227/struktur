use std::{collections::VecDeque, fmt::Display, ops::{Add, ControlFlow, FromResidual, Try}};

use crate::{parse::{IndentationHint, ParseError}, text_span::TextSpan};

#[derive(Debug, Clone, Copy)]
pub struct Token<'src> {
    pub kind: TokenKind,
    pub text: &'src str,
    pub span: TextSpan,
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(static_str) = self.kind.static_source() {
            write!(f, "{}", static_str.escape_debug())?;
        } else {
            write!(f, "{:?} `{}`", self.kind, self.text.escape_debug())?;
        }

        write!(f, " @ {}..{}", self.span.offset(), self.span.offset() + self.span.len())?;

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Equals,
    Backslash,
    DashGreaterThan,
    OpenParen,
    CloseParen,
    True,
    False,
    Let,
    In,
    Fun,
    If,
    Then,
    Else,
    Name,
    Number,
    _String,
    Newline,
    EnterBlock,
    ExitBlock,
    EndOfInput,
}

impl TokenKind {
    pub fn static_source(&self) -> Option<&'static str> {
        use TokenKind::*;
        match self {
            Equals => Some("="),
            Backslash => Some("\\"),
            DashGreaterThan => Some("->"),
            OpenParen => Some("("),
            CloseParen => Some(")"),
            True => Some("true"),
            False => Some("false"),
            Let => Some("let"),
            In => Some("in"),
            Fun => Some("fun"),
            If => Some("if"),
            Then => Some("then"),
            Else => Some("else"),
            Name => None,
            Number => None,
            _String => None,
            Newline => None,
            EnterBlock => None,
            ExitBlock => None,
            EndOfInput => None,
        }
    }
}

#[derive(Debug, Clone)]
enum LexError {
    Err(ParseError),
    Eoi,
}

#[derive(Debug, Clone)]
#[must_use]
enum LexResult<T> {
    Ok(T),
    Err(ParseError),
    Eoi,
}

impl<T> Try for LexResult<T> {
    type Output = T;

    type Residual = LexError;

    fn from_output(output: Self::Output) -> Self {
        Self::Ok(output)
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            LexResult::Ok(x) => ControlFlow::Continue(x),
            LexResult::Err(error) => ControlFlow::Break(LexError::Err(error)),
            LexResult::Eoi => ControlFlow::Break(LexError::Eoi)
        }
    }
}

impl<T> FromResidual for LexResult<T> {
    fn from_residual(residual: <Self as std::ops::Try>::Residual) -> Self {
        match residual {
            LexError::Err(error) => LexResult::Err(error),
            LexError::Eoi => LexResult::Eoi
        }
    }
}

impl<T> From<Option<T>> for LexResult<T> {
    fn from(value: Option<T>) -> Self {
        match value {
            Some(x) => LexResult::Ok(x),
            None => LexResult::Eoi
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct StrLen {
    chars: usize,
    bytes: usize,
}

impl Add for StrLen {
    type Output = StrLen;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            chars: self.chars + rhs.chars,
            bytes: self.bytes + rhs.bytes
        }
    }
}

struct PartialToken {
    kind: TokenKind,
    chars: usize,
}

enum BlockOp {
    Enter,
    Exit { levels: usize },
    Empty,
}

struct Block {
    size: StrLen,
    origin: TextSpan,
}

struct Lexer<'src> {
    source: &'src str,
    offset: usize,
    at_start: bool,
    blocks: VecDeque<Block>,
    tokens: Vec<Token<'src>>,
}

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            offset: 0,
            at_start: true,
            blocks: VecDeque::new(),
            tokens: Vec::new()
        }
    }

    fn current(&self) -> Option<char> {
        self.source.chars().next()
    }

    fn byte_length_of_chars(&self, count: usize) -> Option<usize> {
        let mut chars = self.source.chars();
        let mut bytes = 0;
        for _ in 0..count {
            bytes += chars.next()?.len_utf8();
        }
        Some(bytes)
    }

    fn consume_bytes(&mut self, bytes: usize) -> LexResult<&str> {
        if bytes >= self.source.len() {
            return LexResult::Eoi;
        }

        let text = &self.source[..bytes];
        self.source = &self.source[bytes..];
        self.offset += bytes;

        LexResult::Ok(text)
    }

    fn consume_chars(&mut self, chars: usize) -> LexResult<&str> {
        let bytes = LexResult::from(self.byte_length_of_chars(chars))?;
        self.consume_bytes(bytes)
    }

    fn peek(&self, chars: usize) -> Option<&str> {
        self.byte_length_of_chars(chars)
            .map(|bytes| &self.source[..bytes])
    }

    fn leading(&self, mut f: impl FnMut(char) -> bool) -> StrLen {
        let mut char_len = 0;
        let mut byte_len = 0;

        for c in self.source.chars() {
            if !f(c) {
                break;
            }

            char_len += 1;
            byte_len += c.len_utf8();
        }

        StrLen {
            chars: char_len,
            bytes: byte_len
        }
    }

    fn consume_whitespace(&mut self) -> LexResult<StrLen> {
        let len = self.leading(is_whitespace_not_newline);
        self.consume_bytes(len.bytes)?;
        LexResult::Ok(len)
    }

    fn construct_token(&self, token: PartialToken) -> LexResult<Token<'src>> {
        let PartialToken { kind, chars } = token;

        let bytes = LexResult::from(self.byte_length_of_chars(chars))?;
        let from = self.offset;
        let text = &self.source[..bytes];

        let token = Token {
            kind,
            text,
            span: TextSpan::new(from, bytes)
        };

        LexResult::Ok(token)
    }

    fn push_token(&mut self, token: PartialToken) -> LexResult<()> {
        let PartialToken { kind, chars } = token;

        let bytes = LexResult::from(self.byte_length_of_chars(chars))?;
        let from = self.offset;
        let text = &self.source[..bytes];
        self.source = &self.source[bytes..];
        self.offset += bytes;

        self.tokens.push(Token {
            kind,
            text,
            span: TextSpan::new(from, bytes)
        });

        LexResult::Ok(())
    }

    pub fn consume_blocks(&mut self) {
        while self.blocks.pop_back().is_some() {
            let token = Token {
                kind: TokenKind::ExitBlock,
                text: "",
                span: TextSpan::empty(self.offset),
            };
            self.tokens.push(token);
        }
    }

    pub fn lex_token(&mut self) -> LexResult<()> {
        let current = LexResult::from(self.current())?;

        if self.newline_indentation()? {
            return LexResult::Ok(());
        }

        if is_whitespace_not_newline(current) {
            _ = self.consume_whitespace();
            return LexResult::Ok(());
        }

        if let Some((name, len)) = self.name()? {
            let kind = keyword(name).unwrap_or(TokenKind::Name);
            self.push_token(PartialToken { chars: len.chars, kind })?;
            return LexResult::Ok(());
        }

        if let Some(len) = self.number()? {
            self.push_token(PartialToken { chars: len.chars, kind: TokenKind::Number })?;
            return LexResult::Ok(());
        }

        if let Some((len, kind)) = self.symbol() {
            self.push_token(PartialToken { chars: len.chars, kind })?;
            return LexResult::Ok(());
        }

        LexResult::Err(ParseError::UnknownCharacter {
            char_span: TextSpan::new(self.offset, current.len_utf8())
        })
    }

    fn newline_indentation(&mut self) -> LexResult<bool> {
        let newline = if self.at_start {
            None
        }
        else if LexResult::from(self.current())? == '\n' {
            let newline = self.construct_token(PartialToken { kind: TokenKind::Newline, chars: 1 })?;
            self.consume_chars(1)?;
            Some(newline)
        }
        else {
            return LexResult::Ok(false);
        };

        if let Some((op, len@StrLen { chars, bytes })) = self.indentation()? {
            match op {
                BlockOp::Enter => {
                    self.blocks.push_back(Block {
                        size: len,
                        origin: TextSpan::new(self.offset, bytes)
                    });
                    self.push_token(PartialToken {
                        chars,
                        kind: TokenKind::EnterBlock
                    })?;
                }
                BlockOp::Exit { levels } => {
                    for _ in 0..levels {
                        self.blocks.pop_back().unwrap();

                        let token = self.construct_token(PartialToken {
                            chars,
                            kind: TokenKind::ExitBlock
                        })?;
                        self.tokens.push(token);
                    }
                }
                BlockOp::Empty => {
                    if let Some(newline) = newline {
                        self.tokens.push(newline);
                    }

                    self.consume_bytes(bytes)?;
                }
            }

            LexResult::Ok(true)
        } else {
            LexResult::Ok(false)
        }
    }

    fn indentation(&self) -> LexResult<Option<(BlockOp, StrLen)>> {
        let mut newline = false;
        let whitespace_len = self.leading(|c| {
            if c == '\n' {
                newline = true;
                true
            } else {
                is_whitespace(c) && !newline
            }
        });

        if newline {
            return LexResult::Ok(Some((BlockOp::Empty, whitespace_len)));
        }

        let whitespace_str = &self.source[..whitespace_len.bytes];

        for (byte_offset, c) in whitespace_str.char_indices() {
            if c != ' ' {
                return LexResult::Err(ParseError::IllegalIndentation {
                    char_span: TextSpan::new(self.offset, byte_offset + c.len_utf8())
                });
            }
        }

        let mut size = 0;
        for (block_index, block) in self.blocks.iter().enumerate() {
            if whitespace_len.chars == size {
                // Indentation is equal to that of another smaller block level,
                // meaning that the indentation has decreased.
                let remaining = self.blocks.len() - block_index;
                return LexResult::Ok(Some((BlockOp::Exit { levels: remaining }, whitespace_len)));
            }

            let new_size = block.size.chars;
            if whitespace_len.chars < new_size {
                // Indentation is greater than the previous block level but less than the new one,
                // meaning that we have inconsistent indentation.
                return LexResult::Err(ParseError::InconsistentIndentation {
                    indentation: whitespace_len.chars,
                    indent_span: TextSpan::new(self.offset, whitespace_len.bytes),
                    blocks: self.blocks.iter()
                        .map(|block| IndentationHint {
                            indentation: block.size.chars,
                            span: block.origin
                        }).collect()
                });
            }

            size = new_size;
        }

        if whitespace_len.chars == size {
            // Indentation hasn't changed.
            LexResult::Ok(Some((BlockOp::Empty, whitespace_len)))
        } else {
            // Indentation has increased.
            LexResult::Ok(Some((BlockOp::Enter, whitespace_len)))
        }
    }

    fn name(&self) -> LexResult<Option<(&str, StrLen)>> {
        let mut first = true;
        let name_length = self.leading(|c| {
            if first {
                first = false;
                can_begin_name(c)
            } else {
                can_appear_in_name(c)
            }
        });

        if name_length.chars > 0 {
            LexResult::Ok(Some((&self.source[..name_length.bytes], name_length)))
        } else {
            LexResult::Ok(None)
        }
    }

    fn number(&self) -> LexResult<Option<StrLen>> {
        let number_length = self.leading(|c| c.is_ascii_digit());
        LexResult::Ok((number_length.chars > 0).then_some(number_length))
    }

    fn symbol(&self) -> Option<(StrLen, TokenKind)> {
        use TokenKind::*;

        let single = self.current()?;
        if let Some(kind) = match single {
            '=' => Some(Equals),
            '\\' => Some(Backslash),
            '(' => Some(OpenParen),
            ')' => Some(CloseParen),
            _ => None
        } {
            return Some(
                (StrLen { chars: 1, bytes: single.len_utf8() }, kind)
            );
        }

        let dual = self.peek(2)?;
        if let Some(kind) = match dual {
            "->" => Some(DashGreaterThan),
            _ => None
        } {
            return Some(
                (StrLen { chars: 2, bytes: dual.len() }, kind)
            );
        }

        None
    }
}

fn is_whitespace(c: char) -> bool {
    c.is_whitespace()
}

fn is_whitespace_not_newline(c: char) -> bool {
    c != '\n' && is_whitespace(c)
}

fn can_begin_name(c: char) -> bool {
    c.is_alphabetic()
    // || c.is_symbol() || c.is_punctuation_other() || c.is_punctuation_dash() || c.is_punctuation_connector()
}

fn can_appear_in_name(c: char) -> bool {
    can_begin_name(c) || c.is_numeric()
}

fn keyword(s: &str) -> Option<TokenKind> {
    use TokenKind::*;
    match s {
        "true" => Some(True),
        "false" => Some(False),
        "let" => Some(Let),
        "in" => Some(In),
        "fun" => Some(Fun),
        "if" => Some(If),
        "then" => Some(Then),
        "else" => Some(Else),
        _ => None
    }
}

#[derive(Debug, Clone)]
pub struct Lexed<'src> {
    pub tokens: Vec<Token<'src>>,
    pub eoi: Token<'static>,
}

pub fn lex<'src>(source: &'src str) -> Result<Lexed<'src>, ParseError> {
    let mut lexer = Lexer::new(source);

    loop {
        match lexer.lex_token() {
            LexResult::Ok(()) => {}
            LexResult::Err(error) => return Err(error),
            LexResult::Eoi => break
        }

        lexer.at_start = false;
    }

    lexer.consume_blocks();

    let tokens = lexer.tokens;

    let eoi = Token {
        kind: TokenKind::EndOfInput,
        text: "",
        span: TextSpan::empty(lexer.offset)
    };

    Ok(Lexed {
        tokens,
        eoi
    })
}

#[cfg(test)]
mod tests {
    use std::assert_matches::assert_matches;

    use super::*;

    fn print_result(res: &Result<Lexed, ParseError>) {
        match res {
            Ok(lexed) => {
                for t in &lexed.tokens {
                    println!("{}", t);
                }
                println!("{}", lexed.eoi);
            }
            Err(e) => println!("{e:?}")
        }
    }

    #[test]
    fn chars() {
        let s = "räksmörgås 夜は奇妙だ";

        let lexer = Lexer::new(s);

        assert_matches!(lexer.byte_length_of_chars(16), Some(29));
        assert_matches!(lexer.byte_length_of_chars(17), None);
    }

    #[test]
    fn indent() {
        let s = "a\n  b \n  c\n    d\ne";

        let result = lex(s);

        print_result(&result);
    }

    #[test]
    fn names() {
        let s = "a bc d0 åäö ä1";

        let result = lex(s);

        print_result(&result);
    }

    #[test]
    fn foo() {
        let s = "fac = fun\n    0 -> 1\n    n -> mul n (fac (sub n 1))";

        let result = lex(s);

        print_result(&result);
    }
}
