//! Tokenizer for Lean 4 source text.
//!
//! The lexer is total: every byte of the input ends up inside exactly one
//! token, unclassifiable bytes included (as [`SyntaxKind::LEX_ERROR`]). That
//! property is what lets the parser rebuild the source verbatim from the tree.
//!
//! Where Lean's own lexical rules are surprising, this module follows Lean
//! rather than convention:
//!
//! * An identifier absorbs `.` only when an identifier character follows, so
//!   `Nat.succ` is a single token while `x.1` is `x`, `.`, `1`.
//! * `!` and `?` are identifier-continuation characters, which is why `simp?`
//!   and `Array.get!` are single identifiers — and why `a != b` needs spaces.
//! * Block comments nest, and `/--` / `/-!` open doc comments, which are
//!   significant tokens rather than trivia because they attach to declarations.

use crate::kind::{KEYWORDS, SYMBOLS, SyntaxKind};
use std::sync::LazyLock;

/// A single lexed token, including trivia.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RawToken<'a> {
    /// What kind of token this is.
    pub kind: SyntaxKind,
    /// The exact source text, so the tree can round-trip.
    pub text: &'a str,
    /// Byte offset of the token start.
    pub offset: u32,
    /// 1-based line number of the token start.
    pub line: u32,
    /// 0-based column of the token start, counted in Unicode code points
    /// (Lean's own notion of a column).
    pub col: u32,
}

impl RawToken<'_> {
    /// Byte offset just past the token.
    pub fn end(&self) -> u32 {
        self.offset + self.text.len() as u32
    }
}

/// Symbols sorted longest-first so that maximal-munch matching is correct:
/// `:=` must be tried before `:`, and `<;>` before `<`.
static SORTED_SYMBOLS: LazyLock<Vec<(&'static str, SyntaxKind)>> = LazyLock::new(|| {
    let mut syms = SYMBOLS.to_vec();
    syms.sort_by_key(|(text, _)| std::cmp::Reverse(text.len()));
    syms
});

/// Looks up a reserved word.
fn keyword_kind(text: &str) -> Option<SyntaxKind> {
    KEYWORDS
        .iter()
        .find(|(kw, _)| *kw == text)
        .map(|(_, kind)| *kind)
}

/// Lean's `isLetterLike`: the Unicode ranges usable as identifier starts.
///
/// The carve-outs matter: `λ` is excluded from lower Greek because it starts a
/// lambda, and `Π`/`Σ` are excluded from upper Greek because they are notation.
fn is_letter_like(c: char) -> bool {
    let v = c as u32;
    (c.is_alphabetic() && c.is_ascii())
        || (0x3b1..=0x3c9).contains(&v) && v != 0x3bb // lower Greek, not λ
        || (0x391..=0x3A9).contains(&v) && v != 0x3a0 && v != 0x3a3 // upper Greek, not Π Σ
        || (0x3ca..=0x3fb).contains(&v)
        || (0x1f00..=0x1ffe).contains(&v)
        || (0x2100..=0x214f).contains(&v) // letterlike symbols
        || (0x1d49c..=0x1d59f).contains(&v) // script / fraktur / double-struck
        || (0xa000..=0xa48c).contains(&v) // Yi
        || (0x4e00..=0x9fff).contains(&v) // CJK
        || (0x1100..=0x11ff).contains(&v) // Hangul Jamo
        || (0xac00..=0xd7a3).contains(&v) // Hangul syllables
        || (0x3040..=0x30ff).contains(&v) // Hiragana / Katakana
}

/// Subscript letters and digits, which Lean allows inside identifiers.
fn is_subscript(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v) // ₀-₉
        || (0x2090..=0x209c).contains(&v) // ₐ-ₜ
        || (0x1d62..=0x1d6a).contains(&v) // ᵢ-ᵪ
}

/// Can this character begin an identifier?
fn is_id_start(c: char) -> bool {
    is_letter_like(c) || c == '_'
}

/// Can this character continue an identifier?
fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || is_letter_like(c)
        || is_subscript(c)
        || matches!(c, '_' | '\'' | '!' | '?' | '\u{271d}')
}

/// The tokenizer state.
struct Lexer<'a> {
    src: &'a str,
    /// Current byte position.
    pos: usize,
    line: u32,
    col: u32,
    out: Vec<RawToken<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(src: &'a str) -> Self {
        Lexer {
            src,
            pos: 0,
            line: 1,
            col: 0,
            out: Vec::new(),
        }
    }

    /// The character at the current position.
    fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    /// The character `n` characters ahead.
    fn peek_nth(&self, n: usize) -> Option<char> {
        self.src[self.pos..].chars().nth(n)
    }

    /// True if the remaining input starts with `s`.
    fn starts_with(&self, s: &str) -> bool {
        self.src[self.pos..].starts_with(s)
    }

    /// Consumes one character, maintaining line and column counters.
    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        if c == '\n' {
            self.line += 1;
            self.col = 0;
        } else {
            self.col += 1;
        }
        Some(c)
    }

    /// Consumes characters while `pred` holds.
    fn bump_while(&mut self, mut pred: impl FnMut(char) -> bool) {
        while self.peek().is_some_and(&mut pred) {
            self.bump();
        }
    }

    /// Records a token spanning `start..self.pos`.
    fn push(&mut self, kind: SyntaxKind, start: usize, line: u32, col: u32) {
        self.out.push(RawToken {
            kind,
            text: &self.src[start..self.pos],
            offset: start as u32,
            line,
            col,
        });
    }

    fn run(mut self) -> Vec<RawToken<'a>> {
        while self.peek().is_some() {
            self.token();
        }
        self.out
    }

    fn token(&mut self) {
        let start = self.pos;
        let line = self.line;
        let col = self.col;
        let c = self.peek().expect("caller checked for input");

        let kind = if c.is_whitespace() {
            self.bump_while(char::is_whitespace);
            SyntaxKind::WHITESPACE
        } else if self.starts_with("--") {
            self.bump_while(|c| c != '\n');
            SyntaxKind::LINE_COMMENT
        } else if self.starts_with("/-") {
            self.block_comment()
        } else if c == '"' {
            self.string()
        } else if c == 'r' && matches!(self.peek_nth(1), Some('"' | '#')) && self.raw_string_ahead()
        {
            self.raw_string()
        } else if c.is_ascii_digit() {
            self.number()
        } else if c == '«' {
            self.escaped_ident()
        } else if is_id_start(c) && !(c == '_' && !self.peek_nth(1).is_some_and(is_id_rest)) {
            return self.ident_or_keyword(start, line, col);
        } else if c == '`' {
            self.backtick()
        } else if c == '\'' {
            self.char_literal()
        } else {
            self.symbol()
        };

        self.push(kind, start, line, col);
    }

    /// `/- ... -/`, which nests. `/--` and `/-!` are doc comments.
    fn block_comment(&mut self) -> SyntaxKind {
        self.bump(); // '/'
        self.bump(); // '-'
        let kind = match self.peek() {
            // `/---/` is an empty block comment, not a doc comment.
            Some('-') if !self.starts_with("-/") => {
                self.bump();
                SyntaxKind::DOC_COMMENT
            }
            Some('!') => {
                self.bump();
                SyntaxKind::MOD_DOC_COMMENT
            }
            _ => SyntaxKind::BLOCK_COMMENT,
        };
        let mut depth = 1usize;
        while depth > 0 {
            if self.peek().is_none() {
                break; // Unterminated: the comment runs to end of file.
            }
            if self.starts_with("/-") {
                self.bump();
                self.bump();
                depth += 1;
            } else if self.starts_with("-/") {
                self.bump();
                self.bump();
                depth -= 1;
            } else {
                self.bump();
            }
        }
        kind
    }

    /// `"..."` with Lean's escape sequences.
    fn string(&mut self) -> SyntaxKind {
        self.bump(); // opening quote
        loop {
            match self.peek() {
                None | Some('\n') => return SyntaxKind::LEX_ERROR, // unterminated
                Some('"') => {
                    self.bump();
                    return SyntaxKind::STRING;
                }
                Some('\\') => {
                    self.bump();
                    self.bump(); // the escaped character
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
    }

    /// Checks for `r"` or `r#*"` without consuming, so a bare `r` stays an ident.
    fn raw_string_ahead(&self) -> bool {
        let rest = &self.src[self.pos + 1..];
        let hashes = rest.chars().take_while(|&c| c == '#').count();
        rest[hashes..].starts_with('"')
    }

    /// `r"..."` or `r#"..."#`, where the hash count sets the terminator.
    fn raw_string(&mut self) -> SyntaxKind {
        self.bump(); // 'r'
        let mut hashes = 0;
        while self.peek() == Some('#') {
            self.bump();
            hashes += 1;
        }
        self.bump(); // opening quote
        let terminator = format!("\"{}", "#".repeat(hashes));
        loop {
            if self.peek().is_none() {
                return SyntaxKind::LEX_ERROR;
            }
            if self.starts_with(&terminator) {
                for _ in 0..terminator.chars().count() {
                    self.bump();
                }
                return SyntaxKind::RAW_STRING;
            }
            self.bump();
        }
    }

    /// Decimal, hex, octal, binary, and scientific literals.
    fn number(&mut self) -> SyntaxKind {
        if self.peek() == Some('0') {
            match self.peek_nth(1) {
                Some('x' | 'X') => {
                    self.bump();
                    self.bump();
                    self.bump_while(|c| c.is_ascii_hexdigit());
                    return SyntaxKind::NUMBER;
                }
                Some('b' | 'B') => {
                    self.bump();
                    self.bump();
                    self.bump_while(|c| matches!(c, '0' | '1'));
                    return SyntaxKind::NUMBER;
                }
                Some('o' | 'O') => {
                    self.bump();
                    self.bump();
                    self.bump_while(|c| ('0'..='7').contains(&c));
                    return SyntaxKind::NUMBER;
                }
                _ => {}
            }
        }
        self.bump_while(|c| c.is_ascii_digit());
        let mut scientific = false;
        // A `.` only continues the literal if a digit follows; `1.foo` is a
        // projection and `1..2` is a range.
        if self.peek() == Some('.') && self.peek_nth(1).is_some_and(|c| c.is_ascii_digit()) {
            scientific = true;
            self.bump();
            self.bump_while(|c| c.is_ascii_digit());
        }
        if matches!(self.peek(), Some('e' | 'E')) {
            let sign_len = usize::from(matches!(self.peek_nth(1), Some('+' | '-')));
            if self
                .peek_nth(1 + sign_len)
                .is_some_and(|c| c.is_ascii_digit())
            {
                scientific = true;
                self.bump(); // 'e'
                if sign_len == 1 {
                    self.bump();
                }
                self.bump_while(|c| c.is_ascii_digit());
            }
        }
        if scientific {
            SyntaxKind::SCIENTIFIC
        } else {
            SyntaxKind::NUMBER
        }
    }

    /// `«any text»`, which may appear as a component of a dotted name.
    fn escaped_ident(&mut self) -> SyntaxKind {
        self.bump(); // '«'
        loop {
            match self.bump() {
                None => return SyntaxKind::LEX_ERROR,
                Some('»') => break,
                Some(_) => {}
            }
        }
        self.continue_dotted_ident();
        SyntaxKind::IDENT
    }

    /// An identifier or reserved word.
    ///
    /// Takes the start position explicitly because keyword classification needs
    /// the finished text.
    fn ident_or_keyword(&mut self, start: usize, line: u32, col: u32) {
        self.bump_while(is_id_rest);
        self.continue_dotted_ident();
        let text = &self.src[start..self.pos];
        // Only an undotted, unescaped word can be a reserved word.
        let kind = keyword_kind(text).unwrap_or(SyntaxKind::IDENT);
        self.push(kind, start, line, col);
    }

    /// Absorbs `.name` components, which is what makes `Nat.succ` one token.
    fn continue_dotted_ident(&mut self) {
        while self.peek() == Some('.') {
            match self.peek_nth(1) {
                Some(c) if is_id_start(c) => {
                    self.bump(); // '.'
                    self.bump_while(is_id_rest);
                }
                Some('«') => {
                    self.bump(); // '.'
                    self.bump(); // '«'
                    loop {
                        match self.bump() {
                            None | Some('»') => break,
                            Some(_) => {}
                        }
                    }
                }
                // `x.1`, `x..y`, `x.` — the dot is a separate token.
                _ => break,
            }
        }
    }

    /// `` `name `` and ``` ``name ``` are name literals; `` `( `` opens a
    /// syntax quotation and is left to the parser.
    fn backtick(&mut self) -> SyntaxKind {
        let ticks = if self.starts_with("``") { 2 } else { 1 };
        let after = self.peek_nth(ticks);
        if after.is_some_and(|c| is_id_start(c) || c == '«') {
            for _ in 0..ticks {
                self.bump();
            }
            if self.peek() == Some('«') {
                self.escaped_ident();
            } else {
                self.bump_while(is_id_rest);
                self.continue_dotted_ident();
            }
            SyntaxKind::NAME_LIT
        } else {
            for _ in 0..ticks {
                self.bump();
            }
            if ticks == 2 {
                SyntaxKind::DOUBLE_BACKTICK
            } else {
                SyntaxKind::BACKTICK
            }
        }
    }

    /// `'c'`. A lone `'` that does not close falls back to a tick token.
    fn char_literal(&mut self) -> SyntaxKind {
        let save = (self.pos, self.line, self.col);
        self.bump(); // opening quote
        let ok = match self.peek() {
            Some('\\') => {
                self.bump();
                self.bump();
                self.peek() == Some('\'')
            }
            Some(c) if c != '\'' && c != '\n' => {
                self.bump();
                self.peek() == Some('\'')
            }
            _ => false,
        };
        if ok {
            self.bump(); // closing quote
            SyntaxKind::CHAR
        } else {
            (self.pos, self.line, self.col) = save;
            self.bump();
            SyntaxKind::TICK
        }
    }

    /// Longest-match punctuation, or a one-character error token.
    fn symbol(&mut self) -> SyntaxKind {
        for (text, kind) in SORTED_SYMBOLS.iter() {
            if self.starts_with(text) {
                for _ in 0..text.chars().count() {
                    self.bump();
                }
                return *kind;
            }
        }
        self.bump();
        SyntaxKind::LEX_ERROR
    }
}

/// Tokenizes `src`, including whitespace and comments.
///
/// Concatenating the `text` of every returned token reproduces `src` exactly.
pub fn lex(src: &str) -> Vec<RawToken<'_>> {
    Lexer::new(src).run()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Renders tokens compactly for assertions.
    fn dump(src: &str) -> String {
        lex(src)
            .iter()
            .map(|t| format!("{:?}({})", t.kind, t.text))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// The property the whole design rests on.
    fn assert_lossless(src: &str) {
        let joined: String = lex(src).iter().map(|t| t.text).collect();
        assert_eq!(joined, src, "lexer lost input");
    }

    #[test]
    fn dotted_names_are_one_token_but_projections_are_not() {
        assert_eq!(dump("Nat.succ"), "IDENT(Nat.succ)");
        assert_eq!(dump("x.1"), "IDENT(x) DOT(.) NUMBER(1)");
        assert_eq!(dump("x.foo"), "IDENT(x.foo)");
        assert_eq!(dump("a..b"), "IDENT(a) DOT_DOT(..) IDENT(b)");
    }

    #[test]
    fn bang_and_question_continue_identifiers() {
        assert_eq!(dump("simp?"), "IDENT(simp?)");
        assert_eq!(dump("Array.get!"), "IDENT(Array.get!)");
        // Faithful to Lean: without spaces the `!` binds to the identifier.
        assert_eq!(
            dump("a != b"),
            "IDENT(a) WHITESPACE( ) NE_ASCII(!=) WHITESPACE( ) IDENT(b)"
        );
    }

    #[test]
    fn block_comments_nest_and_doc_comments_are_distinct() {
        assert_eq!(
            dump("/- a /- b -/ c -/"),
            "BLOCK_COMMENT(/- a /- b -/ c -/)"
        );
        assert_eq!(dump("/-- doc -/"), "DOC_COMMENT(/-- doc -/)");
        assert_eq!(dump("/-! mod -/"), "MOD_DOC_COMMENT(/-! mod -/)");
        // `/--/` reads as an empty block comment; `/---/` as an empty doc
        // comment, since `-/` closes it immediately after the `/--` opener.
        assert_eq!(dump("/--/"), "BLOCK_COMMENT(/--/)");
        assert_eq!(dump("/---/"), "DOC_COMMENT(/---/)");
    }

    #[test]
    fn underscore_alone_is_a_hole() {
        assert_eq!(dump("_"), "UNDERSCORE(_)");
        assert_eq!(dump("_x"), "IDENT(_x)");
    }

    #[test]
    fn numbers_cover_lean_forms() {
        assert_eq!(dump("0xff"), "NUMBER(0xff)");
        assert_eq!(dump("0b1010"), "NUMBER(0b1010)");
        assert_eq!(dump("1.5e-3"), "SCIENTIFIC(1.5e-3)");
        assert_eq!(dump("1.foo"), "NUMBER(1) DOT(.) IDENT(foo)");
    }

    #[test]
    fn lambda_is_not_a_letter_even_though_greek_letters_are() {
        assert_eq!(dump("λ"), "LAMBDA(λ)");
        assert_eq!(dump("α"), "IDENT(α)");
        assert_eq!(dump("Σ"), "SIGMA(Σ)");
        assert_eq!(dump("γ₁"), "IDENT(γ₁)");
    }

    #[test]
    fn strings_chars_and_names() {
        assert_eq!(dump(r#""a\"b""#), r#"STRING("a\"b")"#);
        assert_eq!(dump(r##"r#"raw"#"##), r##"RAW_STRING(r#"raw"#)"##);
        assert_eq!(dump("'x'"), "CHAR('x')");
        assert_eq!(dump("'\\n'"), "CHAR('\\n')");
        assert_eq!(dump("`Nat.zero"), "NAME_LIT(`Nat.zero)");
        assert_eq!(dump("``foo"), "NAME_LIT(``foo)");
        assert_eq!(dump("`(x)"), "BACKTICK(`) L_PAREN(() IDENT(x) R_PAREN())");
    }

    #[test]
    fn maximal_munch_on_symbols() {
        assert_eq!(dump(":="), "COLON_EQ(:=)");
        assert_eq!(dump("<;>"), "SEQ_FOCUS(<;>)");
        assert_eq!(dump("|>."), "PIPE_RIGHT_DOT(|>.)");
        assert_eq!(dump("⁻¹"), "INV(⁻¹)");
    }

    #[test]
    fn positions_are_tracked_in_code_points() {
        let toks = lex("def f\n  := α β");
        let alpha = toks.iter().find(|t| t.text == "α").unwrap();
        assert_eq!((alpha.line, alpha.col), (2, 5));
    }

    #[test]
    fn nothing_is_ever_dropped() {
        for src in [
            "def f := 1",
            "/- unterminated",
            "\"unterminated",
            "theorem t : ∀ x, p x := by simp\n",
            "«weird name» := 3",
            "\u{1f600} unknown",
        ] {
            assert_lossless(src);
        }
    }
}
