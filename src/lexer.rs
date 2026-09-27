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
//! * Words introduced by tactic syntax — `only`, `using`, `generalizing` — are
//!   reserved words, not identifiers. Lean keeps a single global token table, so
//!   a word used as a token anywhere is a token everywhere.

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

/// Superscript and subscript modifier characters.
///
/// Lean notation uses these only as postfix — `sᶜ` for complement, `Xᵒᵖ` for
/// the opposite category, `‖x‖₊` for a non-negative norm — and they also modify
/// an operator they follow, which is why `→` and `→ₗ` are different arrows.
fn is_modifier(c: char) -> bool {
    let v = c as u32;
    matches!(v, 0xb2 | 0xb3 | 0xb9)
        || (0x2b0..=0x2ff).contains(&v)   // spacing modifier letters
        || (0x1d2c..=0x1d6a).contains(&v) // phonetic extensions (ᵒ ᵐ ᵖ)
        || (0x1d9b..=0x1dbf).contains(&v) // phonetic extensions supplement (ᶜ ᶠ)
        || (0x2070..=0x209c).contains(&v) // superscripts and subscripts
}

/// Could this character be part of notation?
///
/// Any non-ASCII character can be, and the rule has to be this permissive
/// because Lean's token table admits arbitrary strings: a library may declare
/// notation from any block it likes, and mathlib does. It uses `⁅x, y⁆` from
/// General Punctuation for Lie brackets and `Kᗮ` from *Canadian Syllabics* for
/// orthogonal complements. Enumerating Unicode's mathematical blocks was tried
/// first and left a tail of 94 characters that no principled block list would
/// have caught.
///
/// So the lexer cannot know that a character is *not* notation, and does not
/// guess. `LEX_ERROR` is left for what is genuinely malformed: control
/// characters, and unterminated literals.
fn is_notation_char(c: char) -> bool {
    !c.is_ascii() && !c.is_whitespace() && !c.is_control()
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

/// Suffixes that decorate a one-character type name into notation of its own:
/// `ℕ+` is `PNat`, `ℝ≥0` is `NNReal`, `ℝ≥0∞` is `ENNReal`. Longest first.
///
/// Applied only after a single non-ASCII letter, which is what keeps a
/// sloppily-spaced `a+ b` from lexing as the identifier `a+`.
const TYPE_SUFFIXES: &[&str] = &["\u{2265}0\u{221e}", "\u{2265}0", "+"];

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
        } else if self.starts_with("''") {
            // `f '' s` is `Set.image`, not two empty character literals.
            self.bump();
            self.bump();
            SyntaxKind::IMAGE
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
    ///
    /// An interpolated string — one written `s!"…"`, `m!"…"` and so on — may
    /// embed terms in `{…}`, and those terms may contain strings of their own:
    ///
    /// ```lean
    /// s!"one of {", ".intercalate names}"
    /// ```
    ///
    /// Terminating at the first `"` cuts that in half, so brace depth is tracked
    /// and a nested literal is scanned past. Depth is only tracked for an
    /// interpolated string, because `"{"` is a perfectly good ordinary one and
    /// tracking it there would never terminate.
    fn string(&mut self) -> SyntaxKind {
        let interpolated = self.after_interpolation_prefix();
        self.bump(); // opening quote
        let mut depth = 0usize;
        loop {
            match self.peek() {
                None => return SyntaxKind::LEX_ERROR, // unterminated
                // A newline ends an unterminated string, but an embedded term
                // may legitimately span lines.
                Some('\n') if depth == 0 => return SyntaxKind::LEX_ERROR,
                Some('"') if depth == 0 => {
                    self.bump();
                    return SyntaxKind::STRING;
                }
                Some('"') => {
                    // A string inside an embedded term.
                    self.bump();
                    loop {
                        match self.peek() {
                            None => return SyntaxKind::LEX_ERROR,
                            Some('\\') => {
                                self.bump();
                                self.bump();
                            }
                            Some('"') => {
                                self.bump();
                                break;
                            }
                            Some(_) => {
                                self.bump();
                            }
                        }
                    }
                }
                Some('{') if interpolated => {
                    depth += 1;
                    self.bump();
                }
                Some('}') if interpolated && depth > 0 => {
                    depth -= 1;
                    self.bump();
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

    /// True if this string directly follows an identifier ending in `!`, which
    /// is how Lean marks interpolation.
    fn after_interpolation_prefix(&self) -> bool {
        self.out
            .iter()
            .rev()
            .find(|t| !t.kind.is_trivia())
            .is_some_and(|t| {
                t.kind == SyntaxKind::IDENT && t.text.ends_with('!') && t.end() as usize == self.pos
            })
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
        // A number that directly follows a `.` is a projection index, so it
        // takes no fractional part of its own: `x.2.2` is two projections, not
        // a projection by the float `2.2`.
        let after_dot = self
            .out
            .iter()
            .rev()
            .find(|t| !t.kind.is_trivia())
            .is_some_and(|t| t.kind == SyntaxKind::DOT);
        // A `.` only continues the literal if a digit follows; `1.foo` is a
        // projection and `1..2` is a range.
        if !after_dot
            && self.peek() == Some('.')
            && self.peek_nth(1).is_some_and(|c| c.is_ascii_digit())
        {
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
        // `ℕ+` and friends are single tokens in Lean's token table.
        let so_far = &self.src[start..self.pos];
        if so_far.chars().count() == 1 && !so_far.is_ascii() {
            for suffix in TYPE_SUFFIXES {
                if self.starts_with(suffix) {
                    for _ in 0..suffix.chars().count() {
                        self.bump();
                    }
                    break;
                }
            }
        }
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

    /// Longest-match punctuation, then the generic notation fallbacks, then a
    /// one-character error token.
    fn symbol(&mut self) -> SyntaxKind {
        for (text, kind) in SORTED_SYMBOLS.iter() {
            if self.starts_with(text) {
                for _ in 0..text.chars().count() {
                    self.bump();
                }
                // A suffix makes a different operator: `→ₗ[R]` is the
                // linear-map arrow, `→+` the additive-monoid hom, `⁻¹'` the
                // preimage. Restricted to non-ASCII base symbols so that `a +`
                // and `x *` are unaffected.
                // A modifier decorates any operator — `~ᵤ` is `Associated`,
                // `=ᵐ` almost-everywhere equality. The ASCII suffixes `+ * '`
                // decorate only a non-ASCII base, so `a + b` and `x * y` are
                // untouched.
                // `∃!` is unique existence and `λ_` a monoidal unitor; both are
                // single tokens, and `λ` cannot start an identifier since it
                // opens a lambda.
                let decorates = |c: char| {
                    is_modifier(c)
                        || (!text.is_ascii() && matches!(c, '+' | '*' | '\'' | '!' | '_' | '>'))
                };
                if !kind.is_delimiter() && self.peek().is_some_and(decorates) {
                    self.bump_while(decorates);
                    return SyntaxKind::SYMBOL;
                }
                return *kind;
            }
        }

        let c = self.peek().expect("caller checked for input");
        if is_modifier(c) {
            // A modifier run that begins a token is postfix notation applied to
            // whatever preceded it.
            self.bump_while(is_modifier);
            return SyntaxKind::MODIFIER;
        }
        if is_notation_char(c) {
            self.bump();
            self.bump_while(is_modifier);
            return SyntaxKind::SYMBOL;
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
    fn a_number_after_a_dot_is_a_projection_index() {
        // `x.2.2` reaches a nested field; reading `2.2` as a float broke it.
        assert_eq!(dump("x.2.2"), "IDENT(x) DOT(.) NUMBER(2) DOT(.) NUMBER(2)");
        // Floats elsewhere are unaffected.
        assert_eq!(dump("1.5"), "SCIENTIFIC(1.5)");
        assert_eq!(dump("f 1.5"), "IDENT(f) WHITESPACE( ) SCIENTIFIC(1.5)");
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
    fn an_interpolated_string_may_embed_a_string() {
        // The embedded term is lexed as part of the literal, so a string inside
        // it must not terminate the outer one.
        assert_eq!(
            dump(r#"s!"a {", ".intercalate xs} b""#),
            r#"IDENT(s!) STRING("a {", ".intercalate xs} b")"#
        );
        // A brace in an ordinary string is just a brace.
        assert_eq!(dump(r#""{""#), r#"STRING("{")"#);
        // And interpolation needs the `!` to be adjacent.
        assert_eq!(
            dump(r#"s !"{""#),
            r#"IDENT(s) WHITESPACE( ) BANG(!) STRING("{")"#
        );
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
    fn unknown_notation_lexes_as_a_symbol_rather_than_an_error() {
        // mathlib uses 292 characters this parser has no specific rule for.
        // They must reach the parser as notation, not as lexer errors.
        assert_eq!(dump("⊸"), "SYMBOL(⊸)");
        assert_eq!(dump("⨯"), "SYMBOL(⨯)");
        // mathlib reaches well outside Unicode's mathematical blocks: `⁅⁆` are
        // General Punctuation and `ᗮ` is Canadian Syllabics.
        assert_eq!(dump("ᗮ"), "SYMBOL(ᗮ)");
        // Since any character may be declared as notation, the lexer does not
        // guess that one is not. LEX_ERROR is for the genuinely malformed.
        assert_eq!(dump("\u{1f600}"), "SYMBOL(😀)");
        assert_eq!(dump("\u{0}"), "LEX_ERROR(\0)");
    }

    #[test]
    fn modifiers_attach_to_the_operator_they_follow() {
        // `→` and `→ₗ` are different arrows, so the modifier joins the token.
        assert_eq!(dump("→ₗ"), "SYMBOL(→ₗ)");
        assert_eq!(dump("→"), "ARROW(→)");
        // A modifier run that starts a token is postfix notation.
        assert_eq!(dump("ᶜ"), "MODIFIER(ᶜ)");
        assert_eq!(dump("ᵒᵖ"), "MODIFIER(ᵒᵖ)");
        assert_eq!(dump("sᶜ"), "IDENT(s) MODIFIER(ᶜ)");
        // Subscripts still belong to an identifier that precedes them.
        assert_eq!(dump("x₀"), "IDENT(x₀)");
        // `⁻¹` keeps its own kind, being a known symbol.
        assert_eq!(dump("⁻¹"), "INV(⁻¹)");
    }

    #[test]
    fn decorated_operators_are_single_tokens() {
        // Lean's bundled-morphism arrows are tokens in their own right.
        assert_eq!(dump("→+"), "SYMBOL(→+)");
        assert_eq!(dump("→+*"), "SYMBOL(→+*)");
        assert_eq!(dump("≃ₗ"), "SYMBOL(≃ₗ)");
        assert_eq!(dump("⁻¹'"), "SYMBOL(⁻¹')");
        // `''` is `Set.image`, not two character literals.
        assert_eq!(
            dump("f '' s"),
            "IDENT(f) WHITESPACE( ) IMAGE('') WHITESPACE( ) IDENT(s)"
        );
        // ASCII operators are left alone, so ordinary arithmetic is unaffected.
        assert_eq!(dump("a+b"), "IDENT(a) PLUS(+) IDENT(b)");
        assert_eq!(dump("a+ b"), "IDENT(a) PLUS(+) WHITESPACE( ) IDENT(b)");
    }

    #[test]
    fn decorated_type_names_are_single_tokens() {
        assert_eq!(dump("ℕ+"), "IDENT(ℕ+)");
        assert_eq!(dump("ℝ≥0"), "IDENT(ℝ≥0)");
        assert_eq!(dump("ℝ≥0∞"), "IDENT(ℝ≥0∞)");
        // Only a single non-ASCII letter takes a suffix.
        assert_eq!(dump("Nat+"), "IDENT(Nat) PLUS(+)");
    }

    #[test]
    fn curated_notation_keeps_specific_kinds() {
        assert_eq!(dump("‖"), "NORM_BAR(‖)");
        assert_eq!(dump("≫"), "GG(≫)");
        assert_eq!(dump("∑"), "BIG_SUM(∑)");
    }

    #[test]
    fn tactic_words_are_reserved_like_lean_reserves_them() {
        // Lean's token table is global, so these are not identifiers. Without
        // this, `induction xs using foo` reads `using` as an argument.
        assert_eq!(dump("only"), "KW_ONLY(only)");
        assert_eq!(dump("using"), "KW_USING(using)");
        assert_eq!(dump("generalizing"), "KW_GENERALIZING(generalizing)");
        // Only the whole word is reserved.
        assert_eq!(dump("only_if"), "IDENT(only_if)");
        assert_eq!(dump("Finset.sum_only"), "IDENT(Finset.sum_only)");
    }

    #[test]
    fn turnstile_marks_the_goal_in_a_location_clause() {
        assert_eq!(dump("⊢"), "TURNSTILE(⊢)");
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
