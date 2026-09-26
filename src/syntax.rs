//! Turning parser output into a lossless rowan tree.
//!
//! The parser never touches rowan directly. It produces [`Frag`]s, which
//! reference *significant* tokens by index, and this module interleaves the
//! trivia back in. Doing it in a second pass has two payoffs: the parser can
//! backtrack freely (a discarded branch is just a dropped `Frag`), and
//! losslessness is guaranteed structurally, because [`materialize`] emits every
//! raw token exactly once, in order.

use crate::kind::{SyntaxKind, SyntaxNode};
use crate::lexer::RawToken;
use rowan::{GreenNode, GreenNodeBuilder, TextRange, TextSize};

/// A token the parser actually looks at: trivia removed, with a back-reference
/// to its position in the raw token list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SigToken<'a> {
    /// The token kind.
    pub kind: SyntaxKind,
    /// The token's source text.
    pub text: &'a str,
    /// Index into the raw token list this came from.
    pub raw: usize,
    /// 1-based line.
    pub line: u32,
    /// 0-based column, in code points.
    pub col: u32,
    /// Byte offset in the source.
    pub offset: u32,
}

impl std::fmt::Display for SigToken<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "`{}`", self.text)
    }
}

/// Drops trivia from a raw token list, keeping indices back into it.
pub fn significant<'a>(raws: &[RawToken<'a>]) -> Vec<SigToken<'a>> {
    raws.iter()
        .enumerate()
        .filter(|(_, t)| !t.kind.is_trivia())
        .map(|(raw, t)| SigToken {
            kind: t.kind,
            text: t.text,
            raw,
            line: t.line,
            col: t.col,
            offset: t.offset,
        })
        .collect()
}

/// An unfinished piece of tree: either a significant token (by index) or an
/// interior node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Frag {
    /// A leaf, identified by its index into the significant-token list.
    Token(usize),
    /// An interior node and its children.
    Node(SyntaxKind, Vec<Frag>),
}

impl Frag {
    /// A node wrapping `children`.
    pub fn node(kind: SyntaxKind, children: Vec<Frag>) -> Frag {
        Frag::Node(kind, children)
    }

    /// The index of this fragment's leftmost token, if it has one.
    ///
    /// Used to flush pending trivia *before* opening a node, so node ranges
    /// start at real syntax instead of at the preceding blank line.
    fn first_token(&self) -> Option<usize> {
        match self {
            Frag::Token(i) => Some(*i),
            Frag::Node(_, kids) => kids.iter().find_map(Frag::first_token),
        }
    }
}

/// A parse error, in source coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// Human-readable description.
    pub message: String,
    /// Byte range in the source text.
    pub range: TextRange,
}

/// The result of parsing a file: a tree plus whatever went wrong.
#[derive(Debug, Clone)]
pub struct Parse {
    green: GreenNode,
    errors: Vec<ParseError>,
}

impl Parse {
    /// Builds a parse result.
    pub fn new(green: GreenNode, errors: Vec<ParseError>) -> Parse {
        Parse { green, errors }
    }

    /// The root node of the tree.
    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    /// The underlying green tree.
    pub fn green(&self) -> &GreenNode {
        &self.green
    }

    /// Errors encountered while parsing. A non-empty list still comes with a
    /// usable tree, with the unparsed regions wrapped in `ERROR` nodes.
    pub fn errors(&self) -> &[ParseError] {
        &self.errors
    }

    /// True if the file parsed cleanly.
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }

    /// The source text, reconstructed from the tree.
    pub fn text(&self) -> String {
        self.syntax().text().to_string()
    }
}

/// Builds the green tree, re-inserting trivia around the significant tokens
/// the parser consumed.
pub fn materialize(
    root: SyntaxKind,
    children: &[Frag],
    raws: &[RawToken<'_>],
    sigs: &[SigToken<'_>],
) -> GreenNode {
    let mut m = Materializer {
        builder: GreenNodeBuilder::new(),
        raws,
        sigs,
        next_raw: 0,
    };
    m.builder.start_node(root.into());
    for child in children {
        m.frag(child);
    }
    // Trailing trivia (and any tokens the parser never reached) belong to the
    // root, after everything else.
    m.flush_before(raws.len());
    m.builder.finish_node();
    m.builder.finish()
}

struct Materializer<'a, 'src> {
    builder: GreenNodeBuilder<'static>,
    raws: &'a [RawToken<'src>],
    sigs: &'a [SigToken<'src>],
    /// The first raw token not yet emitted.
    next_raw: usize,
}

impl Materializer<'_, '_> {
    /// Emits raw tokens up to, but not including, `raw_idx`.
    fn flush_before(&mut self, raw_idx: usize) {
        while self.next_raw < raw_idx {
            let t = self.raws[self.next_raw];
            self.builder.token(t.kind.into(), t.text);
            self.next_raw += 1;
        }
    }

    fn frag(&mut self, frag: &Frag) {
        match frag {
            Frag::Token(sig_idx) => {
                let raw_idx = self.sigs[*sig_idx].raw;
                self.flush_before(raw_idx);
                let t = self.raws[raw_idx];
                self.builder.token(t.kind.into(), t.text);
                self.next_raw = raw_idx + 1;
            }
            Frag::Node(kind, kids) => {
                // Put leading trivia outside the node so its range starts at
                // the node's own first token.
                if let Some(first) = frag.first_token() {
                    self.flush_before(self.sigs[first].raw);
                }
                self.builder.start_node((*kind).into());
                for kid in kids {
                    self.frag(kid);
                }
                self.builder.finish_node();
            }
        }
    }
}

/// Renders a tree as indented text, one line per node and token.
///
/// Token text is shown quoted; ranges are byte offsets.
pub fn debug_tree(node: &SyntaxNode) -> String {
    let mut out = String::new();
    write_tree(node, 0, &mut out);
    out
}

fn write_tree(node: &SyntaxNode, depth: usize, out: &mut String) {
    use std::fmt::Write;
    let _ = writeln!(
        out,
        "{:indent$}{:?}@{:?}..{:?}",
        "",
        node.kind(),
        u32::from(node.text_range().start()),
        u32::from(node.text_range().end()),
        indent = depth * 2
    );
    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Node(n) => write_tree(&n, depth + 1, out),
            rowan::NodeOrToken::Token(t) => {
                let _ = writeln!(
                    out,
                    "{:indent$}{:?}@{:?}..{:?} {:?}",
                    "",
                    t.kind(),
                    u32::from(t.text_range().start()),
                    u32::from(t.text_range().end()),
                    t.text(),
                    indent = (depth + 1) * 2
                );
            }
        }
    }
}

/// Renders a tree as a compact s-expression, omitting trivia.
///
/// Useful for asserting on tree *shape* — operator precedence, block
/// nesting — without the noise of whitespace tokens.
pub fn sexpr(node: &SyntaxNode) -> String {
    let mut out = String::new();
    write_sexpr(node, &mut out);
    out
}

fn write_sexpr(node: &SyntaxNode, out: &mut String) {
    use std::fmt::Write;
    let _ = write!(out, "({:?}", node.kind());
    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Node(n) => {
                out.push(' ');
                write_sexpr(&n, out);
            }
            rowan::NodeOrToken::Token(t) if !t.kind().is_trivia() => {
                let _ = write!(out, " {}", t.text());
            }
            rowan::NodeOrToken::Token(_) => {}
        }
    }
    out.push(')');
}

/// Converts a token-index range into a source byte range.
pub fn token_range_to_text_range(
    sigs: &[SigToken<'_>],
    raws: &[RawToken<'_>],
    start: usize,
    end: usize,
) -> TextRange {
    let start_off = sigs
        .get(start)
        .map(|t| t.offset)
        .unwrap_or_else(|| raws.last().map(RawToken::end).unwrap_or(0));
    let end_off = if end > start {
        sigs.get(end - 1)
            .map(|t| t.offset + t.text.len() as u32)
            .unwrap_or(start_off)
    } else {
        start_off
    };
    TextRange::new(
        TextSize::from(start_off),
        TextSize::from(end_off.max(start_off)),
    )
}
