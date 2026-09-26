//! A lossless parser and syntax tree for Lean 4 source files.
//!
//! # What you get
//!
//! [`parse`] turns source text into a tree that reproduces the input exactly —
//! whitespace, comments and all — and that survives syntax errors by wrapping
//! unparsable regions in `ERROR` nodes:
//!
//! ```
//! use lean4_syntax::ast::{AstNode, HasDecl, SourceFile};
//!
//! let parse = lean4_syntax::parse("/-- Doubles. -/\ndef double (n : Nat) : Nat := n + n\n");
//! assert!(parse.errors().is_empty());
//!
//! let file = SourceFile::cast(parse.syntax()).unwrap();
//! let def = file.declarations().next().unwrap();
//! assert_eq!(def.name().unwrap().text(), "double");
//! ```
//!
//! # Structure
//!
//! Source text flows through four stages:
//!
//! | Stage | Module | Produces |
//! |---|---|---|
//! | Tokenize | [`lexer`] | every token, trivia included |
//! | Parse | [`parser`] | a tree of [`syntax::Frag`]s referencing tokens by index |
//! | Materialize | [`syntax`] | a rowan green tree, trivia re-interleaved |
//! | View | [`ast`] | typed wrappers over the untyped tree |
//!
//! Splitting parsing from tree construction is what makes losslessness
//! structural rather than a matter of discipline: the parser works on
//! significant tokens only and never has to thread trivia through its rules,
//! while [`syntax::materialize`] emits every raw token exactly once, in order.
//! It also lets the parser backtrack freely, since an abandoned branch is just
//! a dropped fragment.
//!
//! # Scope
//!
//! Lean 4's grammar is user-extensible: `notation`, `infixl` and `macro_rules`
//! add syntax as a file is elaborated, so no parser outside Lean itself can
//! claim full coverage. This one parses the core language — commands,
//! declarations, the term grammar with Lean's built-in precedences, and the
//! structure of `do` and tactic blocks — and *records* grammar-extending
//! commands without applying them. See the README for the specific
//! consequences.

pub mod ast;
pub mod kind;
pub mod lexer;
pub mod parser;
pub mod syntax;

pub use kind::{Lean, SyntaxKind, SyntaxNode, SyntaxToken};
pub use parser::parse;
pub use syntax::{Parse, ParseError};
