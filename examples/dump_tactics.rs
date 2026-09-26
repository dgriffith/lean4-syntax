//! Reports which tactic shapes a file's tactics were parsed into.
//!
//! A high `TACTIC` (generic fallback) count relative to the structured shapes
//! means the grammar is not recognising as much as it appears to.

use lean4_syntax::SyntaxKind::*;
use std::collections::BTreeMap;

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: dump_tactics <file.lean>");
    let src = std::fs::read_to_string(&path).expect("readable file");
    let parse = lean4_syntax::parse(&src);

    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut generic_names: Vec<String> = Vec::new();

    for node in parse.syntax().descendants() {
        let kind = node.kind();
        if !matches!(
            kind,
            TACTIC
                | TACTIC_SIMP
                | TACTIC_REWRITE
                | TACTIC_TERM
                | TACTIC_TERM_LIST
                | TACTIC_INTRO
                | TACTIC_CASES
                | TACTIC_HAVE
                | TACTIC_CASE
                | TACTIC_CONV
                | TACTIC_SHOW
                | TACTIC_CALC
                | TACTIC_COMBINATOR_APP
                | TACTIC_FOCUS
                | TACTIC_ALT
                | TACTIC_SEQ_BRACKETED
                | TACTIC_COMBINATOR
        ) {
            continue;
        }
        *counts.entry(format!("{kind:?}")).or_default() += 1;
        if kind == TACTIC
            && let Some(first) = node
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find(|t| !t.kind().is_trivia())
        {
            generic_names.push(first.text().to_string());
        }
    }

    let total: usize = counts.values().sum();
    for (kind, n) in &counts {
        println!("{n:>4}  {kind}");
    }
    println!("{total:>4}  TOTAL");
    if !generic_names.is_empty() {
        generic_names.sort();
        generic_names.dedup();
        println!("\nfell back to generic: {}", generic_names.join(", "));
    }
    println!("errors: {}", parse.errors().len());
}
