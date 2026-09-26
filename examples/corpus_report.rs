//! Parses a corpus of Lean files and reports what the parser cannot handle.
//!
//! Three outcomes are reported separately, because they mean different things:
//!
//! * **Panic** — a defect. The parser must never panic on any input.
//! * **Round-trip failure** — a defect. Losslessness is unconditional, so a
//!   tree whose text differs from its source is always a bug.
//! * **Parse errors** — coverage gaps. Expected, and the point of the exercise.
//!
//! Commands that matched only the generic fallback are counted separately
//! again: they parse without error, so they would otherwise make a file look
//! clean while its structure went unrecognised.
//!
//! Read that list with one caveat. The fallback needs only a leading
//! identifier, so a fragment left by an earlier failure can be absorbed as a
//! "command" — seeing `rw`, `simp` or a bare type name in the ranking means a
//! cascade, not a command mathlib actually defines. Names like `alias`,
//! `run_cmd` and `termination_by` are the real entries.
//!
//! Two further breakdowns separate causes from symptoms. Recovery resumes at
//! the next top-level token, so one unsupported construct leaves a trail of
//! fragments behind it; ranking only the *first* failure in each file
//! approximates root causes instead. And unknown characters are censused
//! directly, since a token the lexer cannot classify is a cause by definition
//! and never a consequence of one.
//!
//! Gaps are grouped by *signature* rather than listed per file, so a hundred
//! instances of one unsupported construct read as one line instead of burying
//! the long tail. A signature pairs the enclosing node with the first token of
//! the failing region, including that token's text only when it comes from a
//! bounded vocabulary — keywords and symbols, never identifiers, which would
//! make every lemma name its own group.
//!
//! ```text
//! cargo run --release --example corpus_report -- path/to/mathlib4
//! ```

use lean4_syntax::{SyntaxKind, SyntaxNode};
use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// How a single file fared.
enum Outcome {
    Panicked,
    NotLossless,
    /// Each unparsable region, with the offset and excerpt used for examples,
    /// plus the names of commands that matched only the generic fallback.
    Parsed {
        errors: Vec<(Signature, usize, String)>,
        unknown_commands: Vec<String>,
        /// Text of every token the lexer could not classify.
        unknown_chars: Vec<String>,
    },
}

/// A groupable description of one unparsable region.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Signature {
    /// The node containing the failure.
    parent: String,
    /// The first token of the failing region.
    token: String,
}

impl std::fmt::Display for Signature {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} :: {}", self.parent, self.token)
    }
}

/// One instance of a signature, for showing a concrete example.
struct Example {
    file: PathBuf,
    line: usize,
    snippet: String,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (flags, roots): (Vec<_>, Vec<_>) = args.iter().partition(|a| a.starts_with("--"));
    if roots.is_empty() {
        eprintln!("usage: corpus_report [--top N] [--limit N] <dir-or-file>...");
        std::process::exit(2);
    }
    let value_of = |name: &str, default: usize| -> usize {
        flags
            .iter()
            .find_map(|f| f.strip_prefix(&format!("--{name}=")))
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    };
    let top = value_of("top", 25);
    let limit = value_of("limit", usize::MAX);

    let mut files = Vec::new();
    for root in &roots {
        collect_lean_files(Path::new(root), &mut files);
    }
    files.sort();
    files.truncate(limit);
    if files.is_empty() {
        eprintln!("no .lean files found");
        std::process::exit(2);
    }

    // The parser is not expected to panic; if it does, report it rather than
    // letting one file abort the whole run. Suppress the default hook so a
    // panic does not drown the report.
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let mut bytes = 0usize;
    let mut clean = 0usize;
    let mut with_errors = 0usize;
    let mut not_lossless: Vec<PathBuf> = Vec::new();
    let mut panicked: Vec<PathBuf> = Vec::new();
    let mut counts: BTreeMap<Signature, usize> = BTreeMap::new();
    let mut examples: BTreeMap<Signature, Example> = BTreeMap::new();
    let mut per_file: Vec<(usize, PathBuf)> = Vec::new();
    let mut unknown_cmds: BTreeMap<String, usize> = BTreeMap::new();
    let mut unknown_chars: BTreeMap<String, usize> = BTreeMap::new();
    let mut files_with_unknown_chars = 0usize;
    let mut first_errors: BTreeMap<Signature, usize> = BTreeMap::new();
    let mut first_examples: BTreeMap<Signature, Example> = BTreeMap::new();

    let start = Instant::now();
    for path in &files {
        let Ok(src) = std::fs::read_to_string(path) else {
            continue;
        };
        bytes += src.len();

        match examine(&src) {
            Outcome::Panicked => panicked.push(path.clone()),
            Outcome::NotLossless => not_lossless.push(path.clone()),
            Outcome::Parsed {
                errors,
                unknown_commands,
                unknown_chars: chars,
            } => {
                for name in unknown_commands {
                    *unknown_cmds.entry(name).or_default() += 1;
                }
                if !chars.is_empty() {
                    files_with_unknown_chars += 1;
                }
                for c in chars {
                    *unknown_chars.entry(c).or_default() += 1;
                }
                if errors.is_empty() {
                    clean += 1;
                    continue;
                }
                with_errors += 1;
                per_file.push((errors.len(), path.clone()));
                let lines = LineIndex::new(&src);
                // The first failure in a file is the likely cause; the rest are
                // usually fragments left by recovery.
                if let Some((sig, offset, snippet)) = errors.first() {
                    *first_errors.entry(sig.clone()).or_default() += 1;
                    first_examples
                        .entry(sig.clone())
                        .or_insert_with(|| Example {
                            file: path.clone(),
                            line: lines.line_of(*offset),
                            snippet: snippet.clone(),
                        });
                }
                for (sig, offset, snippet) in errors {
                    *counts.entry(sig.clone()).or_default() += 1;
                    examples.entry(sig).or_insert_with(|| Example {
                        file: path.clone(),
                        line: lines.line_of(offset),
                        snippet,
                    });
                }
            }
        }
    }
    let elapsed = start.elapsed();
    std::panic::set_hook(previous_hook);

    // ---- Report ------------------------------------------------------------

    let total = files.len();
    let mb = bytes as f64 / 1_000_000.0;
    println!(
        "scanned {total} files, {mb:.1} MB in {:.1?} ({:.2} MB/s)\n",
        elapsed,
        mb / elapsed.as_secs_f64()
    );
    let pct = |n: usize| 100.0 * n as f64 / total as f64;
    println!("  {clean:>6} clean                ({:.1}%)", pct(clean));
    println!(
        "  {with_errors:>6} with parse errors    ({:.1}%)",
        pct(with_errors)
    );
    println!(
        "  {files_with_unknown_chars:>6} contain unknown chars ({:.1}%)  <- ceiling on the clean rate",
        pct(files_with_unknown_chars)
    );
    println!("  {:>6} failed round-trip    <- defect", not_lossless.len());
    println!("  {:>6} panicked             <- defect", panicked.len());

    for (label, list) in [("round-trip", &not_lossless), ("panic", &panicked)] {
        for path in list.iter().take(20) {
            println!("    {label}: {}", path.display());
        }
    }

    let error_total: usize = counts.values().sum();
    println!(
        "\n{error_total} unparsable regions, {} distinct signatures\n",
        counts.len()
    );

    if !unknown_chars.is_empty() {
        let total_chars: usize = unknown_chars.values().sum();
        let mut ranked_chars: Vec<_> = unknown_chars.iter().collect();
        ranked_chars.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        println!(
            "{total_chars} unclassifiable tokens, {} distinct — every one is a cause, not a symptom:",
            unknown_chars.len()
        );
        for (text, n) in ranked_chars.iter().take(30) {
            let codepoints: Vec<String> = text
                .chars()
                .map(|c| format!("U+{:04X}", c as u32))
                .collect();
            println!("  {n:>6}  {text}   {}", codepoints.join(" "));
        }
        println!();
    }

    let mut ranked_first: Vec<_> = first_errors.iter().collect();
    ranked_first.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    println!("first failure per file, which approximates root cause:");
    for (sig, n) in ranked_first.iter().take(top) {
        println!("\n  {n:>6}  {sig}");
        if let Some(ex) = first_examples.get(*sig) {
            println!("          {}:{}", ex.file.display(), ex.line);
            println!("          {}", ex.snippet);
        }
    }
    println!();

    let mut ranked: Vec<_> = counts.iter().collect();
    ranked.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));

    let covered: usize = ranked.iter().take(top).map(|(_, n)| **n).sum();
    println!(
        "top {} signatures account for {covered} of {error_total} regions ({:.0}%):",
        top.min(ranked.len()),
        100.0 * covered as f64 / error_total.max(1) as f64
    );
    for (sig, n) in ranked.iter().take(top) {
        println!("\n  {n:>6}  {sig}");
        if let Some(ex) = examples.get(*sig) {
            println!("          {}:{}", ex.file.display(), ex.line);
            println!("          {}", ex.snippet);
        }
    }

    if !unknown_cmds.is_empty() {
        let total_unknown: usize = unknown_cmds.values().sum();
        let mut ranked_cmds: Vec<_> = unknown_cmds.iter().collect();
        ranked_cmds.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        println!(
            "\n{total_unknown} commands matched only the generic fallback, {} distinct names:",
            unknown_cmds.len()
        );
        for (name, n) in ranked_cmds.iter().take(15) {
            println!("  {n:>6}  {name}");
        }
    }

    per_file.sort_by_key(|a| std::cmp::Reverse(a.0));
    if !per_file.is_empty() {
        println!("\nfiles with the most unparsable regions:");
        for (n, path) in per_file.iter().take(10) {
            println!("  {n:>6}  {}", path.display());
        }
    }
}

/// Parses one file, catching panics and checking losslessness.
fn examine(src: &str) -> Outcome {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let parse = lean4_syntax::parse(src);
        let lossless = parse.text() == src;
        let unknown_commands: Vec<String> = parse
            .syntax()
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::UNKNOWN_CMD)
            .filter_map(|n| {
                n.children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .find(|t| !t.kind().is_trivia())
                    .map(|t| t.text().to_string())
            })
            .collect();
        let unknown_chars: Vec<String> = parse
            .syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == SyntaxKind::LEX_ERROR)
            .map(|t| t.text().to_string())
            .collect();
        let errors: Vec<(Signature, usize, String)> = error_nodes(&parse.syntax())
            .map(|n| {
                let offset = u32::from(n.text_range().start()) as usize;
                (signature(&n), offset, snippet(&n))
            })
            .collect();
        (lossless, errors, unknown_commands, unknown_chars)
    }));
    match result {
        Err(_) => Outcome::Panicked,
        Ok((false, ..)) => Outcome::NotLossless,
        Ok((true, errors, unknown_commands, unknown_chars)) => Outcome::Parsed {
            errors,
            unknown_commands,
            unknown_chars,
        },
    }
}

/// Every `ERROR` node in the tree.
fn error_nodes(root: &SyntaxNode) -> impl Iterator<Item = SyntaxNode> + use<> {
    root.descendants()
        .filter(|n| n.kind() == SyntaxKind::ERROR)
        .collect::<Vec<_>>()
        .into_iter()
}

/// Describes an unparsable region in a way that groups with its peers.
fn signature(node: &SyntaxNode) -> Signature {
    let parent = node
        .parent()
        .map(|p| format!("{:?}", p.kind()))
        .unwrap_or_else(|| "<root>".to_string());

    let first = node
        .descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| !t.kind().is_trivia());

    // Keywords and symbols come from a bounded vocabulary, so their text is a
    // useful discriminator. Identifier text is not: it would split one gap into
    // a thousand groups, one per lemma name.
    let token = match first {
        Some(t) if t.kind().is_keyword() || t.kind().is_symbol() => {
            format!("{:?} {:?}", t.kind(), t.text())
        }
        Some(t) => format!("{:?}", t.kind()),
        None => "<empty>".to_string(),
    };

    Signature { parent, token }
}

/// A one-line, length-capped excerpt of the failing region.
fn snippet(node: &SyntaxNode) -> String {
    let text = node.text().to_string();
    let collapsed = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut out: String = collapsed.chars().take(72).collect();
    if collapsed.chars().count() > 72 {
        out.push('…');
    }
    out
}

/// Maps byte offsets to 1-based line numbers.
struct LineIndex {
    starts: Vec<usize>,
}

impl LineIndex {
    fn new(src: &str) -> LineIndex {
        let mut starts = vec![0];
        starts.extend(
            src.char_indices()
                .filter(|(_, c)| *c == '\n')
                .map(|(i, _)| i + 1),
        );
        LineIndex { starts }
    }

    fn line_of(&self, offset: usize) -> usize {
        self.starts.partition_point(|&s| s <= offset)
    }
}

/// Recursively collects `.lean` files.
fn collect_lean_files(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_file() {
        if path.extension().is_some_and(|e| e == "lean") {
            out.push(path.to_path_buf());
        }
        return;
    }
    let Ok(entries) = std::fs::read_dir(path) else {
        return;
    };
    for entry in entries.flatten() {
        let child = entry.path();
        // Skip build output and version control.
        let name = child.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if name.starts_with('.') || name == "lake-packages" || name == ".lake" {
            continue;
        }
        collect_lean_files(&child, out);
    }
}
