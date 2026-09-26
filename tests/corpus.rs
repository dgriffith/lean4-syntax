//! Regression tests over whole files, plus robustness properties.

use std::path::Path;

/// Parses every `.lean` file in `tests/data`, requiring a clean parse and an
/// exact round-trip.
#[test]
fn corpus_files_parse_without_errors() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    let mut checked = 0;
    for entry in std::fs::read_dir(&dir).expect("corpus directory exists") {
        let path = entry.expect("readable entry").path();
        if path.extension().is_none_or(|e| e != "lean") {
            continue;
        }
        let src = std::fs::read_to_string(&path).expect("readable file");
        let parse = lean4_syntax::parse(&src);
        assert_eq!(parse.text(), src, "{} did not round-trip", path.display());
        assert!(
            parse.ok(),
            "{} produced errors: {:#?}",
            path.display(),
            parse.errors()
        );
        checked += 1;
    }
    assert!(checked > 0, "no corpus files found in {}", dir.display());
}

/// Truncating a file at any point must not panic, and must still round-trip.
///
/// This is the shape of input an editor produces on every keystroke, and it is
/// where a parser that assumes well-formed input tends to fall over.
#[test]
fn every_prefix_of_every_corpus_file_is_survivable() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    for entry in std::fs::read_dir(&dir).expect("corpus directory exists") {
        let path = entry.expect("readable entry").path();
        if path.extension().is_none_or(|e| e != "lean") {
            continue;
        }
        let src = std::fs::read_to_string(&path).expect("readable file");
        for end in 0..=src.len() {
            if !src.is_char_boundary(end) {
                continue;
            }
            let prefix = &src[..end];
            let parse = lean4_syntax::parse(prefix);
            assert_eq!(
                parse.text(),
                prefix,
                "prefix of length {end} of {} did not round-trip",
                path.display()
            );
        }
    }
}

/// Deleting any single line must not panic either — a rough stand-in for the
/// broken intermediate states real editing passes through.
#[test]
fn removing_any_line_is_survivable() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    for entry in std::fs::read_dir(&dir).expect("corpus directory exists") {
        let path = entry.expect("readable entry").path();
        if path.extension().is_none_or(|e| e != "lean") {
            continue;
        }
        let src = std::fs::read_to_string(&path).expect("readable file");
        let lines: Vec<&str> = src.lines().collect();
        for skip in 0..lines.len() {
            let mutated: String = lines
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != skip)
                .map(|(_, l)| format!("{l}\n"))
                .collect();
            let parse = lean4_syntax::parse(&mutated);
            assert_eq!(parse.text(), mutated, "line {skip} removal lost text");
        }
    }
}

/// Arbitrary token soup must round-trip. Tokens are drawn from Lean's own
/// vocabulary so the parser is exercised rather than just the lexer.
#[test]
fn token_soup_round_trips() {
    const PIECES: &[&str] = &[
        "def", "theorem", ":=", ":", "(", ")", "{", "}", "[", "]", "⟨", "⟩", "fun", "=>", "→",
        "match", "with", "|", "by", "simp", "do", "let", "←", "\n", "  ", "x", "Nat", "1", "\"s\"",
        "@[", "end", "where", "·", "<;>", "calc", "∀", ",", ";", "_", ".",
    ];
    // A deterministic xorshift keeps the test reproducible.
    let mut state = 0x2545F491_4F6CDD1Du64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    for _ in 0..400 {
        let len = (next() % 60) as usize;
        let src: String = (0..len)
            .map(|_| PIECES[(next() % PIECES.len() as u64) as usize])
            .collect::<Vec<_>>()
            .join(" ");
        let parse = lean4_syntax::parse(&src);
        assert_eq!(parse.text(), src, "token soup lost text: {src:?}");
    }
}
