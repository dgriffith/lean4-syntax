//! CLI for inspecting the Lean 4 parser's output.

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (flags, paths): (Vec<_>, Vec<_>) = args.iter().partition(|a| a.starts_with("--"));
    if paths.is_empty() {
        eprintln!("usage: lean4 [--quiet] <file.lean>...");
        return ExitCode::FAILURE;
    }
    let quiet = flags.iter().any(|f| *f == "--quiet");

    let mut failed = false;
    for path in paths {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("{path}: {e}");
                failed = true;
                continue;
            }
        };
        let parse = lean4_syntax::parse(&src);
        if parse.text() != src {
            eprintln!("{path}: BUG - tree does not round-trip");
            failed = true;
        }
        if !quiet {
            print!("{}", lean4_syntax::syntax::debug_tree(&parse.syntax()));
        }
        for err in parse.errors() {
            let offset = u32::from(err.range.start()) as usize;
            let line = src[..offset.min(src.len())].lines().count().max(1);
            eprintln!("{path}:{line}: {}", err.message);
            failed = true;
        }
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
