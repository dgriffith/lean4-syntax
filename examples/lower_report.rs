//! Reports how much of a corpus the HIR lowering actually interprets.
//!
//! `Opaque` is lowering's only escape hatch, so counting opaque nodes — grouped
//! by the CST kind each one wraps — says exactly what is left to model. A
//! `LoweringError` is different and worse: it means the shape *was* recognised
//! and still could not be lowered.

use lean4_syntax::hir;
use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (flags, roots): (Vec<_>, Vec<_>) = args.iter().partition(|a| a.starts_with("--"));
    if roots.is_empty() {
        eprintln!("usage: lower_report [--top=N] <dir-or-file>...");
        std::process::exit(2);
    }
    let top = flags
        .iter()
        .find_map(|f| f.strip_prefix("--top="))
        .and_then(|v| v.parse().ok())
        .unwrap_or(20usize);

    let mut files = Vec::new();
    for root in &roots {
        collect(Path::new(root), &mut files);
    }
    files.sort();

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let mut panicked: Vec<PathBuf> = Vec::new();
    let mut nodes = 0usize;
    let mut opaque = 0usize;
    let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();
    let mut errors: BTreeMap<String, usize> = BTreeMap::new();
    let mut error_examples: BTreeMap<String, (PathBuf, String)> = BTreeMap::new();
    let mut items = 0usize;
    let mut links = 0usize;

    let start = Instant::now();
    for path in &files {
        let Ok(src) = std::fs::read_to_string(path) else {
            continue;
        };
        let result = catch_unwind(AssertUnwindSafe(|| {
            let parse = lean4_syntax::parse(&src);
            let module = hir::lower(&parse.syntax());
            let root = parse.syntax();

            let mut local_opaque: Vec<String> = Vec::new();
            for (_, term) in module.terms() {
                if let hir::Term::Opaque(ptr) = term {
                    local_opaque.push(format!("{:?}", ptr.kind()));
                    let _ = ptr.try_to_node(&root);
                }
            }
            for (_, tactic) in module.tactics() {
                if let hir::Tactic::Opaque { node, .. } = tactic {
                    local_opaque.push(format!("{:?}", node.kind()));
                }
            }
            for (_, pat) in module.pats() {
                if let hir::Pat::Opaque(ptr) = pat {
                    local_opaque.push(format!("{:?}", ptr.kind()));
                }
            }
            let total = module.terms().count()
                + module.tactics().count()
                + module.pats().count()
                + module.binders().count();
            let errs: Vec<String> = module
                .errors
                .iter()
                .map(|e| format!("{} [{:?}]", e.message, e.node.kind()))
                .collect();
            (
                total,
                local_opaque,
                errs,
                module.items().count(),
                module.source.len(),
            )
        }));

        match result {
            Err(_) => panicked.push(path.clone()),
            Ok((total, local_opaque, errs, item_count, link_count)) => {
                nodes += total;
                opaque += local_opaque.len();
                items += item_count;
                links += link_count;
                for kind in local_opaque {
                    *by_kind.entry(kind).or_default() += 1;
                }
                for err in errs {
                    *errors.entry(err.clone()).or_default() += 1;
                    error_examples
                        .entry(err)
                        .or_insert_with(|| (path.clone(), String::new()));
                }
            }
        }
    }
    let elapsed = start.elapsed();
    std::panic::set_hook(previous);

    println!(
        "lowered {} files in {:.1?}\n",
        files.len() - panicked.len(),
        elapsed
    );
    println!("  {items:>8} items");
    println!("  {nodes:>8} HIR nodes");
    println!("  {links:>8} source links");
    println!(
        "  {opaque:>8} opaque ({:.1}% of nodes)  <- the coverage metric",
        100.0 * opaque as f64 / nodes.max(1) as f64
    );
    println!(
        "  {:>8} panicked  <- defect, lowering must be total",
        panicked.len()
    );
    for path in panicked.iter().take(10) {
        println!("    panic: {}", path.display());
    }

    if !by_kind.is_empty() {
        let mut ranked: Vec<_> = by_kind.iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        println!("\nopaque nodes by the syntax they wrap:");
        for (kind, n) in ranked.iter().take(top) {
            println!("  {n:>8}  {kind}");
        }
    }

    let error_total: usize = errors.values().sum();
    if error_total > 0 {
        let mut ranked: Vec<_> = errors.iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        println!("\n{error_total} lowering errors — recognised but not lowered:");
        for (msg, n) in ranked.iter().take(top) {
            println!("  {n:>8}  {msg}");
            if let Some((file, _)) = error_examples.get(*msg) {
                println!("            {}", file.display());
            }
        }
    }
}

fn collect(path: &Path, out: &mut Vec<PathBuf>) {
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
        let name = child.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if name.starts_with('.') || name == ".lake" {
            continue;
        }
        collect(&child, out);
    }
}
