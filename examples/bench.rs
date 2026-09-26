//! Rough scaling check: parse the corpus repeated N times and report throughput.

fn main() {
    let base = std::fs::read_to_string("tests/data/declarations.lean").unwrap();
    for reps in [10usize, 20, 40, 80, 160] {
        let src = base.repeat(reps);
        let start = std::time::Instant::now();
        let parse = lean4_syntax::parse(&src);
        let elapsed = start.elapsed();
        assert!(parse.ok());
        println!(
            "{:>8} bytes  {:>8.1?}  {:>7.2} MB/s",
            src.len(),
            elapsed,
            src.len() as f64 / elapsed.as_secs_f64() / 1_000_000.0
        );
    }
}
