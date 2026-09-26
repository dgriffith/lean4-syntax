# lean4-syntax

A lossless parser and syntax tree for Lean 4 source files, in Rust.

```rust
use lean4_syntax::ast::{AstNode, HasDecl, SourceFile};

let parse = lean4_syntax::parse(source);
let file = SourceFile::cast(parse.syntax()).unwrap();

for decl in file.declarations() {
    println!("{}", decl.name().unwrap().text());
}
```

## Design

Four stages, each in its own module:

```
source ──▶ lexer ──▶ parser ──▶ syntax ──▶ ast
           tokens    Frag tree   rowan CST  typed views
           (+trivia) (token idx) (+trivia)
```

**The tree is lossless.** Concatenating its tokens reproduces the input byte for
byte — whitespace, comments, and the contents of unparsable regions included.
This holds by construction rather than by care: the parser consumes only
*significant* tokens and records them by index, and a separate materialization
pass re-interleaves trivia, emitting every raw token exactly once in order. A
parser bug can therefore produce a badly *shaped* tree, but not a lossy one.

That separation also buys backtracking for free. The parser is built with
[chumsky] combinators, whose `choice` backtracks on failure; because rules
return values rather than mutating a tree builder, an abandoned branch is just a
dropped fragment.

**The tree is untyped, with typed views on top.** Nodes carry a `SyntaxKind` and
nothing else ([rowan], the same library rust-analyzer uses). The `ast` module
adds zero-cost wrappers — `Def`, `Theorem`, `Term`, `Binder` — whose accessors
all return `Option` or iterators, so a tree built from broken source stays
navigable.

**Errors never abort the parse.** A command that fails to parse becomes an
`ERROR` node holding its tokens, and parsing resumes at the next plausible
command start. Every other declaration in the file still parses.

### Indentation

Lean is layout-sensitive, and getting this wrong is the main way a Lean parser
goes subtly bad. The parser threads an indentation threshold through chumsky's
*context* parameter, giving a direct encoding of Lean's `colGt` / `colGe` rules.
Two consequences worth knowing:

- An application argument must be indented past the enclosing position, so a
  dedented line starts new syntax rather than being absorbed as an argument.
- A block ends when an item fails to parse, provided one item already
  succeeded. That is what lets a nested `by` block close at the right place:

  ```lean
  theorem t : p ∧ q := by
    have hp : p := by
      exact hp'      -- inner block
    exact ⟨hp, hq⟩   -- dedent: belongs to the outer block
  ```

## Scope

Lean 4's grammar is user-extensible — `notation`, `infixl`, `macro_rules` and
`syntax` add grammar as a file elaborates — so no parser outside Lean itself can
claim total coverage. This one covers the core language and **records**
grammar-extending commands without applying them.

Covered: all commands and declaration forms (`def`, `theorem`, `structure`,
`class`, `inductive`, `instance`, `mutual`, …) with modifiers, attributes,
docstrings, universe binders, `where` clauses and `deriving`; the full term
grammar with Lean's built-in precedence table; binders in all four
explicitness forms; `match`, `do`, `calc` and `by` blocks with correct layout;
and the tactic grammar described below.

Deliberately not interpreted:

| Construct | Treatment |
|---|---|
| `notation`, `infixl`, `prefix`, `postfix` | recorded as `NOTATION_CMD` / `MIXFIX_CMD`; the new syntax does **not** become available to the term parser |
| `syntax`, `macro`, `macro_rules`, `elab` | recorded; bodies kept as `RAW_TOKENS` |
| syntax quotations `` `(…) `` | contents kept as `RAW_TOKENS` |

### Tactics

Tactics are structured, which matters because they are what proof-rewriting
tools actually manipulate. `simp only [foo, ← bar] at h ⊢` yields the `only`
flag, three classified arguments, and a location that distinguishes hypotheses
from the goal — not a token run to be re-lexed.

There is deliberately **one node kind per shape, not per tactic name**. Lean's
tactic vocabulary is open-ended and grows with every library, so a kind per name
would be enormous and permanently incomplete. Instead a handful of shapes cover
the grammar, and the name token says which tactic it is:

| Shape | Covers |
|---|---|
| `TACTIC_SIMP` | `simp`, `simp_all`, `norm_num`, `linarith`, … — optional `only`, config, lemma list, location |
| `TACTIC_REWRITE` | `rw`, `rewrite`, `erw`, `simp_rw`, `nth_rw` — rule lists with `←`, location |
| `TACTIC_TERM` / `TACTIC_TERM_LIST` | `exact`, `apply`, `refine`, `specialize` / `use` |
| `TACTIC_INTRO` | `intro`, `rintro`, `ext`, `funext` — full pattern language |
| `TACTIC_CASES` | `cases`, `rcases`, `induction` — targets, `using`, `generalizing`, `with` |
| `TACTIC_HAVE` | `have`, `obtain`, `set`, `suffices`, `replace` |
| `TACTIC_CASE` / `TACTIC_CONV` / `TACTIC_SHOW` / `TACTIC_CALC` | goal naming, conversion mode, restatement, calculation |
| `TACTIC_COMBINATOR_APP` | `try`, `repeat`, `all_goals`, `iterate n` |
| `TACTIC_FOCUS`, `TACTIC_ALT`, `TACTIC_COMBINATOR`, `TACTIC_SEQ_BRACKETED` | `·`, `first \| …`, `<;>`, `(…)` |
| `TACTIC` | everything else — name plus a balanced `TACTIC_ARGS` run |

That last row is load-bearing rather than a gap. A tactic taking no arguments
needs no shape (`rfl`, `trivial`), and an unfamiliar or user-defined tactic still
parses with its arguments retained. Every structured shape also carries an
optional trailing `TACTIC_ARGS`, so syntax a shape does not model stays attached
to the tactic it belongs to instead of being mistaken for the next one — and a
non-empty one is a visible signal of an unmodelled form.

`rcases`/`rintro`/`obtain` patterns get their own small grammar
(`RCASES_PAT`, `RCASES_TUPLE`, `RCASES_ALT`), covering tuples, alternations,
`-` to clear a hypothesis and `@` to expose implicit arguments.

### Known limitations

- **Precedences are Lean's built-in table.** A file that declares its own
  operators parses them as application or fails locally; it will not honour the
  declared precedence.
- **Big terms are not bare application arguments.** Lean restricts arguments to
  maximal precedence, and this parser follows it, with a trailing lambda as the
  one exception (`xs.map fun x => x + 1` works). So `f do …` needs
  `f <| do …` — which is what keeps `for x in xs do …` parsing correctly.
- **`a != b` needs spaces.** `!` and `?` are identifier characters in Lean, so
  `a!=b` lexes as `a!`, `=`, `b`. This matches Lean.
- **`only`, `using` and `generalizing` are reserved.** Lean keeps one *global*
  token table, so words introduced by tactic syntax are tokens everywhere rather
  than identifiers that happen to appear in tactic position. Reserving them is
  what stops `induction xs using List.rec` from reading `using` as an argument
  of `xs`. A file using one of them as an identifier will not parse — but nor
  would it in Lean.
- Uncommon brace terms beyond `{x := e}`, `{s with …}`, `{x // p}`, `{x | p}`
  and `{a, b}` are not modeled.

## Usage

```
cargo run -- file.lean            # dump the tree
cargo run -- --quiet file.lean    # check only; reports errors and round-trip failures
cargo run --release --example bench
```

## Tests

```
cargo test
```

- `roundtrip.rs` — the losslessness invariant, including on malformed input
- `parser.rs` — tree shape: precedence, associativity, layout, error recovery
- `ast.rs` — the typed API
- `corpus.rs` — whole files, plus robustness properties: every *prefix* of every
  corpus file and every single-line deletion must parse without panicking and
  still round-trip, and 400 random token soups must round-trip

Parsing is linear in input size, at roughly 1.7 MB/s in release builds.

[chumsky]: https://github.com/zesterer/chumsky
[rowan]: https://github.com/rust-analyzer/rowan

## License

Dual-licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
