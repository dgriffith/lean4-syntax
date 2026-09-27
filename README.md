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

## The HIR

`ast` gives typed views over the lossless CST, where every accessor returns
`Option` (the tree must represent broken code) and children are borrowed (it must
round-trip byte-for-byte). Both are right for editing and wrong for analysis.

So `hir` is a second tree: a real ADT — `Term`, `Tactic`, `Item` — reached through
`hir::lower`. The payoff is not the enum but that **lowering concentrates all the
`Option` handling in one place**, so everything downstream sees total data.

```rust
let parse = lean4_syntax::parse(source);
let module = lean4_syntax::hir::lower(&parse.syntax());

for (_, item) in module.items() {
    println!("{:?} {:?}", item.kind, item.name);
}
```

**Arena, not `Box`.** Nodes live in arenas on `Module` and refer to each other by
integer id. That follows from wanting analysis *and* rewriting at once: rewriting
needs each node to link back to source, analysis needs structural equality, and a
span stored *inside* a node makes derived equality positional and useless for
comparison. With an arena the id is the identity, so source links live outside
the nodes in a `SourceMap`. The cost is real — an id means nothing without its
`Module`, so methods take `&Module` and there are no deep nested patterns.

**Two kinds of equality**, and the obvious reading is the wrong one. Derived
`PartialEq` is *shallow*: it compares a node's payload and its children's *ids*,
which are arena positions. Two identical subterms in different places are **not**
`==`. `Module::same_term` compares structure, resolving binders, patterns and
tactics. So `==` is for caching keyed on identity; `same_term` answers whether
two subterms are the same expression. An analysis using the wrong one would
silently miss every repeated subterm.

**One visitor.** `hir::visit` is the single place that knows each node's shape.
Traversal, structural comparison and id remapping — which rewriting needs — are
all derived from it, rather than each carrying its own forty-arm match.

**Totality.** Lowering never panics and never drops syntax: anything unmodelled
becomes `Opaque`, and anything that *should* have lowered is additionally
recorded as a `LoweringError`. That separation is what makes coverage measurable:
`Opaque` without an error is a deliberate boundary, `Opaque` with one is a gap.
`examples/lower_report.rs` reports both.

## Scope

Lean 4's grammar is user-extensible — `notation`, `infixl`, `macro_rules` and
`syntax` add grammar as a file elaborates — so no parser outside Lean itself can
claim total coverage. This one covers the core language and **records**
grammar-extending commands without applying them.

Covered: Lean's module system (`module`, `public import`, `@[expose] public
section`); all commands and declaration forms (`def`, `theorem`, `structure`,
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
| unrecognised notation | parses at an *assumed* precedence, flagged in the tree — see Notation |
| unrecognised commands | `UNKNOWN_CMD` plus a balanced token run, so an unfamiliar command does not cascade into the declarations after it |

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

### `|` is the hard character

`|` does four jobs in Lean: absolute value, the match-alternative separator, the
`rcases` alternation, and the `first | …` branch marker. Absolute value is
supported anyway, and it is worth knowing why that is safe rather than reckless.

The separators are matched by explicit `tok(PIPE)` rules inside the grammar that
needs them — `match` alternatives, constructor lists, `rcases` patterns — and
never reach the term parser. And a wrong attempt fails cheaply, because the
closing `|` is required: in

```lean
| a => f
| b => g
```

reading `| b` as an absolute value dies at the `=>` where the closing `|` should
be, so the application ends where it should. That is worth roughly 8% of the
mathlib clean-parse rate on its own.

The cost is pattern alternation, listed under limitations below.

### Notation

Lean's grammar is user-extensible, and mathlib exercises that hard: 292 distinct
characters appear in it that no fixed table would anticipate — including `⁅x, y⁆`
from General Punctuation and `Kᗮ` from *Canadian Syllabics*. So notation is
handled in two layers.

**A curated table** for the head of the distribution, with Lean's own
precedences: `‖x‖`, `⌊x⌋`, `⌈x⌉`, `⟪x, y⟫`, `⁅x, y⁆` as delimiter pairs; `≫`,
`⟶`, `⥤`, `•`, `''`, `≡`, `⧸`, `⊗` as operators; `∑`, `∏`, `⋃`, `⨆`, `∫` as
*binders*, since they bind a variable like a quantifier rather than combining two
terms; and `⊤`, `⊥`, `∅`, `∞`, `𝟙` as constants.

**A generic fallback** for everything else. Any non-ASCII character reaches the
parser as a `SYMBOL` token — the lexer cannot know a character is *not* notation,
because Lean's token table admits arbitrary strings — and a `SYMBOL` works as an
atom, as an infix operator, or, when written flush against its operand, as a
postfix one. Operators may carry a bracketed parameter, so mathlib's bundled
arrows (`M →ₗ[R] N`, `M ⊗[R] N`) parse without being enumerated.

The catch is precedence: a curated operator has Lean's, a generic one has a
guess. **The tree says which.** A generic operator keeps the `SYMBOL` token kind
inside its `OPERATOR` node, so anything reasoning about associativity can tell a
known precedence from an assumed one, rather than silently trusting a guess.

### Known limitations

- **Precedence is assumed for uncurated operators.** A file's own `notation` and
  `infixl` declarations are recorded but not applied, so an operator outside the
  curated table parses at a default precedence rather than its declared one.
  This is visible in the tree (see Notation) rather than silent.
- **Pattern alternation, `| a | b => e`, is not supported.** It is the one shape
  that genuinely collides with `|x|` for absolute value, which *is* supported:
  the alternation would have to be disambiguated from an absolute value opening
  where a pattern is expected.
- **`{a, b}` is read as a set literal**, never as a structure instance with
  abbreviated fields. The two are ambiguous in surface syntax and Lean separates
  them by expected type, which a parser does not have. A brace form with at
  least one `x := e` field does support abbreviation.
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

## Validation against mathlib

`examples/corpus_report.rs` parses a directory tree and reports what the parser
cannot handle. Against **mathlib4 at `516d3125`** — 9,160 files, 102 MB:

| | |
|---|---|
| Round-trip failures | **0** |
| Panics | **0** |
| Files parsing with no errors | 63.5% |
| Files containing a character the lexer cannot classify | 0.5% |

The first two numbers are the ones that had to be zero: losslessness and
not-crashing are unconditional promises, and they hold across 102 MB of real
Lean including every construct mathlib uses.

The clean rate has moved 0.5% → 9.3% → 30.8% → 46.1% → 63.5% as the gaps below
were closed.
Unclassifiable characters, once present in 78.4% of files and the hard ceiling on
that rate, are now down to 0.5%.

Finding the gaps needed the report to separate causes from symptoms, which it
does three ways: it ranks by the position the parser *failed* at rather than
where recovery resumed, takes only the first failure per file, and censuses
unclassifiable characters directly. Without that, the ranking is dominated by
fragments — the top entry was an innocent `(` continuing a declaration whose
head had already failed.

Running it found gaps that a hand-written corpus never would, most of them core
language rather than mathlib notation: the module system (in 8,750 of 9,160
files), `noncomputable section`, `variable (α) in`, `show T by tac`,
newline-separated structure instance fields, structure fields with binders,
`#[…]` array literals, the `↑`/`⇑`/`↥` coercion arrows, `include`/`omit`/`export`,
`nonrec` — which was being read as a command, detaching it from the declaration
it modifies — named arguments `f (p := e)`, `$x` antiquotations, and `ℕ+` and
`→+`, which are single tokens in Lean rather than an identifier or arrow plus
`+`. The corpus files and `tests/corpus_forms.rs` keep all of them fixed.

Several were *layout* bugs, which matter more than their counts: each construct
parsed in isolation and failed in place. An unguarded `repeated()` crossing a
line break is the shape they share — `have ⟨t, ht⟩ := f x` absorbing its own
body as one more argument of `f`, `intros` claiming the next line's tactic as a
pattern, `import A.B` swallowing the following command's name as a module. The
rule they all needed is the one application arguments already had: a
continuation must be indented past the position its construct was anchored at.

Lowering to the HIR is measured the same way, by `examples/lower_report.rs`.
Over the same corpus it produces **9.4M HIR nodes with zero panics**, and 0.7% of
those nodes are `Opaque` — all of them at the two deliberate boundaries,
uninterpreted tactics and syntax quotations. Zero `LoweringError`s, meaning
nothing was recognised and then failed to lower.

```
cargo run --release --example corpus_report -- path/to/mathlib4
cargo run --release --example lower_report  -- path/to/mathlib4
```

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
