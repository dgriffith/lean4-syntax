//! An owned, total representation of a Lean file, for analysis and rewriting.
//!
//! # Why a second tree
//!
//! [`crate::ast`] gives typed views over the lossless CST. Every accessor there
//! returns `Option`, because the CST must represent broken code, and its
//! children are borrowed rather than owned, because it must round-trip
//! byte-for-byte. Both properties are right for editing and wrong for analysis:
//! you do not want an `Option` in the middle of a transformation you are trying
//! to reason about.
//!
//! So this module is a real algebraic data type — [`Term`], [`Tactic`],
//! [`Item`] — reached through [`lower()`]. The payoff is not the enum itself but
//! that **lowering concentrates all the `Option` handling in one place**, so
//! everything downstream sees total data.
//!
//! # Arena, not `Box`
//!
//! Nodes live in arenas on [`Module`] and refer to each other by integer id.
//! That choice follows from wanting analysis *and* rewriting at once. Rewriting
//! needs each node to link back to source; analysis needs structural equality,
//! so that two subterms can be compared, memoised or hash-consed. Those pull
//! against each other: a span stored *inside* a node makes derived
//! `PartialEq`/`Hash` positional and therefore useless for comparison.
//!
//! With an arena the id *is* the identity, so source links live outside
//! the nodes in a [`SourceMap`]. The cost is real and shows up immediately: an
//! id means nothing without its `Module`, so methods take `&Module`, and there
//! are no deep nested patterns.
//!
//! # Two kinds of equality
//!
//! Worth being precise about, because the obvious reading is wrong. Derived
//! `PartialEq` on [`Term`] is **shallow**: it compares a node's own payload and
//! its children's *ids*. Since ids are arena positions, two structurally
//! identical subterms in different places are **not** equal by `==`:
//!
//! ```
//! # use lean4_syntax::hir::{self, Term};
//! let parse = lean4_syntax::parse("def f := (a + b, a + b)");
//! let module = hir::lower(&parse.syntax());
//! let sums: Vec<_> = module.terms().filter(|(_, t)| matches!(t, Term::Infix { .. })).collect();
//! assert_ne!(sums[0].1, sums[1].1);                        // different child ids
//! assert!(module.same_term(sums[0].0, sums[1].0));         // same structure
//! ```
//!
//! So `==` is the right tool for caching and memoisation keyed on identity, and
//! [`Module::same_term`] is the right tool for asking whether two subterms *are*
//! the same expression. The latter costs a traversal; the former is a
//! comparison. Getting this backwards would make an analysis quietly miss every
//! repeated subterm.
//!
//! The one exception is [`Term::Opaque`], which embeds a syntax pointer because
//! that *is* its content. Two opaque regions with identical text at different
//! positions compare unequal — which is the honest answer, since neither has
//! been interpreted.
//!
//! # Totality
//!
//! [`lower()`] never panics and never drops syntax: anything it does not model
//! becomes `Opaque`, and anything it *should* have modelled is additionally
//! recorded as a [`LoweringError`]. `Opaque` is the only escape hatch, which is
//! what makes coverage measurable — see `examples/lower_report.rs`.

pub mod lower;
pub mod visit;

use crate::kind::Lean;
use rowan::ast::SyntaxNodePtr;
use std::collections::HashMap;
use std::ops::Index;

pub use lower::lower;
pub use visit::{Collect, Visitor};

/// A name as written, which may be dotted (`Nat.succ`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(pub String);

impl Name {
    /// The dot-separated components. `Nat.succ` yields `["Nat", "succ"]`.
    ///
    /// Note that a guillemet-escaped component may itself contain dots; this
    /// splits naively, which is enough for the uses it has today.
    pub fn components(&self) -> impl Iterator<Item = &str> {
        self.0.split('.')
    }

    /// The last component, which is the name within its namespace.
    pub fn base(&self) -> &str {
        self.0.rsplit('.').next().unwrap_or(&self.0)
    }

    /// The text as written.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Name {
        Name(s.to_string())
    }
}

/// Declares an arena index type.
macro_rules! id {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(u32);

        impl $name {
            /// The raw index, for callers that need to key their own tables.
            pub fn index(self) -> usize {
                self.0 as usize
            }

            /// Builds an id from a raw index. Used by canonicalisation, which
            /// deliberately produces ids that do not refer to real slots.
            #[allow(dead_code)]
            pub(crate) fn from_raw(raw: u32) -> Self {
                $name(raw)
            }
        }
    };
}

id!(
    /// A term in a [`Module`]'s arena.
    TermId
);
id!(
    /// A binder in a [`Module`]'s arena.
    BinderId
);
id!(
    /// A tactic in a [`Module`]'s arena.
    TacticId
);
id!(
    /// A pattern in a [`Module`]'s arena.
    PatId
);
id!(
    /// A top-level item in a [`Module`].
    ItemId
);

/// Any HIR node, for keying the source map uniformly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum HirId {
    /// A term.
    Term(TermId),
    /// A binder.
    Binder(BinderId),
    /// A tactic.
    Tactic(TacticId),
    /// A pattern.
    Pat(PatId),
    /// A top-level item.
    Item(ItemId),
}

// ---- Terms -----------------------------------------------------------------

/// Whether an operator's precedence came from Lean or was assumed.
///
/// The parser applies a default precedence to notation it does not have a rule
/// for. Anything reasoning about associativity must be able to tell the two
/// apart rather than silently trusting a guess.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Precedence {
    /// Taken from Lean's own notation declarations.
    Known,
    /// Defaulted, because the operator has no rule here.
    Assumed,
}

/// The universe-level keyword of a sort.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SortKind {
    /// `Type`
    Type,
    /// `Prop`
    Prop,
    /// `Sort`
    Sort,
}

/// The binder-introducing symbol of a quantifier or big operator.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QuantifierKind {
    /// `∀`
    Forall,
    /// `∃`
    Exists,
    /// `Σ`
    Sigma,
    /// `Π`
    Pi,
    /// A big operator such as `∑`, `∏`, `⨆` or `∫`, kept as written since they
    /// differ only in which operation they fold.
    BigOperator(Name),
}

/// A literal, kept as written rather than parsed into a value.
///
/// Preserving the spelling matters for rewriting: `0x10` and `16` mean the same
/// thing but should not be silently interchanged in someone's source.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Lit {
    /// An integer, in any base.
    Nat(String),
    /// A decimal or scientific literal.
    Scientific(String),
    /// A string literal, including its quotes and escapes.
    Str(String),
    /// A character literal.
    Char(String),
    /// A name literal, `` `Nat.succ ``.
    Name(String),
}

/// One argument of an application.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Arg {
    /// Present for `f (p := e)`.
    pub name: Option<Name>,
    /// The argument itself.
    pub value: TermId,
}

/// One `| pat, pat => body` alternative.
///
/// The body is a term or a tactic sequence depending on where the alternative
/// appears — `match` gives terms, `induction … with` gives tactics.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Arm {
    /// The patterns this alternative matches.
    pub pats: Vec<PatId>,
    /// The right-hand side.
    pub body: ArmBody,
}

/// The right-hand side of an alternative.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ArmBody {
    /// A term, as in a `match`.
    Term(TermId),
    /// A tactic sequence, as in `induction n with | zero => rfl`.
    Tactic(TacticId),
}

/// One field of a structure instance.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldInit {
    /// The field's name.
    pub name: Name,
    /// The value, absent for the abbreviated form `{ x }` meaning `{ x := x }`.
    pub value: Option<TermId>,
}

/// One step of a `calc` block.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CalcStep {
    /// The relation being asserted.
    pub relation: TermId,
    /// Its proof.
    pub proof: TermId,
}

/// One statement of a `do` block.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DoStmt {
    /// `let x := e`
    Let {
        pat: PatId,
        ty: Option<TermId>,
        value: TermId,
        mutable: bool,
    },
    /// `let x ← e`
    LetArrow {
        pat: PatId,
        ty: Option<TermId>,
        value: TermId,
        mutable: bool,
    },
    /// `x ← e`
    Bind { pat: PatId, value: TermId },
    /// `x := e`, reassigning a `mut` binding.
    Reassign { name: Name, value: TermId },
    /// `return e`
    Return(Option<TermId>),
    /// `if c then … else …`
    If {
        cond: TermId,
        then_branch: Vec<DoStmt>,
        else_branch: Option<Vec<DoStmt>>,
    },
    /// `for x in e do …`
    For {
        pat: PatId,
        iterable: TermId,
        body: Vec<DoStmt>,
    },
    /// `while c do …`
    While { cond: TermId, body: Vec<DoStmt> },
    /// `try … catch … finally …`
    Try {
        body: Vec<DoStmt>,
        catches: Vec<Vec<DoStmt>>,
        finally_branch: Option<Vec<DoStmt>>,
    },
    /// `break`
    Break,
    /// `continue`
    Continue,
    /// A bare expression.
    Expr(TermId),
    /// A statement lowering did not model.
    Opaque(SyntaxNodePtr<Lean>),
}

/// A term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// An identifier used as a term. May be dotted.
    Ref(Name),
    /// `.mk` — a constructor to be resolved from the expected type.
    DotIdent(Name),
    /// A literal.
    Lit(Lit),
    /// `_`
    Hole,
    /// `?x` or `?_`
    SyntheticHole(Option<Name>),
    /// `sorry`
    Sorry,
    /// `Type u`, `Prop`, `Sort 0`
    Sort {
        kind: SortKind,
        level: Option<TermId>,
    },
    /// Notation used as a term with no rule of its own: `⊤`, `∞`, `𝟙`.
    Symbol(Name),
    /// Function application.
    App { func: TermId, args: Vec<Arg> },
    /// A binary operator application.
    Infix {
        op: Name,
        precedence: Precedence,
        lhs: TermId,
        rhs: TermId,
    },
    /// A prefix operator application.
    Prefix { op: Name, operand: TermId },
    /// A postfix operator application, including modifier notation like `sᶜ`.
    Postfix { op: Name, operand: TermId },
    /// `A → B`
    Arrow { domain: TermId, codomain: TermId },
    /// `(x : A) → B x`
    DepArrow {
        binders: Vec<BinderId>,
        codomain: TermId,
    },
    /// `fun x => e`
    Fun {
        binders: Vec<BinderId>,
        body: TermId,
    },
    /// `fun | p => e | q => f`
    FunAlts { arms: Vec<Arm> },
    /// `∀ x, p x` and the big operators.
    Quantifier {
        kind: QuantifierKind,
        binders: Vec<BinderId>,
        body: TermId,
    },
    /// `let x := e; body`
    Let {
        pat: PatId,
        ty: Option<TermId>,
        value: Option<TermId>,
        arms: Vec<Arm>,
        body: TermId,
    },
    /// `have h : T := e; body`. The value may be absent in tactic mode.
    Have {
        pat: Option<PatId>,
        ty: Option<TermId>,
        value: Option<TermId>,
        body: TermId,
    },
    /// `show T from e` or `show T by tac`
    Show { ty: TermId, proof: Option<TermId> },
    /// `suffices h : T from e`
    Suffices {
        pat: Option<PatId>,
        ty: Option<TermId>,
        proof: Option<TermId>,
    },
    /// `match e with | …`
    Match { discrs: Vec<TermId>, arms: Vec<Arm> },
    /// `if c then a else b`
    If {
        cond: TermId,
        then_branch: TermId,
        else_branch: TermId,
    },
    /// `do …`
    Do(Vec<DoStmt>),
    /// `by …`
    By(TacticId),
    /// `(a, b)`
    Tuple(Vec<TermId>),
    /// `⟨a, b⟩`
    AnonCtor(Vec<TermId>),
    /// `{ x := 1 }` and `{ s with x := 1 }`
    StructInst {
        source: Option<TermId>,
        fields: Vec<FieldInit>,
    },
    /// `[a, b]`
    ListLit(Vec<TermId>),
    /// `#[a, b]`
    ArrayLit(Vec<TermId>),
    /// `{a, b}`
    SetLit(Vec<TermId>),
    /// `{ x : T // p x }`
    Subtype { binder: BinderId, predicate: TermId },
    /// `{ x | p x }`
    SetOf { binder: BinderId, predicate: TermId },
    /// `e.1`
    Proj { receiver: TermId, index: u32 },
    /// `e.field` and `e |>.field`
    Field { receiver: TermId, name: Name },
    /// `(e : T)`
    Ascription { term: TermId, ty: TermId },
    /// `@f`
    Explicit(TermId),
    /// `·`
    Placeholder,
    /// `$x`
    Antiquotation(Option<Name>),
    /// A curated delimiter pair: `‖x‖`, `⌊x⌋`, `⟪x, y⟫`.
    Bracketed { open: Name, parts: Vec<TermId> },
    /// `Foo.{u, v}` — a term with explicit universe arguments.
    Universes { term: TermId, levels: Vec<Name> },
    /// `calc a = b := h …`
    Calc { steps: Vec<CalcStep> },
    /// Syntax lowering did not interpret.
    ///
    /// The only escape hatch, and the only variant whose equality is
    /// positional: two opaque regions with identical text compare unequal,
    /// because neither has been interpreted.
    Opaque(SyntaxNodePtr<Lean>),
}

// ---- Binders and patterns --------------------------------------------------

/// How a binder's argument is supplied at a call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Explicitness {
    /// `(x : T)` — given positionally.
    Explicit,
    /// `{x : T}` — inferred.
    Implicit,
    /// `⦃x : T⦄` — inferred, but only once something after it is given.
    StrictImplicit,
    /// `[Inst]` — found by instance resolution.
    Instance,
}

/// A bound variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Binder {
    /// The names introduced. An anonymous instance binder introduces none.
    pub names: Vec<Name>,
    /// The declared type, if written.
    pub ty: Option<TermId>,
    /// How the argument is supplied.
    pub explicitness: Explicitness,
    /// A default or tactic value, from `(x : T := v)`.
    pub default: Option<TermId>,
}

/// A pattern, covering both `match` patterns and `rcases`-style ones.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pat {
    /// A name binding.
    Name(Name),
    /// `_`
    Hole,
    /// `-`, which clears the hypothesis rather than binding it.
    Discard,
    /// `⟨a, b⟩` or `(a, b)`
    Tuple(Vec<PatId>),
    /// `a | b`
    Alt(Vec<PatId>),
    /// A `match` pattern, which is syntactically a term.
    Term(TermId),
    /// A pattern lowering did not model.
    Opaque(SyntaxNodePtr<Lean>),
}

// ---- Tactics ---------------------------------------------------------------

/// Where a tactic acts.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    /// Named hypotheses.
    pub hypotheses: Vec<Name>,
    /// True when the goal is included, written `⊢`.
    pub goal: bool,
    /// True for `at *`.
    pub everywhere: bool,
}

/// One entry of a simp-like tactic's argument list.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SimpArg {
    /// A lemma to use.
    Lemma { term: TermId, reversed: bool },
    /// `-foo`, removing a lemma from the set.
    Removed(TermId),
    /// `*`, admitting all hypotheses.
    Wildcard,
}

/// One rewrite rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RwRule {
    /// The equation to rewrite with.
    pub term: TermId,
    /// True for `← foo`, rewriting right to left.
    pub reversed: bool,
}

/// A tactic.
///
/// Shaped like the parser's tactic nodes: one variant per *shape*, with the
/// tactic's name carried as data. Lean's tactic vocabulary is open-ended, so a
/// variant per name would be both enormous and permanently incomplete.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Tactic {
    /// A sequence of tactics, as in a `by` block.
    Seq(Vec<TacticId>),
    /// `simp only [foo, ← bar] at h ⊢` and the other simp-like tactics.
    Simp {
        name: Name,
        only: bool,
        args: Vec<SimpArg>,
        location: Option<Location>,
    },
    /// `rw [foo, ← bar] at h`
    Rewrite {
        name: Name,
        rules: Vec<RwRule>,
        location: Option<Location>,
        occurrence: Option<u32>,
    },
    /// A tactic taking terms, such as `exact`, `apply` or `use`.
    Apply {
        name: Name,
        terms: Vec<TermId>,
        location: Option<Location>,
    },
    /// `intro x y ⟨a, b⟩`
    Intro { name: Name, pats: Vec<PatId> },
    /// `cases`, `rcases`, `induction`.
    Cases {
        name: Name,
        targets: Vec<TermId>,
        using_term: Option<TermId>,
        generalizing: Vec<Name>,
        arms: Vec<Arm>,
        pats: Vec<PatId>,
    },
    /// `have h : T := e`, `obtain ⟨a, b⟩ := e`, `set x := e`.
    Have {
        name: Name,
        pat: Option<PatId>,
        ty: Option<TermId>,
        value: Option<TermId>,
    },
    /// `case inl h => …`, `next x => …`
    Case {
        name: Name,
        tags: Vec<Name>,
        body: TacticId,
    },
    /// `· tac` — focus the first goal.
    Focus(TacticId),
    /// `tac <;> tac`
    Chain(Vec<TacticId>),
    /// `first | tac | tac`
    Alt(Vec<TacticId>),
    /// `try`, `repeat`, `all_goals`, `iterate n`.
    Combinator {
        name: Name,
        count: Option<u32>,
        body: TacticId,
    },
    /// `conv at h in pat => …`
    Conv {
        name: Name,
        location: Option<Location>,
        pattern: Option<TermId>,
        body: TacticId,
    },
    /// `show T`
    Show(TermId),
    /// A `calc` block in tactic position.
    Calc { steps: Vec<CalcStep> },
    /// A tactic with no shape of its own: one taking no arguments, or one
    /// lowering did not model. The name is present when the tactic had one.
    Opaque {
        name: Option<Name>,
        node: SyntaxNodePtr<Lean>,
    },
}

// ---- Items -----------------------------------------------------------------

/// What kind of top-level item this is.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ItemKind {
    /// `def`
    Def,
    /// `theorem` or `lemma`
    Theorem,
    /// `abbrev`
    Abbrev,
    /// `example`
    Example,
    /// `instance`
    Instance,
    /// `axiom`
    Axiom,
    /// `opaque`
    Opaque,
    /// `structure`
    Structure,
    /// `class`
    Class,
    /// `inductive`
    Inductive,
    /// `namespace N`
    Namespace,
    /// `section` or `end`, which open and close a scope.
    Section,
    /// `end`
    End,
    /// `import`
    Import,
    /// `open`
    Open,
    /// `variable`
    Variable,
    /// `universe`
    Universe,
    /// A command carried through without being modelled.
    Other(Name),
}

/// One constructor of an inductive type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ctor {
    /// The constructor's name.
    pub name: Name,
    /// Its arguments.
    pub binders: Vec<BinderId>,
    /// Its result type, if written.
    pub ty: Option<TermId>,
    /// Its docstring, if present.
    pub doc: Option<String>,
}

/// One field of a structure or class.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldDecl {
    /// The field's name.
    pub name: Name,
    /// Its arguments, for a field that takes some.
    pub binders: Vec<BinderId>,
    /// Its type, if written.
    pub ty: Option<TermId>,
    /// Its default value, if written.
    pub default: Option<TermId>,
    /// Its docstring, if present.
    pub doc: Option<String>,
}

/// A top-level item.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Item {
    /// What kind of item this is.
    pub kind: ItemKind,
    /// Its name, where it has one. `example` never does.
    pub name: Option<Name>,
    /// Its docstring, as written including delimiters.
    pub doc: Option<String>,
    /// Its attributes, each as written.
    pub attrs: Vec<String>,
    /// Modifier keywords such as `private` or `noncomputable`, in source order.
    pub modifiers: Vec<Name>,
    /// Its binders.
    pub binders: Vec<BinderId>,
    /// Its declared type, if written.
    pub ty: Option<TermId>,
    /// Its defining term, for a `:= value` body.
    pub value: Option<TermId>,
    /// Its defining equations, for a `| pat => e` body.
    pub arms: Vec<Arm>,
    /// Constructors, for an inductive.
    pub ctors: Vec<Ctor>,
    /// Fields, for a structure or class.
    pub fields: Vec<FieldDecl>,
    /// Names from a `deriving` clause.
    pub deriving: Vec<Name>,
    /// Items nested inside this one: the single command scoped by
    /// `variable … in`, or every declaration inside a `mutual … end` block.
    pub nested: Vec<ItemId>,
}

// ---- Module ----------------------------------------------------------------

/// Links HIR nodes to the syntax they came from, and back.
///
/// Kept outside the nodes so that HIR values stay structurally comparable. The
/// reverse direction is not optional: Lean's `InfoTree` reports goal states by
/// *source position*, so mapping a position back to a HIR node is how those
/// annotations will attach.
#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    to_node: HashMap<HirId, SyntaxNodePtr<Lean>>,
    to_hir: HashMap<SyntaxNodePtr<Lean>, HirId>,
}

impl SourceMap {
    /// Records the syntax a HIR node came from.
    pub fn insert(&mut self, id: HirId, ptr: SyntaxNodePtr<Lean>) {
        self.to_node.insert(id, ptr);
        // A CST node may lower to several HIR nodes; keep the first, which is
        // the outermost and the one a position lookup should land on.
        self.to_hir.entry(ptr).or_insert(id);
    }

    /// The syntax a HIR node came from.
    pub fn node(&self, id: HirId) -> Option<SyntaxNodePtr<Lean>> {
        self.to_node.get(&id).copied()
    }

    /// The HIR node a piece of syntax lowered to.
    pub fn hir(&self, ptr: SyntaxNodePtr<Lean>) -> Option<HirId> {
        self.to_hir.get(&ptr).copied()
    }

    /// How many links are recorded.
    pub fn len(&self) -> usize {
        self.to_node.len()
    }

    /// True when nothing has been recorded.
    pub fn is_empty(&self) -> bool {
        self.to_node.is_empty()
    }
}

/// Syntax that should have lowered to a specific form but did not.
///
/// Distinct from an `Opaque` node, which is the *expected* outcome for syntax
/// this crate deliberately does not model. An error means the shape was
/// recognised and still could not be lowered, which is a gap worth closing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweringError {
    /// What was missing.
    pub message: String,
    /// The syntax it concerns.
    pub node: SyntaxNodePtr<Lean>,
}

/// A lowered file: the arenas, the items, and the map back to syntax.
#[derive(Debug, Clone, Default)]
pub struct Module {
    terms: Vec<Term>,
    binders: Vec<Binder>,
    tactics: Vec<Tactic>,
    pats: Vec<Pat>,
    items: Vec<Item>,
    /// Links to the syntax each node came from.
    pub source: SourceMap,
    /// Shapes that were recognised but could not be lowered.
    pub errors: Vec<LoweringError>,
}

impl Module {
    /// The file's top-level items, in source order.
    pub fn items(&self) -> impl Iterator<Item = (ItemId, &Item)> {
        self.items
            .iter()
            .enumerate()
            .map(|(i, item)| (ItemId(i as u32), item))
    }

    /// Every term in the file, in allocation order.
    pub fn terms(&self) -> impl Iterator<Item = (TermId, &Term)> {
        self.terms
            .iter()
            .enumerate()
            .map(|(i, t)| (TermId(i as u32), t))
    }

    /// Every tactic in the file, in allocation order.
    pub fn tactics(&self) -> impl Iterator<Item = (TacticId, &Tactic)> {
        self.tactics
            .iter()
            .enumerate()
            .map(|(i, t)| (TacticId(i as u32), t))
    }

    /// Every binder in the file, in allocation order.
    pub fn binders(&self) -> impl Iterator<Item = (BinderId, &Binder)> {
        self.binders
            .iter()
            .enumerate()
            .map(|(i, b)| (BinderId(i as u32), b))
    }

    /// Every pattern in the file, in allocation order.
    pub fn pats(&self) -> impl Iterator<Item = (PatId, &Pat)> {
        self.pats
            .iter()
            .enumerate()
            .map(|(i, p)| (PatId(i as u32), p))
    }

    /// How many nodes lowering left uninterpreted.
    ///
    /// The coverage metric: it should fall as lowering learns more shapes.
    pub fn opaque_count(&self) -> usize {
        self.terms
            .iter()
            .filter(|t| matches!(t, Term::Opaque(_)))
            .count()
            + self
                .tactics
                .iter()
                .filter(|t| matches!(t, Tactic::Opaque { .. }))
                .count()
            + self
                .pats
                .iter()
                .filter(|p| matches!(p, Pat::Opaque(_)))
                .count()
    }

    /// The ids a term refers to, in a stable order.
    pub fn term_refs(&self, id: TermId) -> Collect {
        let mut term = self[id].clone();
        let mut refs = Collect::default();
        visit::visit_term(&mut term, &mut refs);
        refs
    }

    /// The ids a tactic refers to, in a stable order.
    pub fn tactic_refs(&self, id: TacticId) -> Collect {
        let mut tactic = self[id].clone();
        let mut refs = Collect::default();
        visit::visit_tactic(&mut tactic, &mut refs);
        refs
    }

    /// True when two terms have the same structure, wherever their parts sit in
    /// the arena.
    ///
    /// This is the equality an analysis wants; `==` compares arena positions.
    /// Exact rather than a fingerprint, so a rewriting tool can act on the
    /// answer: the cost is one traversal of the smaller subtree.
    pub fn same_term(&self, a: TermId, b: TermId) -> bool {
        if a == b {
            return true;
        }
        // Recurses with the depth of the term; see `lower` for why that needs
        // guarding rather than trusting the default stack.
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || self.same_term_inner(a, b))
    }

    fn same_term_inner(&self, a: TermId, b: TermId) -> bool {
        let (ca, ra) = self.canonical(self[a].clone(), visit::visit_term);
        let (cb, rb) = self.canonical(self[b].clone(), visit::visit_term);
        ca == cb && self.same_refs(&ra, &rb)
    }

    /// True when two binders have the same structure.
    pub fn same_binder(&self, a: BinderId, b: BinderId) -> bool {
        if a == b {
            return true;
        }
        let (ca, ra) = self.canonical(self[a].clone(), visit::visit_binder);
        let (cb, rb) = self.canonical(self[b].clone(), visit::visit_binder);
        ca == cb && self.same_refs(&ra, &rb)
    }

    /// True when two patterns have the same structure.
    pub fn same_pat(&self, a: PatId, b: PatId) -> bool {
        if a == b {
            return true;
        }
        let (ca, ra) = self.canonical(self[a].clone(), visit::visit_pat);
        let (cb, rb) = self.canonical(self[b].clone(), visit::visit_pat);
        ca == cb && self.same_refs(&ra, &rb)
    }

    /// True when two tactics have the same structure.
    pub fn same_tactic(&self, a: TacticId, b: TacticId) -> bool {
        if a == b {
            return true;
        }
        let (ca, ra) = self.canonical(self[a].clone(), visit::visit_tactic);
        let (cb, rb) = self.canonical(self[b].clone(), visit::visit_tactic);
        ca == cb && self.same_refs(&ra, &rb)
    }

    /// Canonicalises a node's ids to traversal order, and reports the originals.
    ///
    /// Comparing canonical forms answers "same shape?"; comparing the reported
    /// ids recursively answers "same children?".
    fn canonical<T: Clone>(&self, node: T, visit: fn(&mut T, &mut dyn Visitor)) -> (T, Collect) {
        let mut refs = Collect::default();
        let mut for_refs = node.clone();
        visit(&mut for_refs, &mut refs);
        let mut canon = node;
        visit(&mut canon, &mut visit::Canonicalize::default());
        (canon, refs)
    }

    fn same_refs(&self, a: &Collect, b: &Collect) -> bool {
        a.terms.len() == b.terms.len()
            && a.binders.len() == b.binders.len()
            && a.pats.len() == b.pats.len()
            && a.tactics.len() == b.tactics.len()
            && a.terms
                .iter()
                .zip(&b.terms)
                .all(|(x, y)| self.same_term(*x, *y))
            && a.binders
                .iter()
                .zip(&b.binders)
                .all(|(x, y)| self.same_binder(*x, *y))
            && a.pats
                .iter()
                .zip(&b.pats)
                .all(|(x, y)| self.same_pat(*x, *y))
            && a.tactics
                .iter()
                .zip(&b.tactics)
                .all(|(x, y)| self.same_tactic(*x, *y))
    }

    fn alloc_term(&mut self, term: Term) -> TermId {
        self.terms.push(term);
        TermId((self.terms.len() - 1) as u32)
    }

    fn alloc_binder(&mut self, binder: Binder) -> BinderId {
        self.binders.push(binder);
        BinderId((self.binders.len() - 1) as u32)
    }

    fn alloc_tactic(&mut self, tactic: Tactic) -> TacticId {
        self.tactics.push(tactic);
        TacticId((self.tactics.len() - 1) as u32)
    }

    fn alloc_pat(&mut self, pat: Pat) -> PatId {
        self.pats.push(pat);
        PatId((self.pats.len() - 1) as u32)
    }

    fn alloc_item(&mut self, item: Item) -> ItemId {
        self.items.push(item);
        ItemId((self.items.len() - 1) as u32)
    }
}

impl Index<TermId> for Module {
    type Output = Term;
    fn index(&self, id: TermId) -> &Term {
        &self.terms[id.index()]
    }
}

impl Index<BinderId> for Module {
    type Output = Binder;
    fn index(&self, id: BinderId) -> &Binder {
        &self.binders[id.index()]
    }
}

impl Index<TacticId> for Module {
    type Output = Tactic;
    fn index(&self, id: TacticId) -> &Tactic {
        &self.tactics[id.index()]
    }
}

impl Index<PatId> for Module {
    type Output = Pat;
    fn index(&self, id: PatId) -> &Pat {
        &self.pats[id.index()]
    }
}

impl Index<ItemId> for Module {
    type Output = Item;
    fn index(&self, id: ItemId) -> &Item {
        &self.items[id.index()]
    }
}
