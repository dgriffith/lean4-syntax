//! Typed views over the syntax tree.
//!
//! The tree itself is untyped: every node is a [`SyntaxNode`] carrying a
//! [`SyntaxKind`]. The types here are zero-cost wrappers that make a node's
//! shape checkable and its parts reachable by name, in the style of
//! rust-analyzer's generated AST layer:
//!
//! ```
//! # use lean4_syntax::ast::{AstNode, Command, HasDecl, SourceFile};
//! let parse = lean4_syntax::parse("/-- doubles -/ def double (n : Nat) : Nat := n + n");
//! let file = SourceFile::cast(parse.syntax()).unwrap();
//! let Some(Command::Def(def)) = file.commands().next() else { panic!() };
//! assert_eq!(def.name().unwrap().text(), "double");
//! assert_eq!(def.doc_comment().unwrap().text(), "/-- doubles -/");
//! ```
//!
//! Every accessor returns `Option` or an iterator: a tree built from source
//! with syntax errors is still navigable, so nothing here may assume a
//! well-formed parse.

use crate::kind::{SyntaxKind, SyntaxKind::*, SyntaxNode, SyntaxToken};

/// A node with a statically known kind.
pub trait AstNode: Sized {
    /// Can a node of this kind be viewed as `Self`?
    fn can_cast(kind: SyntaxKind) -> bool;
    /// Views `node` as `Self`, if the kind matches.
    fn cast(node: SyntaxNode) -> Option<Self>;
    /// The underlying untyped node.
    fn syntax(&self) -> &SyntaxNode;

    /// The node's source text.
    fn text(&self) -> String {
        self.syntax().text().to_string()
    }
}

/// The first child node that can be viewed as `N`.
pub fn child<N: AstNode>(parent: &SyntaxNode) -> Option<N> {
    parent.children().find_map(N::cast)
}

/// All child nodes that can be viewed as `N`.
pub fn children<N: AstNode>(parent: &SyntaxNode) -> impl Iterator<Item = N> + use<N> {
    parent.children().filter_map(N::cast)
}

/// The first direct child token of the given kind.
pub fn token(parent: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    parent
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|it| it.kind() == kind)
}

/// Declares a typed node wrapper for a single syntax kind.
macro_rules! ast_node {
    ($(#[$meta:meta])* $name:ident, $kind:ident) => {
        $(#[$meta])*
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub struct $name(SyntaxNode);

        impl AstNode for $name {
            fn can_cast(kind: SyntaxKind) -> bool {
                kind == $kind
            }
            fn cast(node: SyntaxNode) -> Option<Self> {
                if node.kind() == $kind { Some($name(node)) } else { None }
            }
            fn syntax(&self) -> &SyntaxNode {
                &self.0
            }
        }
    };
}

/// Declares an enum over several typed node wrappers.
macro_rules! ast_enum {
    ($(#[$meta:meta])* $name:ident { $($variant:ident($ty:ident)),* $(,)? }) => {
        $(#[$meta])*
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub enum $name {
            $(
                /// See the wrapped type.
                $variant($ty)
            ),*
        }

        impl AstNode for $name {
            fn can_cast(kind: SyntaxKind) -> bool {
                $(<$ty as AstNode>::can_cast(kind))||*
            }
            fn cast(node: SyntaxNode) -> Option<Self> {
                $(
                    if <$ty as AstNode>::can_cast(node.kind()) {
                        return <$ty as AstNode>::cast(node).map($name::$variant);
                    }
                )*
                None
            }
            fn syntax(&self) -> &SyntaxNode {
                match self {
                    $($name::$variant(it) => it.syntax()),*
                }
            }
        }
    };
}

// ---- Nodes -----------------------------------------------------------------

ast_node!(
    /// A whole file.
    SourceFile,
    SOURCE_FILE
);
ast_node!(
    /// `import Lean.Data.HashMap`
    Import,
    IMPORT
);
ast_node!(
    /// `open Foo Bar in …`
    Open,
    OPEN_CMD
);
ast_node!(
    /// `namespace Demo`
    Namespace,
    NAMESPACE
);
ast_node!(
    /// `section Foo`
    Section,
    SECTION
);
ast_node!(
    /// `end Demo`
    End,
    END_CMD
);
ast_node!(
    /// `variable {α : Type u}`
    Variable,
    VARIABLE_CMD
);
ast_node!(
    /// `universe u v`
    Universe,
    UNIVERSE_CMD
);
ast_node!(
    /// `set_option trace.foo true`
    SetOption,
    SET_OPTION_CMD
);
ast_node!(
    /// `attribute [simp] foo`
    AttributeCmd,
    ATTRIBUTE_CMD
);
ast_node!(
    /// `mutual … end`
    Mutual,
    MUTUAL_BLOCK
);
ast_node!(
    /// `#check`, `#eval`, …
    HashCmd,
    HASH_CMD
);
ast_node!(
    /// A `/-! … -/` module docstring.
    ModuleDoc,
    MODULE_DOC
);

ast_node!(
    /// `def f … := …`
    Def,
    DEF
);
ast_node!(
    /// `theorem t … := …` (also `lemma`)
    Theorem,
    THEOREM
);
ast_node!(
    /// `abbrev A := …`
    Abbrev,
    ABBREV
);
ast_node!(
    /// `example : T := …`
    Example,
    EXAMPLE
);
ast_node!(
    /// `instance : C X where …`
    Instance,
    INSTANCE
);
ast_node!(
    /// `axiom a : T`
    Axiom,
    AXIOM
);
ast_node!(
    /// `opaque o : T`
    Opaque,
    OPAQUE_DECL
);
ast_node!(
    /// `structure S where …`
    Structure,
    STRUCTURE
);
ast_node!(
    /// `class C where …`
    Class,
    CLASS_DECL
);
ast_node!(
    /// `inductive I where | …`
    Inductive,
    INDUCTIVE
);

ast_node!(
    /// `notation … => …`
    NotationCmd,
    NOTATION_CMD
);
ast_node!(
    /// `infixl:65 " ⊕ " => Sum`
    MixfixCmd,
    MIXFIX_CMD
);
ast_node!(
    /// `syntax … : term`
    SyntaxCmd,
    SYNTAX_CMD
);
ast_node!(
    /// `macro_rules | … => …`
    MacroRulesCmd,
    MACRO_RULES_CMD
);
ast_node!(
    /// `macro … => …`
    MacroCmd,
    MACRO_CMD
);
ast_node!(
    /// `elab … => …`
    ElabCmd,
    ELAB_CMD
);
ast_node!(
    /// `declare_syntax_cat foo`
    DeclareSyntaxCat,
    DECLARE_SYNTAX_CAT_CMD
);
ast_node!(
    /// A command the parser recognised but did not model.
    UnknownCmd,
    UNKNOWN_CMD
);
ast_node!(
    /// Tokens that could not be parsed.
    Error,
    ERROR
);

ast_node!(
    /// The leading docstring, attributes and modifiers of a declaration.
    DeclModifiers,
    DECL_MODIFIERS
);
ast_node!(
    /// `@[simp, norm_cast]`
    AttrList,
    ATTR_LIST
);
ast_node!(
    /// One attribute inside `@[…]`.
    Attr,
    ATTR
);
ast_node!(
    /// A declaration's name, with optional universe binders.
    DeclId,
    DECL_ID
);
ast_node!(
    /// A declaration's binders and result type.
    DeclSig,
    DECL_SIG
);
ast_node!(
    /// `: T`
    TypeSpec,
    TYPE_SPEC
);
ast_node!(
    /// `:= value`, or a `where` block of fields.
    DeclBody,
    DECL_BODY
);
ast_node!(
    /// Pattern-matching equations used as a declaration body.
    DeclEqns,
    DECL_EQNS
);
ast_node!(
    /// `where` auxiliary declarations.
    WhereClause,
    WHERE_CLAUSE
);
ast_node!(
    /// `extends A, B`
    ExtendsClause,
    EXTENDS_CLAUSE
);
ast_node!(
    /// `deriving Repr, BEq`
    DerivingClause,
    DERIVING_CLAUSE
);
ast_node!(
    /// The constructors of an inductive type.
    CtorList,
    CTOR_LIST
);
ast_node!(
    /// One inductive constructor.
    Ctor,
    CTOR
);
ast_node!(
    /// The fields of a structure or class.
    StructFieldList,
    STRUCT_FIELD_LIST
);
ast_node!(
    /// One structure field.
    StructField,
    STRUCT_FIELD
);

ast_node!(
    /// A group of binders.
    Binders,
    BINDERS
);
ast_node!(
    /// A bare `x`.
    SimpleBinder,
    SIMPLE_BINDER
);
ast_node!(
    /// `(x : T)`
    ParenBinder,
    PAREN_BINDER
);
ast_node!(
    /// `{x : T}`
    ImplicitBinder,
    IMPLICIT_BINDER
);
ast_node!(
    /// `⦃x : T⦄`
    StrictImplicitBinder,
    STRICT_IMPLICIT_BINDER
);
ast_node!(
    /// `[Monad m]`
    InstBinder,
    INST_BINDER
);

ast_node!(
    /// An identifier used as a term.
    Ref,
    REF
);
ast_node!(
    /// `.mk`
    DotIdent,
    DOT_IDENT
);
ast_node!(
    /// `_`
    Hole,
    HOLE
);
ast_node!(
    /// `?x`
    SyntheticHole,
    SYNTHETIC_HOLE
);
ast_node!(
    /// `sorry`
    Sorry,
    SORRY_TERM
);
ast_node!(
    /// A numeric, string, character or name literal.
    Literal,
    LITERAL
);
ast_node!(
    /// `Type u`, `Prop`, `Sort 0`
    Sort,
    SORT
);
ast_node!(
    /// `(e)`
    ParenTerm,
    PAREN_TERM
);
ast_node!(
    /// `(a, b)`
    Tuple,
    TUPLE
);
ast_node!(
    /// `(e : T)`
    TypeAscription,
    TYPE_ASCRIPTION
);
ast_node!(
    /// Function application.
    App,
    APP
);
ast_node!(
    /// A binary operator application.
    InfixTerm,
    INFIX_TERM
);
ast_node!(
    /// A prefix operator application.
    PrefixTerm,
    PREFIX_TERM
);
ast_node!(
    /// A postfix operator application.
    PostfixTerm,
    POSTFIX_TERM
);
ast_node!(
    /// `A → B`
    ArrowTerm,
    ARROW_TERM
);
ast_node!(
    /// `(x : A) → B x`
    DepArrow,
    DEP_ARROW
);
ast_node!(
    /// `fun x => e`
    Fun,
    FUN
);
ast_node!(
    /// `fun | p => e | q => f`
    FunAlts,
    FUN_ALTS
);
ast_node!(
    /// `∀ x, p x` and friends.
    Quantifier,
    QUANTIFIER
);
ast_node!(
    /// `let x := e; body`
    LetTerm,
    LET_TERM
);
ast_node!(
    /// `have h : T := e; body`
    HaveTerm,
    HAVE_TERM
);
ast_node!(
    /// `show T from e`
    ShowTerm,
    SHOW_TERM
);
ast_node!(
    /// `suffices h : T from e`
    SufficesTerm,
    SUFFICES_TERM
);
ast_node!(
    /// `match e with | …`
    MatchTerm,
    MATCH_TERM
);
ast_node!(
    /// The alternatives of a `match`.
    MatchAlts,
    MATCH_ALTS
);
ast_node!(
    /// One `| pat => body` alternative.
    MatchAlt,
    MATCH_ALT
);
ast_node!(
    /// The patterns of one alternative.
    Patterns,
    PATTERNS
);
ast_node!(
    /// `if c then a else b`
    IfTerm,
    IF_TERM
);
ast_node!(
    /// `if let p := e then a else b`
    IfLet,
    IF_LET
);
ast_node!(
    /// `do …`
    DoTerm,
    DO_TERM
);
ast_node!(
    /// The statements of a `do` block.
    DoSeq,
    DO_SEQ
);
ast_node!(
    /// `by …`
    ByTerm,
    BY_TERM
);
ast_node!(
    /// `⟨a, b⟩`
    AnonCtor,
    ANON_CTOR
);
ast_node!(
    /// `{ x := 1 }`
    StructInst,
    STRUCT_INST
);
ast_node!(
    /// One `x := e` field of a structure instance.
    StructInstField,
    STRUCT_INST_FIELD
);
ast_node!(
    /// `[a, b]`
    ListLit,
    LIST_LIT
);
ast_node!(
    /// `{a, b}`
    SetLit,
    SET_LIT
);
ast_node!(
    /// `[0:10]`
    RangeLit,
    RANGE_LIT
);
ast_node!(
    /// `{ x : T // p x }`
    Subtype,
    SUBTYPE
);
ast_node!(
    /// `{ x | p x }`
    SetOf,
    SET_OF
);
ast_node!(
    /// `e.1`
    Proj,
    PROJ
);
ast_node!(
    /// `e.field`
    FieldAccess,
    FIELD_ACCESS
);
ast_node!(
    /// `e |>.f`
    PipeProj,
    PIPE_PROJ
);
ast_node!(
    /// `@f`
    AtTerm,
    AT_TERM
);
ast_node!(
    /// `·`
    CdotTerm,
    CDOT_TERM
);
ast_node!(
    /// `calc a = b := h …`
    CalcTerm,
    CALC_TERM
);
ast_node!(
    /// One step of a `calc` block.
    CalcStep,
    CALC_STEP
);
ast_node!(
    /// A syntax quotation.
    QuotedTerm,
    QUOTED_TERM
);
ast_node!(
    /// Universe arguments, `f.{u, v}`.
    UnivArgs,
    UNIV_ARGS
);

ast_node!(
    /// A `by` block's tactic sequence.
    TacticSeq,
    TACTIC_SEQ
);
ast_node!(
    /// A single tactic.
    Tactic,
    TACTIC
);
ast_node!(
    /// `· tac` — focus the first goal.
    TacticFocus,
    TACTIC_FOCUS
);
ast_node!(
    /// `(tac; tac)`
    TacticSeqBracketed,
    TACTIC_SEQ_BRACKETED
);
ast_node!(
    /// `first | tac | tac`
    TacticAlt,
    TACTIC_ALT
);
ast_node!(
    /// `tac <;> tac`
    TacticCombinator,
    TACTIC_COMBINATOR
);
ast_node!(
    /// A tactic's uninterpreted arguments.
    TacticArgs,
    TACTIC_ARGS
);

// ---- Enums -----------------------------------------------------------------

ast_enum!(
    /// Any top-level command.
    Command {
        ModuleDoc(ModuleDoc),
        Import(Import),
        Open(Open),
        Namespace(Namespace),
        Section(Section),
        End(End),
        Variable(Variable),
        Universe(Universe),
        SetOption(SetOption),
        Attribute(AttributeCmd),
        Mutual(Mutual),
        Hash(HashCmd),
        Def(Def),
        Theorem(Theorem),
        Abbrev(Abbrev),
        Example(Example),
        Instance(Instance),
        Axiom(Axiom),
        Opaque(Opaque),
        Structure(Structure),
        Class(Class),
        Inductive(Inductive),
        Notation(NotationCmd),
        Mixfix(MixfixCmd),
        Syntax(SyntaxCmd),
        MacroRules(MacroRulesCmd),
        Macro(MacroCmd),
        Elab(ElabCmd),
        DeclareSyntaxCat(DeclareSyntaxCat),
        Unknown(UnknownCmd),
        Error(Error),
    }
);

ast_enum!(
    /// A declaration that introduces a name.
    Decl {
        Def(Def),
        Theorem(Theorem),
        Abbrev(Abbrev),
        Instance(Instance),
        Axiom(Axiom),
        Opaque(Opaque),
        Structure(Structure),
        Class(Class),
        Inductive(Inductive),
        Example(Example),
    }
);

ast_enum!(
    /// Any term.
    Term {
        Ref(Ref),
        DotIdent(DotIdent),
        Hole(Hole),
        SyntheticHole(SyntheticHole),
        Sorry(Sorry),
        Literal(Literal),
        Sort(Sort),
        Paren(ParenTerm),
        Tuple(Tuple),
        TypeAscription(TypeAscription),
        App(App),
        Infix(InfixTerm),
        Prefix(PrefixTerm),
        Postfix(PostfixTerm),
        Arrow(ArrowTerm),
        DepArrow(DepArrow),
        Fun(Fun),
        FunAlts(FunAlts),
        Quantifier(Quantifier),
        Let(LetTerm),
        Have(HaveTerm),
        Show(ShowTerm),
        Suffices(SufficesTerm),
        Match(MatchTerm),
        If(IfTerm),
        IfLet(IfLet),
        Do(DoTerm),
        By(ByTerm),
        AnonCtor(AnonCtor),
        StructInst(StructInst),
        List(ListLit),
        Set(SetLit),
        Range(RangeLit),
        Subtype(Subtype),
        SetOf(SetOf),
        Proj(Proj),
        FieldAccess(FieldAccess),
        PipeProj(PipeProj),
        At(AtTerm),
        Cdot(CdotTerm),
        Calc(CalcTerm),
        Quoted(QuotedTerm),
    }
);

ast_enum!(
    /// Any binder.
    Binder {
        Simple(SimpleBinder),
        Paren(ParenBinder),
        Implicit(ImplicitBinder),
        StrictImplicit(StrictImplicitBinder),
        Inst(InstBinder),
        Pattern(AnonCtor),
    }
);

// ---- Accessors -------------------------------------------------------------

impl SourceFile {
    /// The file's top-level commands, in order.
    pub fn commands(&self) -> impl Iterator<Item = Command> + use<> {
        children(self.syntax())
    }

    /// Every declaration in the file, including ones nested inside
    /// `namespace`, `section` and `mutual` blocks.
    pub fn declarations(&self) -> impl Iterator<Item = Decl> + use<> {
        self.syntax().descendants().filter_map(Decl::cast)
    }
}

impl DeclId {
    /// The declared name.
    pub fn name(&self) -> Option<SyntaxToken> {
        token(self.syntax(), IDENT)
    }

    /// Explicit universe binders, `foo.{u, v}`.
    pub fn universe_params(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == IDENT)
            .skip(1)
    }
}

impl DeclSig {
    /// The declaration's binders.
    pub fn binders(&self) -> Option<Binders> {
        child(self.syntax())
    }

    /// The declared result type, if written.
    pub fn ty(&self) -> Option<Term> {
        child::<TypeSpec>(self.syntax()).and_then(|it| it.ty())
    }
}

impl TypeSpec {
    /// The type itself, without the leading `:`.
    pub fn ty(&self) -> Option<Term> {
        child(self.syntax())
    }
}

impl Binders {
    /// The individual binders.
    pub fn iter(&self) -> impl Iterator<Item = Binder> + use<> {
        children(self.syntax())
    }
}

impl Binder {
    /// The names this binder introduces. An instance binder may introduce none.
    pub fn names(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| matches!(t.kind(), IDENT | UNDERSCORE))
    }

    /// The binder's type annotation, if written.
    pub fn ty(&self) -> Option<Term> {
        match self {
            // `[Monad m]` has no `: T`; the whole contents are the type.
            Binder::Inst(it) => child::<TypeSpec>(it.syntax())
                .and_then(|t| t.ty())
                .or_else(|| child(it.syntax())),
            _ => child::<TypeSpec>(self.syntax()).and_then(|it| it.ty()),
        }
    }

    /// True for `{x : T}`, `⦃x : T⦄` and `[Inst]`, which Lean fills in.
    pub fn is_implicit(&self) -> bool {
        matches!(
            self,
            Binder::Implicit(_) | Binder::StrictImplicit(_) | Binder::Inst(_)
        )
    }
}

impl DeclModifiers {
    /// The `/-- … -/` docstring, if present.
    pub fn doc_comment(&self) -> Option<SyntaxToken> {
        token(self.syntax(), DOC_COMMENT)
    }

    /// The attributes in `@[…]`.
    pub fn attributes(&self) -> impl Iterator<Item = Attr> + use<> {
        child::<AttrList>(self.syntax())
            .into_iter()
            .flat_map(|list| children::<Attr>(list.syntax()).collect::<Vec<_>>())
    }

    /// `private`, `partial`, `noncomputable`, … in source order.
    pub fn keywords(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind().is_keyword())
    }

    /// True if the declaration is marked `private`.
    pub fn is_private(&self) -> bool {
        token(self.syntax(), KW_PRIVATE).is_some()
    }
}

impl DeclBody {
    /// The defining term, for a `:= value` body.
    pub fn value(&self) -> Option<Term> {
        child(self.syntax())
    }

    /// The fields, for a `where` body.
    pub fn fields(&self) -> impl Iterator<Item = StructInstField> + use<> {
        child::<StructFieldList>(self.syntax())
            .into_iter()
            .flat_map(|list| children::<StructInstField>(list.syntax()).collect::<Vec<_>>())
    }
}

/// The parts every named declaration has.
///
/// Implemented for `def`, `theorem`, `structure` and the rest, so tooling can
/// walk declarations without matching on each kind.
pub trait HasDecl: AstNode {
    /// The declaration's name.
    fn name(&self) -> Option<SyntaxToken> {
        child::<DeclId>(self.syntax()).and_then(|it| it.name())
    }

    /// The docstring, attributes and modifiers.
    fn modifiers(&self) -> Option<DeclModifiers> {
        child(self.syntax())
    }

    /// The `/-- … -/` docstring, if present.
    fn doc_comment(&self) -> Option<SyntaxToken> {
        self.modifiers().and_then(|m| m.doc_comment())
    }

    /// The attributes in `@[…]`.
    fn attributes(&self) -> Vec<Attr> {
        self.modifiers()
            .map(|m| m.attributes().collect())
            .unwrap_or_default()
    }

    /// The declaration's binders.
    fn binders(&self) -> Option<Binders> {
        child::<DeclSig>(self.syntax())
            .and_then(|sig| sig.binders())
            .or_else(|| child(self.syntax()))
    }

    /// The declared type, if written.
    fn ty(&self) -> Option<Term> {
        child::<DeclSig>(self.syntax())
            .and_then(|sig| sig.ty())
            .or_else(|| child::<TypeSpec>(self.syntax()).and_then(|it| it.ty()))
    }

    /// The `:=` or `where` body.
    fn body(&self) -> Option<DeclBody> {
        child(self.syntax())
    }

    /// The defining term, when the body is `:= value`.
    fn value(&self) -> Option<Term> {
        self.body().and_then(|b| b.value())
    }

    /// `deriving Repr, BEq`
    fn deriving(&self) -> Option<DerivingClause> {
        child(self.syntax())
    }
}

impl HasDecl for Def {}
impl HasDecl for Theorem {}
impl HasDecl for Abbrev {}
impl HasDecl for Example {}
impl HasDecl for Instance {}
impl HasDecl for Axiom {}
impl HasDecl for Opaque {}
impl HasDecl for Structure {}
impl HasDecl for Class {}
impl HasDecl for Inductive {}

impl Decl {
    /// The declaration's name, if it has one. `example` never does.
    pub fn name(&self) -> Option<SyntaxToken> {
        child::<DeclId>(self.syntax()).and_then(|it| it.name())
    }

    /// The docstring, if present.
    pub fn doc_comment(&self) -> Option<SyntaxToken> {
        child::<DeclModifiers>(self.syntax()).and_then(|m| m.doc_comment())
    }

    /// The declared type, if written.
    pub fn ty(&self) -> Option<Term> {
        child::<DeclSig>(self.syntax()).and_then(|sig| sig.ty())
    }
}

impl Inductive {
    /// The type's constructors.
    pub fn ctors(&self) -> impl Iterator<Item = Ctor> + use<> {
        child::<CtorList>(self.syntax())
            .into_iter()
            .flat_map(|list| children::<Ctor>(list.syntax()).collect::<Vec<_>>())
    }
}

impl Ctor {
    /// The constructor's name.
    pub fn name(&self) -> Option<SyntaxToken> {
        token(self.syntax(), IDENT)
    }

    /// The constructor's arguments.
    pub fn binders(&self) -> Option<Binders> {
        child(self.syntax())
    }
}

impl Structure {
    /// The structure's fields.
    pub fn fields(&self) -> impl Iterator<Item = StructField> + use<> {
        child::<StructFieldList>(self.syntax())
            .into_iter()
            .flat_map(|list| children::<StructField>(list.syntax()).collect::<Vec<_>>())
    }

    /// `extends A, B`
    pub fn extends(&self) -> Option<ExtendsClause> {
        child(self.syntax())
    }
}

impl Class {
    /// The class's fields.
    pub fn fields(&self) -> impl Iterator<Item = StructField> + use<> {
        child::<StructFieldList>(self.syntax())
            .into_iter()
            .flat_map(|list| children::<StructField>(list.syntax()).collect::<Vec<_>>())
    }
}

impl StructField {
    /// The field's name.
    pub fn name(&self) -> Option<SyntaxToken> {
        self.syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == IDENT)
    }

    /// The field's type.
    pub fn ty(&self) -> Option<Term> {
        self.syntax()
            .descendants()
            .find_map(TypeSpec::cast)
            .and_then(|it| it.ty())
    }

    /// The field's docstring, if present.
    pub fn doc_comment(&self) -> Option<SyntaxToken> {
        token(self.syntax(), DOC_COMMENT)
    }
}

impl Import {
    /// The imported module names.
    pub fn modules(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == IDENT)
    }
}

impl Namespace {
    /// The namespace's name.
    pub fn name(&self) -> Option<SyntaxToken> {
        token(self.syntax(), IDENT)
    }
}

impl App {
    /// The applied function.
    pub fn function(&self) -> Option<Term> {
        child(self.syntax())
    }

    /// The arguments, in order.
    pub fn args(&self) -> impl Iterator<Item = Term> + use<> {
        children::<Term>(self.syntax()).skip(1)
    }
}

impl InfixTerm {
    /// The left operand.
    pub fn lhs(&self) -> Option<Term> {
        children(self.syntax()).next()
    }

    /// The right operand.
    pub fn rhs(&self) -> Option<Term> {
        children(self.syntax()).nth(1)
    }

    /// The operator token.
    pub fn op(&self) -> Option<SyntaxToken> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind().is_symbol())
    }
}

impl ArrowTerm {
    /// The domain.
    pub fn domain(&self) -> Option<Term> {
        children(self.syntax()).next()
    }

    /// The codomain.
    pub fn codomain(&self) -> Option<Term> {
        children(self.syntax()).nth(1)
    }
}

impl Fun {
    /// The lambda's binders.
    pub fn binders(&self) -> Option<Binders> {
        child(self.syntax())
    }

    /// The lambda's body.
    pub fn body(&self) -> Option<Term> {
        children(self.syntax()).last()
    }
}

impl Quantifier {
    /// `∀`, `∃`, `Σ` or `Π`.
    pub fn quantifier(&self) -> Option<SyntaxToken> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .next()
    }

    /// The bound variables.
    pub fn binders(&self) -> Option<Binders> {
        child(self.syntax())
    }

    /// The body.
    pub fn body(&self) -> Option<Term> {
        children(self.syntax()).last()
    }
}

impl MatchTerm {
    /// The scrutinees.
    pub fn discriminants(&self) -> impl Iterator<Item = Term> + use<> {
        self.syntax()
            .children()
            .filter(|n| n.kind() == MATCH_DISCRS)
            .filter_map(|n| n.children().find_map(Term::cast))
    }

    /// The alternatives.
    pub fn alts(&self) -> impl Iterator<Item = MatchAlt> + use<> {
        child::<MatchAlts>(self.syntax())
            .into_iter()
            .flat_map(|alts| children::<MatchAlt>(alts.syntax()).collect::<Vec<_>>())
    }
}

impl MatchAlt {
    /// The patterns this alternative matches.
    pub fn patterns(&self) -> impl Iterator<Item = Term> + use<> {
        child::<Patterns>(self.syntax())
            .into_iter()
            .flat_map(|p| children::<Term>(p.syntax()).collect::<Vec<_>>())
    }

    /// The alternative's right-hand side, when it is a term.
    pub fn body(&self) -> Option<Term> {
        children(self.syntax()).last()
    }

    /// The alternative's right-hand side, when it is a tactic sequence.
    pub fn tactics(&self) -> Option<TacticSeq> {
        child(self.syntax())
    }
}

impl ByTerm {
    /// The tactic sequence.
    pub fn tactics(&self) -> Option<TacticSeq> {
        child(self.syntax())
    }
}

impl TacticSeq {
    /// The tactics in the block, in order.
    pub fn tactics(&self) -> impl Iterator<Item = SyntaxNode> + use<> {
        self.syntax().children().filter(|n| {
            matches!(
                n.kind(),
                TACTIC | TACTIC_FOCUS | TACTIC_SEQ_BRACKETED | TACTIC_ALT | TACTIC_COMBINATOR
            )
        })
    }
}

impl Tactic {
    /// The tactic's leading token, which names it.
    pub fn name(&self) -> Option<SyntaxToken> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .next()
    }

    /// The tactic's uninterpreted arguments.
    pub fn args(&self) -> Option<TacticArgs> {
        child(self.syntax())
    }

    /// Structured alternatives, as in `induction n with | zero => …`.
    pub fn alts(&self) -> impl Iterator<Item = MatchAlt> + use<> {
        child::<MatchAlts>(self.syntax())
            .into_iter()
            .flat_map(|alts| children::<MatchAlt>(alts.syntax()).collect::<Vec<_>>())
    }
}

impl Literal {
    /// The literal token.
    pub fn token(&self) -> Option<SyntaxToken> {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .next()
    }
}

impl Ref {
    /// The referenced name, which may be dotted (`Nat.succ`).
    pub fn name(&self) -> Option<SyntaxToken> {
        token(self.syntax(), IDENT)
    }
}
