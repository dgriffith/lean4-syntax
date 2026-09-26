//! The token and node kinds that make up a Lean 4 syntax tree.
//!
//! Every kind lives in one flat `u16` enum because that is what rowan stores in
//! its green nodes. The [`kinds!`] macro keeps the enum, the keyword table and
//! the symbol table in sync: adding a keyword in one place is enough.

/// Declares every [`SyntaxKind`] variant plus the lookup tables the lexer needs.
macro_rules! kinds {
    (
        trivia   { $($trivia:ident),* $(,)? }
        literals { $($lit:ident),* $(,)? }
        keywords { $($kw:ident = $kw_text:literal),* $(,)? }
        symbols  { $($sym:ident = $sym_text:literal),* $(,)? }
        nodes    { $($node:ident),* $(,)? }
    ) => {
        /// A token or node kind. Discriminants are not stable across versions.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(u16)]
        #[allow(non_camel_case_types)]
        pub enum SyntaxKind {
            $($trivia,)*
            IDENT,
            $($lit,)*
            $($kw,)*
            $($sym,)*
            /// A token the lexer could not classify.
            LEX_ERROR,
            $($node,)*
            /// Sentinel; always the last variant.
            __LAST,
        }

        impl SyntaxKind {
            /// Converts back from rowan's untyped representation.
            pub fn from_u16(raw: u16) -> Option<Self> {
                if raw < Self::__LAST as u16 {
                    // Safe: `repr(u16)`, contiguous discriminants, bound checked.
                    Some(unsafe { std::mem::transmute::<u16, Self>(raw) })
                } else {
                    None
                }
            }

            /// True for whitespace and comments, which the parser skips but the
            /// tree still stores.
            pub fn is_trivia(self) -> bool {
                matches!(self, $(Self::$trivia)|*)
            }

            /// True for reserved words such as `def` or `fun`.
            pub fn is_keyword(self) -> bool {
                matches!(self, $(Self::$kw)|*)
            }

            /// True for a bracket or delimiter.
            ///
            /// Delimiters never take a modifier suffix: in `‖x‖₊` the `₊`
            /// modifies the whole bracketed term, so absorbing it into the
            /// closing `‖` would leave the pair unclosed.
            pub fn is_delimiter(self) -> bool {
                matches!(
                    self,
                    Self::L_PAREN
                        | Self::R_PAREN
                        | Self::L_BRACE
                        | Self::R_BRACE
                        | Self::L_BRACKET
                        | Self::R_BRACKET
                        | Self::L_ANGLE_ANON
                        | Self::R_ANGLE_ANON
                        | Self::L_STRICT_IMPLICIT
                        | Self::R_STRICT_IMPLICIT
                        | Self::L_DOUBLE_BRACKET
                        | Self::R_DOUBLE_BRACKET
                        | Self::L_ANON_HAVE
                        | Self::R_ANON_HAVE
                        | Self::NORM_BAR
                        | Self::L_FLOOR
                        | Self::R_FLOOR
                        | Self::L_CEIL
                        | Self::R_CEIL
                        | Self::L_ANGLE_INNER
                        | Self::R_ANGLE_INNER
                        | Self::L_LIE
                        | Self::R_LIE
                )
            }

            /// True for punctuation and operator tokens.
            pub fn is_symbol(self) -> bool {
                matches!(self, $(Self::$sym)|*)
            }

            /// True for nodes (interior tree positions) rather than tokens.
            pub fn is_node(self) -> bool {
                matches!(self, $(Self::$node)|*)
            }

            /// The source text of a keyword or symbol kind, if it is fixed.
            pub fn static_text(self) -> Option<&'static str> {
                match self {
                    $(Self::$kw => Some($kw_text),)*
                    $(Self::$sym => Some($sym_text),)*
                    _ => None,
                }
            }
        }

        /// Reserved words, paired with the kind the lexer should produce.
        pub const KEYWORDS: &[(&str, SyntaxKind)] = &[
            $(($kw_text, SyntaxKind::$kw),)*
        ];

        /// Punctuation and operators. The lexer sorts these longest-first so
        /// that `:=` wins over `:` and `<;>` over `<`.
        pub const SYMBOLS: &[(&str, SyntaxKind)] = &[
            $(($sym_text, SyntaxKind::$sym),)*
        ];
    };
}

kinds! {
    trivia {
        WHITESPACE,
        LINE_COMMENT,
        BLOCK_COMMENT,
    }

    literals {
        // A notation character the parser has no specific rule for. Usable as
        // an atom, or as an infix operator at an assumed precedence.
        SYMBOL,
        // A run of superscript or subscript modifier letters, which Lean
        // notation uses exclusively as postfix: `sᶜ`, `Xᵒᵖ`, `‖x‖₊`.
        MODIFIER,
        NUMBER,
        SCIENTIFIC,
        STRING,
        RAW_STRING,
        CHAR,
        NAME_LIT,      // `Nat.succ  — a quoted name
        // Doc comments are significant: they attach to the declaration that
        // follows, so the parser consumes them rather than skipping them.
        DOC_COMMENT,   // /-- ... -/
        MOD_DOC_COMMENT, // /-! ... -/
    }

    keywords {
        // Commands and declaration heads.
        KW_IMPORT = "import",
        // Lean's module system: `module`, `public import X`, `public section`,
        // `meta import X`. Present in 95% of current mathlib files.
        KW_MODULE = "module",
        KW_PUBLIC = "public",
        KW_META = "meta",
        KW_PRELUDE = "prelude",
        KW_OPEN = "open",
        KW_EXPORT = "export",
        KW_INCLUDE = "include",
        KW_OMIT = "omit",
        KW_NAMESPACE = "namespace",
        KW_SECTION = "section",
        KW_END = "end",
        KW_VARIABLE = "variable",
        KW_VARIABLES = "variables",
        KW_UNIVERSE = "universe",
        KW_SET_OPTION = "set_option",
        KW_ATTRIBUTE = "attribute",
        KW_DEF = "def",
        KW_THEOREM = "theorem",
        KW_LEMMA = "lemma",
        KW_ABBREV = "abbrev",
        KW_EXAMPLE = "example",
        KW_INSTANCE = "instance",
        KW_AXIOM = "axiom",
        KW_OPAQUE = "opaque",
        KW_STRUCTURE = "structure",
        KW_CLASS = "class",
        KW_INDUCTIVE = "inductive",
        KW_DERIVING = "deriving",
        KW_EXTENDS = "extends",
        KW_MUTUAL = "mutual",
        KW_WHERE = "where",
        KW_NOTATION = "notation",
        KW_INFIX = "infix",
        KW_INFIXL = "infixl",
        KW_INFIXR = "infixr",
        KW_PREFIX = "prefix",
        KW_POSTFIX = "postfix",
        KW_MACRO = "macro",
        KW_MACRO_RULES = "macro_rules",
        KW_SYNTAX = "syntax",
        KW_ELAB = "elab",
        KW_ELAB_RULES = "elab_rules",
        KW_DECLARE_SYNTAX_CAT = "declare_syntax_cat",
        KW_INITIALIZE = "initialize",
        KW_BUILTIN_INITIALIZE = "builtin_initialize",
        // Declaration modifiers.
        KW_PRIVATE = "private",
        KW_PROTECTED = "protected",
        KW_PARTIAL = "partial",
        KW_UNSAFE = "unsafe",
        KW_NONCOMPUTABLE = "noncomputable",
        KW_NONREC = "nonrec",
        KW_LOCAL = "local",
        KW_SCOPED = "scoped",
        // Terms.
        KW_FUN = "fun",
        KW_LET = "let",
        KW_REC = "rec",
        KW_HAVE = "have",
        KW_SHOW = "show",
        KW_FROM = "from",
        KW_SUFFICES = "suffices",
        KW_MATCH = "match",
        KW_NOMATCH = "nomatch",
        KW_WITH = "with",
        KW_DO = "do",
        KW_IF = "if",
        KW_THEN = "then",
        KW_ELSE = "else",
        KW_BY = "by",
        KW_AT = "at",
        KW_IN = "in",
        KW_CALC = "calc",
        KW_SORRY = "sorry",
        KW_FORALL_KW = "forall",
        KW_EXISTS_KW = "exists",
        KW_TYPE = "Type",
        KW_PROP = "Prop",
        KW_SORT = "Sort",
        KW_RETURN = "return",
        KW_FOR = "for",
        KW_WHILE = "while",
        KW_REPEAT = "repeat",
        KW_UNLESS = "unless",
        KW_TRY = "try",
        KW_CATCH = "catch",
        KW_FINALLY = "finally",
        KW_MUT = "mut",
        KW_BREAK = "break",
        KW_CONTINUE = "continue",
        KW_FIRST = "first",
        // Lean keeps one global token table, so words introduced by tactic
        // syntax are reserved everywhere rather than being identifiers that
        // happen to appear in tactic position. Without this, `induction xs
        // using List.rec` reads `using` as an argument of `xs`.
        KW_ONLY = "only",
        KW_USING = "using",
        KW_GENERALIZING = "generalizing",
    }

    // NOTE: order here is irrelevant; the lexer sorts by length descending.
    symbols {
        // Brackets.
        L_PAREN = "(",
        R_PAREN = ")",
        L_BRACE = "{",
        R_BRACE = "}",
        L_BRACKET = "[",
        R_BRACKET = "]",
        L_ANGLE_ANON = "\u{27e8}",      // ⟨
        R_ANGLE_ANON = "\u{27e9}",      // ⟩
        L_STRICT_IMPLICIT = "\u{2983}", // ⦃
        R_STRICT_IMPLICIT = "\u{2984}", // ⦄
        L_DOUBLE_BRACKET = "\u{27e6}",  // ⟦
        R_DOUBLE_BRACKET = "\u{27e7}",  // ⟧
        L_ANON_HAVE = "\u{2039}",       // ‹
        R_ANON_HAVE = "\u{203a}",       // ›
        // Punctuation.
        COMMA = ",",
        SEMICOLON = ";",
        COLON = ":",
        COLON_EQ = ":=",
        DOUBLE_COLON = "::",
        DOT = ".",
        DOT_DOT = "..",
        ELLIPSIS = "...",
        AT = "@",
        UNDERSCORE = "_",
        HASH = "#",
        DOLLAR = "$",
        BACKSLASH = "\\",
        QUESTION = "?",
        BANG = "!",
        PIPE = "|",
        CDOT = "\u{00b7}",   // ·
        BULLET = "\u{2022}", // •
        // Arrows and binders.
        THIN_ARROW = "->",
        ARROW = "\u{2192}",       // →
        LEFT_ARROW_ASCII = "<-",
        LEFT_ARROW = "\u{2190}",  // ←
        MAPSTO = "\u{21a6}",      // ↦
        // Core Lean's coercion arrows, all prefix at maximal precedence.
        UP_ARROW = "\u{2191}",    // ↑
        COE_FUN = "\u{21d1}",     // ⇑
        COE_SORT = "\u{21a5}",    // ↥
        FAT_ARROW = "=>",
        IFF_ASCII = "<->",
        IFF = "\u{2194}",         // ↔
        FORALL = "\u{2200}",      // ∀
        EXISTS = "\u{2203}",      // ∃
        LAMBDA = "\u{03bb}",      // λ
        SIGMA = "\u{03a3}",       // Σ
        PI = "\u{03a0}",          // Π
        // Logic.
        AND = "\u{2227}",         // ∧
        OR = "\u{2228}",          // ∨
        NOT = "\u{00ac}",         // ¬
        AND_AND = "&&",
        OR_OR = "||",
        // Comparison.
        EQ = "=",
        EQ_EQ = "==",
        NE_ASCII = "!=",
        NE = "\u{2260}",          // ≠
        LT = "<",
        GT = ">",
        LE_ASCII = "<=",
        GE_ASCII = ">=",
        LE = "\u{2264}",          // ≤
        GE = "\u{2265}",          // ≥
        HEQ = "\u{2245}",         // ≅
        EQUIV = "\u{2243}",       // ≃
        // Arithmetic.
        PLUS = "+",
        MINUS = "-",
        STAR = "*",
        SLASH = "/",
        PERCENT = "%",
        CARET = "^",
        PLUS_PLUS = "++",
        TIMES = "\u{00d7}",       // ×
        OPLUS = "\u{2295}",       // ⊕
        COMPOSE = "\u{2218}",     // ∘
        INV = "\u{207b}\u{00b9}", // ⁻¹
        DVD = "\u{2223}",         // ∣
        // Sets and orders.
        MEM = "\u{2208}",         // ∈
        NOT_MEM = "\u{2209}",     // ∉
        SUBSET_EQ = "\u{2286}",   // ⊆
        SUBSET = "\u{2282}",      // ⊂
        UNION = "\u{222a}",       // ∪
        INTER = "\u{2229}",       // ∩
        SUP = "\u{2294}",         // ⊔
        INF = "\u{2293}",         // ⊓
        // Monadic / pipeline operators.
        BIND = ">>=",
        SEQ_RIGHT = ">>",
        MAP = "<$>",
        SEQ_AP = "<*>",
        PIPE_LEFT = "<|",
        PIPE_RIGHT = "|>",
        ALTERNATIVE = "<|>",
        SEQ_FOCUS = "<;>",
        PIPE_RIGHT_DOT = "|>.",
        // Misc.
        TURNSTILE = "\u{22a2}",   // ⊢
        TURNSTILE_ASCII = "|-",
        // Curated notation, ranked by frequency in mathlib. These need real
        // rules rather than the generic fallback: delimiters come in pairs,
        // big operators bind variables, and the operators below have
        // precedences that matter.
        NORM_BAR = "\u{2016}",        // ‖  (30830 uses)
        L_FLOOR = "\u{230a}",         // ⌊
        R_FLOOR = "\u{230b}",         // ⌋
        L_CEIL = "\u{2308}",          // ⌈
        R_CEIL = "\u{2309}",          // ⌉
        L_ANGLE_INNER = "\u{27ea}",   // ⟪
        R_ANGLE_INNER = "\u{27eb}",   // ⟫
        BIG_SUM = "\u{2211}",         // ∑
        BIG_PROD = "\u{220f}",        // ∏
        BIG_UNION = "\u{22c3}",       // ⋃
        BIG_INTER = "\u{22c2}",       // ⋂
        BIG_SUP = "\u{2a06}",         // ⨆
        BIG_INF = "\u{2a05}",         // ⨅
        BIG_OPLUS = "\u{2a01}",       // ⨁
        BIG_OTIMES = "\u{2a02}",      // ⨂
        INTEGRAL = "\u{222b}",        // ∫
        GG = "\u{226b}",              // ≫  (27345 uses)
        GGG = "\u{22d9}",             // ⋙
        LONG_ARROW = "\u{27f6}",      // ⟶  (24803 uses)
        FUNCTOR_ARROW = "\u{2964}",   // ⥤
        OTIMES = "\u{2297}",          // ⊗
        CONGR_MOD = "\u{2261}",       // ≡
        QUOTIENT = "\u{29f8}",        // ⧸
        // Constant-like notation. These are atoms, so they may appear as
        // application arguments (`IsOpen ⊤`), unlike a generic symbol, which is
        // read as an operator.
        TOP = "\u{22a4}",             // ⊤
        BOT = "\u{22a5}",             // ⊥
        EMPTY_SET = "\u{2205}",       // ∅
        INFINITY = "\u{221e}",        // ∞
        ONE_MORPH = "\u{1d7d9}",      // 𝟙
        ZERO_MORPH = "\u{1d7d8}",     // 𝟘
        IMAGE = "''",
        TILDE = "~",
        AMPERSAND = "&",
        L_LIE = "\u{2045}",           // ⁅
        R_LIE = "\u{2046}",           // ⁆
        SLASH_SLASH = "//",
        TICK = "'",
        BACKTICK = "`",
        DOUBLE_BACKTICK = "``",
    }

    nodes {
        // Root.
        SOURCE_FILE,
        // Commands.
        MODULE_DOC,
        MODULE_CMD,
        IMPORT,
        OPEN_CMD,
        EXPORT_CMD,
        INCLUDE_CMD,
        OMIT_CMD,
        OPEN_HIDING,
        OPEN_RENAMING,
        OPEN_ONLY,
        NAMESPACE,
        SECTION,
        END_CMD,
        VARIABLE_CMD,
        UNIVERSE_CMD,
        SET_OPTION_CMD,
        ATTRIBUTE_CMD,
        MUTUAL_BLOCK,
        HASH_CMD,
        UNKNOWN_CMD,
        // Declarations.
        DECL_MODIFIERS,
        ATTR_LIST,
        ATTR,
        DEF,
        THEOREM,
        ABBREV,
        EXAMPLE,
        INSTANCE,
        AXIOM,
        OPAQUE_DECL,
        STRUCTURE,
        CLASS_DECL,
        INDUCTIVE,
        DECL_ID,
        UNIV_BINDERS,
        DECL_SIG,
        TYPE_SPEC,
        DECL_BODY,
        DECL_EQNS,
        WHERE_CLAUSE,
        WHERE_DECLS,
        EXTENDS_CLAUSE,
        DERIVING_CLAUSE,
        CTOR_LIST,
        CTOR,
        STRUCT_FIELD_LIST,
        STRUCT_FIELD,
        // Notation commands (recorded, not applied to the grammar).
        NOTATION_BRACKET,
        SYMBOL_TERM,
        OPERATOR,
        NOTATION_CMD,
        MIXFIX_CMD,
        PRECEDENCE,
        SYNTAX_CMD,
        MACRO_RULES_CMD,
        MACRO_CMD,
        ELAB_CMD,
        DECLARE_SYNTAX_CAT_CMD,
        INITIALIZE_CMD,
        RAW_TOKENS,
        // Binders.
        BINDERS,
        SIMPLE_BINDER,
        PAREN_BINDER,
        IMPLICIT_BINDER,
        STRICT_IMPLICIT_BINDER,
        INST_BINDER,
        DEFAULT_VALUE,
        // Terms.
        REF,
        DOT_IDENT,
        HOLE,
        SYNTHETIC_HOLE,
        SORRY_TERM,
        LITERAL,
        SORT,
        PAREN_TERM,
        TUPLE,
        TYPE_ASCRIPTION,
        APP,
        INFIX_TERM,
        PREFIX_TERM,
        POSTFIX_TERM,
        ARROW_TERM,
        DEP_ARROW,
        FUN,
        FUN_ALTS,
        QUANTIFIER,
        LET_TERM,
        HAVE_TERM,
        SHOW_TERM,
        SUFFICES_TERM,
        MATCH_TERM,
        MATCH_DISCRS,
        MATCH_ALTS,
        MATCH_ALT,
        PATTERNS,
        IF_TERM,
        IF_LET,
        DO_TERM,
        BY_TERM,
        ANON_CTOR,
        STRUCT_INST,
        STRUCT_INST_SRC,
        STRUCT_INST_FIELD,
        LIST_LIT,
        ARRAY_LIT,
        SET_LIT,
        RANGE_LIT,
        UNIV_ARGS,
        SUBTYPE,
        SET_OF,
        PROJ,
        FIELD_ACCESS,
        PIPE_PROJ,
        AT_TERM,
        CDOT_TERM,
        CALC_TERM,
        CALC_STEP,
        NAME_TERM,
        NAMED_ARG,
        ANTIQUOTATION,
        QUOTED_TERM,
        MACRO_CALL,
        ARG_LIST,
        // Do-notation elements.
        DO_SEQ,
        DO_LET,
        DO_LET_ARROW,
        DO_BIND,
        DO_REASSIGN,
        DO_IF,
        DO_UNLESS,
        DO_FOR,
        DO_WHILE,
        DO_REPEAT,
        DO_TRY,
        DO_CATCH,
        DO_FINALLY,
        DO_RETURN,
        DO_BREAK,
        DO_CONTINUE,
        DO_EXPR,
        // Tactics.
        TACTIC_SEQ,
        TACTIC,
        TACTIC_FOCUS,
        TACTIC_SEQ_BRACKETED,
        TACTIC_ALT,
        TACTIC_ARGS,
        TACTIC_COMBINATOR,
        // Structured tactic shapes. There is deliberately one node per
        // *shape* rather than one per tactic name: the name token identifies
        // the tactic, while the shape says how to reach its parts.
        TACTIC_SIMP,
        TACTIC_REWRITE,
        TACTIC_TERM,
        TACTIC_TERM_LIST,
        TACTIC_INTRO,
        TACTIC_CASES,
        TACTIC_HAVE,
        TACTIC_CASE,
        TACTIC_CONV,
        TACTIC_SHOW,
        TACTIC_CALC,
        TACTIC_COMBINATOR_APP,
        // Parts shared by those shapes.
        LOCATION,
        SIMP_ARG_LIST,
        SIMP_ARG,
        RW_RULE_LIST,
        RW_RULE,
        TACTIC_CONFIG,
        TACTIC_TARGETS,
        USING_CLAUSE,
        WITH_CLAUSE,
        CASE_ARGS,
        // `rcases` / `rintro` / `obtain` patterns.
        RCASES_PAT,
        RCASES_TUPLE,
        RCASES_ALT,
        // Recovery.
        ERROR,
    }
}

/// rowan's language marker for Lean 4 syntax trees.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lean {}

impl rowan::Language for Lean {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        SyntaxKind::from_u16(raw.0).unwrap_or(SyntaxKind::ERROR)
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        rowan::SyntaxKind(kind as u16)
    }
}

/// A node in a parsed Lean file.
pub type SyntaxNode = rowan::SyntaxNode<Lean>;
/// A token in a parsed Lean file.
pub type SyntaxToken = rowan::SyntaxToken<Lean>;
/// Either a node or a token.
pub type SyntaxElement = rowan::SyntaxElement<Lean>;
