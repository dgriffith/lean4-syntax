//! Lowering the CST into the [`Module`] HIR.
//!
//! Every function here is total. Where a child is missing or a shape is not
//! modelled, the result is an `Opaque` node rather than a panic or a dropped
//! subtree — and if the shape *was* recognised and still could not be lowered,
//! a [`LoweringError`] records it. That separation is what makes coverage
//! measurable: `Opaque` without an error is a deliberate boundary, `Opaque` with
//! one is a gap.
//!
//! Lowering matches on [`SyntaxKind`] and reaches into the CST with the generic
//! helpers from [`crate::ast`], rather than going through the typed views for
//! every field. The typed layer is for consumers navigating a few parts of a
//! tree; lowering needs every part of every node, and giving it a named accessor
//! for each would double the size of that module to serve one caller.

use super::*;
use crate::ast::{self, AstNode};
use crate::kind::{SyntaxKind, SyntaxKind::*, SyntaxNode, SyntaxToken};

/// Lowers a parsed file.
///
/// The root should be the `SOURCE_FILE` node from [`crate::parse`]. A tree
/// containing syntax errors lowers fine; the unparsable regions become opaque.
pub fn lower(root: &SyntaxNode) -> Module {
    let mut ctx = Ctx {
        module: Module::default(),
    };
    for child in root.children() {
        if ast::Command::cast(child.clone()).is_some() {
            ctx.item(&child);
        }
    }
    ctx.module
}

struct Ctx {
    module: Module,
}

// ---- Generic CST helpers ---------------------------------------------------

/// The node's direct children that are terms.
fn term_children(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.children()
        .filter(|n| ast::Term::cast(n.clone()).is_some())
        .collect()
}

/// The text of the node's first direct token of the given kind.
fn tok_text(node: &SyntaxNode, kind: SyntaxKind) -> Option<String> {
    ast::token(node, kind).map(|t| t.text().to_string())
}

/// The node's first non-trivia direct token.
fn first_tok(node: &SyntaxNode) -> Option<SyntaxToken> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| !t.kind().is_trivia())
}

/// All direct tokens of the given kinds, in order.
fn toks(node: &SyntaxNode, kinds: &[SyntaxKind]) -> Vec<String> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .filter(|t| kinds.contains(&t.kind()))
        .map(|t| t.text().to_string())
        .collect()
}

/// The first descendant node of the given kind.
fn child_of(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxNode> {
    node.children().find(|n| n.kind() == kind)
}

/// All direct children of the given kind.
fn children_of(node: &SyntaxNode, kind: SyntaxKind) -> Vec<SyntaxNode> {
    node.children().filter(|n| n.kind() == kind).collect()
}

/// The first term child appearing after a token of the given kind.
fn term_after(node: &SyntaxNode, after: SyntaxKind) -> Option<SyntaxNode> {
    let mut seen = false;
    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(t) if t.kind() == after => seen = true,
            rowan::NodeOrToken::Node(n) if seen && ast::Term::cast(n.clone()).is_some() => {
                return Some(n);
            }
            _ => {}
        }
    }
    None
}

impl Ctx {
    fn ptr(node: &SyntaxNode) -> SyntaxNodePtr<Lean> {
        SyntaxNodePtr::new(node)
    }

    /// Records where a node came from.
    fn link(&mut self, id: HirId, node: &SyntaxNode) {
        self.module.source.insert(id, Self::ptr(node));
    }

    /// An opaque term for syntax deliberately not modelled.
    fn unmodeled(&mut self, node: &SyntaxNode) -> TermId {
        let id = self.module.alloc_term(Term::Opaque(Self::ptr(node)));
        self.link(HirId::Term(id), node);
        id
    }

    /// An opaque term for syntax that should have lowered but did not.
    fn gap(&mut self, node: &SyntaxNode, message: impl Into<String>) -> TermId {
        self.module.errors.push(LoweringError {
            message: message.into(),
            node: Self::ptr(node),
        });
        self.unmodeled(node)
    }

    /// Lowers a term, or records a gap if the node is absent.
    fn term_or_gap(&mut self, node: Option<SyntaxNode>, parent: &SyntaxNode, what: &str) -> TermId {
        match node {
            Some(n) => self.term(&n),
            None => self.gap(parent, format!("missing {what}")),
        }
    }

    fn opt_term(&mut self, node: Option<SyntaxNode>) -> Option<TermId> {
        node.map(|n| self.term(&n))
    }

    // ---- Terms -------------------------------------------------------------

    fn term(&mut self, node: &SyntaxNode) -> TermId {
        // Lowering recurses with the shape of the term, and a machine-generated
        // proof can nest far deeper than a human-written one. Growing the stack
        // keeps deep input from aborting the process — a stack overflow is not
        // catchable, so it would be worse than a panic. The parser is protected
        // the same way, by chumsky's own use of `stacker`.
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || self.term_inner(node))
    }

    fn term_inner(&mut self, node: &SyntaxNode) -> TermId {
        let kids = term_children(node);
        let term = match node.kind() {
            REF => Term::Ref(Name(tok_text(node, IDENT).unwrap_or_default())),
            DOT_IDENT => Term::DotIdent(Name(tok_text(node, IDENT).unwrap_or_default())),
            HOLE => Term::Hole,
            SYNTHETIC_HOLE => Term::SyntheticHole(tok_text(node, IDENT).map(Name)),
            SORRY_TERM => Term::Sorry,
            CDOT_TERM => Term::Placeholder,
            SYMBOL_TERM => Term::Symbol(Name(
                first_tok(node)
                    .map(|t| t.text().to_string())
                    .unwrap_or_default(),
            )),
            ANTIQUOTATION => Term::Antiquotation(tok_text(node, IDENT).map(Name)),
            LITERAL => return self.literal(node),
            SORT => {
                let kind = match first_tok(node).map(|t| t.kind()) {
                    Some(KW_PROP) => SortKind::Prop,
                    Some(KW_SORT) => SortKind::Sort,
                    _ => SortKind::Type,
                };
                // `Type u` and `Type*` both put the level in a bare token.
                let level = node
                    .children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .filter(|t| matches!(t.kind(), IDENT | NUMBER | UNDERSCORE | STAR))
                    .map(|t| Term::Ref(Name(t.text().to_string())))
                    .next()
                    .map(|t| self.module.alloc_term(t));
                Term::Sort { kind, level }
            }
            APP => return self.app(node),
            INFIX_TERM => return self.infix(node),
            PREFIX_TERM => {
                let op = first_tok(node)
                    .map(|t| t.text().to_string())
                    .unwrap_or_default();
                let operand = self.term_or_gap(kids.first().cloned(), node, "prefix operand");
                Term::Prefix {
                    op: Name(op),
                    operand,
                }
            }
            POSTFIX_TERM => {
                let operand = self.term_or_gap(kids.first().cloned(), node, "postfix operand");
                let op = node
                    .children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .filter(|t| !t.kind().is_trivia())
                    .last()
                    .map(|t| t.text().to_string())
                    .unwrap_or_default();
                Term::Postfix {
                    op: Name(op),
                    operand,
                }
            }
            ARROW_TERM => {
                let domain = self.term_or_gap(kids.first().cloned(), node, "arrow domain");
                let codomain = self.term_or_gap(kids.get(1).cloned(), node, "arrow codomain");
                Term::Arrow { domain, codomain }
            }
            DEP_ARROW => {
                let binders = self.binders_in(node);
                let codomain = self.term_or_gap(kids.last().cloned(), node, "arrow codomain");
                Term::DepArrow { binders, codomain }
            }
            FUN => {
                let binders = self.binders_in(node);
                let body = self.term_or_gap(kids.last().cloned(), node, "lambda body");
                Term::Fun { binders, body }
            }
            FUN_ALTS => Term::FunAlts {
                arms: self.arms_in(node),
            },
            QUANTIFIER => return self.quantifier(node),
            LET_TERM => return self.let_term(node),
            HAVE_TERM => return self.have_term(node),
            SHOW_TERM => {
                let ty = self.term_or_gap(kids.first().cloned(), node, "shown type");
                let proof = self.opt_term(kids.get(1).cloned());
                Term::Show { ty, proof }
            }
            SUFFICES_TERM => {
                let pat = self.opt_pat_in(node);
                let ty = self.type_spec(node);
                let proof = self.opt_term(kids.last().cloned());
                Term::Suffices { pat, ty, proof }
            }
            MATCH_TERM => return self.match_term(node),
            IF_TERM | IF_LET => {
                let cond = self.term_or_gap(kids.first().cloned(), node, "condition");
                let then_branch = self.term_or_gap(term_after(node, KW_THEN), node, "then branch");
                let else_branch = self.term_or_gap(term_after(node, KW_ELSE), node, "else branch");
                Term::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
            DO_TERM => Term::Do(self.do_seq(node)),
            BY_TERM => {
                let seq = child_of(node, TACTIC_SEQ);
                let tactic = match seq {
                    Some(s) => self.tactic_seq(&s),
                    None => {
                        let ptr = Self::ptr(node);
                        self.module.errors.push(LoweringError {
                            message: "`by` with no tactic block".into(),
                            node: ptr,
                        });
                        self.module.alloc_tactic(Tactic::Opaque {
                            name: None,
                            node: ptr,
                        })
                    }
                };
                Term::By(tactic)
            }
            TUPLE => Term::Tuple(self.terms_in(node)),
            ANON_CTOR => Term::AnonCtor(self.terms_in(node)),
            LIST_LIT => Term::ListLit(self.terms_in(node)),
            ARRAY_LIT => Term::ArrayLit(self.terms_in(node)),
            SET_LIT | RANGE_LIT => Term::SetLit(self.terms_in(node)),
            NOTATION_BRACKET => Term::Bracketed {
                open: Name(
                    first_tok(node)
                        .map(|t| t.text().to_string())
                        .unwrap_or_default(),
                ),
                parts: self.terms_in(node),
            },
            STRUCT_INST => return self.struct_inst(node),
            SUBTYPE | SET_OF => return self.set_like(node),
            PROJ => {
                let receiver = self.term_or_gap(kids.first().cloned(), node, "projection target");
                let index = tok_text(node, NUMBER)
                    .and_then(|t| t.parse().ok())
                    .unwrap_or(0);
                Term::Proj { receiver, index }
            }
            FIELD_ACCESS | PIPE_PROJ => {
                let receiver = self.term_or_gap(kids.first().cloned(), node, "field target");
                let name = Name(tok_text(node, IDENT).unwrap_or_default());
                Term::Field { receiver, name }
            }
            TYPE_ASCRIPTION => {
                let term = self.term_or_gap(kids.first().cloned(), node, "ascribed term");
                // Absent in `(e :)`, which defers to the expected type.
                let ty = self.opt_term(kids.get(1).cloned());
                Term::Ascription { term, ty }
            }
            AT_TERM => {
                // `@f` makes implicit arguments explicit. The operand may be a
                // bare name, which the CST stores as a token.
                let inner = match kids.first() {
                    Some(n) => self.term(n),
                    None => {
                        let name = Name(tok_text(node, IDENT).unwrap_or_default());
                        self.module.alloc_term(Term::Ref(name))
                    }
                };
                Term::Explicit(inner)
            }
            UNIV_ARGS => {
                // The first term child is the receiver; the rest are levels,
                // each of which may be an expression such as `max u w`.
                let mut children = kids.into_iter();
                let term = self.term_or_gap(children.next(), node, "universe-annotated term");
                let levels = children.map(|level| self.term(&level)).collect();
                Term::Universes { term, levels }
            }
            CALC_TERM => Term::Calc {
                steps: self.calc_steps(node),
            },
            NAMED_ARG => {
                // Reached only if a named argument appears outside an
                // application; the value is the term.
                return self.term_or_gap(kids.first().cloned(), node, "named argument value");
            }
            PAREN_TERM => {
                // Parentheses carry no meaning of their own beyond grouping, so
                // they are dropped — except when they wrap nothing, as in the
                // unit value or an operator section.
                return match kids.first() {
                    Some(inner) => self.term(inner),
                    None => {
                        let sym = node
                            .children_with_tokens()
                            .filter_map(|it| it.into_token())
                            .filter(|t| !t.kind().is_trivia() && !t.kind().is_delimiter())
                            .map(|t| t.text().to_string())
                            .next();
                        let term = match sym {
                            Some(op) => Term::Symbol(Name(op)),
                            None => Term::Ref(Name("Unit.unit".into())),
                        };
                        let id = self.module.alloc_term(term);
                        self.link(HirId::Term(id), node);
                        id
                    }
                };
            }
            // Deliberately not interpreted: a quotation's contents are syntax,
            // not a term.
            QUOTED_TERM => return self.unmodeled(node),
            _ => return self.gap(node, format!("unhandled term kind {:?}", node.kind())),
        };
        let id = self.module.alloc_term(term);
        self.link(HirId::Term(id), node);
        id
    }

    fn literal(&mut self, node: &SyntaxNode) -> TermId {
        let token = first_tok(node);
        let lit = match token.as_ref().map(|t| (t.kind(), t.text().to_string())) {
            Some((NUMBER, text)) => Lit::Nat(text),
            Some((SCIENTIFIC, text)) => Lit::Scientific(text),
            Some((STRING | RAW_STRING, text)) => Lit::Str(text),
            Some((CHAR, text)) => Lit::Char(text),
            Some((NAME_LIT, text)) => Lit::Name(text),
            _ => return self.gap(node, "literal with no token"),
        };
        let id = self.module.alloc_term(Term::Lit(lit));
        self.link(HirId::Term(id), node);
        id
    }

    fn app(&mut self, node: &SyntaxNode) -> TermId {
        let kids = term_children(node);
        let mut iter = kids.into_iter();
        let func = self.term_or_gap(iter.next(), node, "applied function");
        let args = iter
            .map(|arg| {
                if arg.kind() == NAMED_ARG {
                    let name = tok_text(&arg, IDENT).map(Name);
                    let value = self.term_or_gap(
                        term_children(&arg).first().cloned(),
                        &arg,
                        "named argument value",
                    );
                    Arg { name, value }
                } else {
                    Arg {
                        name: None,
                        value: self.term(&arg),
                    }
                }
            })
            .collect();
        let id = self.module.alloc_term(Term::App { func, args });
        self.link(HirId::Term(id), node);
        id
    }

    fn infix(&mut self, node: &SyntaxNode) -> TermId {
        let kids = term_children(node);
        // A generic operator is wrapped in an `OPERATOR` node and keeps the
        // `SYMBOL` token kind; that is how an assumed precedence is detectable.
        let (op, precedence) = match child_of(node, OPERATOR) {
            Some(operator) => {
                let token = first_tok(&operator);
                let precedence = match token.as_ref().map(|t| t.kind()) {
                    Some(SYMBOL) => Precedence::Assumed,
                    _ => Precedence::Known,
                };
                (
                    token.map(|t| t.text().to_string()).unwrap_or_default(),
                    precedence,
                )
            }
            None => {
                let op = node
                    .children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .find(|t| !t.kind().is_trivia())
                    .map(|t| t.text().to_string())
                    .unwrap_or_default();
                (op, Precedence::Known)
            }
        };
        let lhs = self.term_or_gap(kids.first().cloned(), node, "left operand");
        let rhs = self.term_or_gap(kids.get(1).cloned(), node, "right operand");
        let id = self.module.alloc_term(Term::Infix {
            op: Name(op),
            precedence,
            lhs,
            rhs,
        });
        self.link(HirId::Term(id), node);
        id
    }

    fn quantifier(&mut self, node: &SyntaxNode) -> TermId {
        let kind = match first_tok(node) {
            Some(t) => match t.kind() {
                FORALL | KW_FORALL_KW => QuantifierKind::Forall,
                EXISTS | KW_EXISTS_KW => QuantifierKind::Exists,
                SIGMA => QuantifierKind::Sigma,
                PI => QuantifierKind::Pi,
                _ => QuantifierKind::BigOperator(Name(t.text().to_string())),
            },
            None => QuantifierKind::Forall,
        };
        let binders = self.binders_in(node);
        let body = self.term_or_gap(term_children(node).last().cloned(), node, "quantifier body");
        let id = self.module.alloc_term(Term::Quantifier {
            kind,
            binders,
            body,
        });
        self.link(HirId::Term(id), node);
        id
    }

    fn let_term(&mut self, node: &SyntaxNode) -> TermId {
        let pat = self
            .opt_pat_in(node)
            .unwrap_or_else(|| self.module.alloc_pat(Pat::Hole));
        let ty = self.type_spec(node);
        let body_node = child_of(node, DECL_BODY);
        let value = body_node
            .as_ref()
            .and_then(|b| term_children(b).first().cloned())
            .map(|n| self.term(&n));
        let arms = child_of(node, DECL_EQNS)
            .map(|e| self.arms_in(&e))
            .unwrap_or_default();
        // The trailing term is the body; everything else has been consumed.
        let body = self.term_or_gap(term_children(node).last().cloned(), node, "let body");
        let id = self.module.alloc_term(Term::Let {
            pat,
            ty,
            value,
            arms,
            body,
        });
        self.link(HirId::Term(id), node);
        id
    }

    fn have_term(&mut self, node: &SyntaxNode) -> TermId {
        let pat = self.opt_pat_in(node);
        let ty = self.type_spec(node);
        let kids = term_children(node);
        // `have h : T := value` then the body: two direct term children, the
        // value first.
        let (value, body) = match kids.len() {
            0 => (None, self.gap(node, "have with no body")),
            1 => (None, self.term(&kids[0])),
            _ => {
                let value = self.term(&kids[0]);
                let body = self.term(kids.last().expect("checked length"));
                (Some(value), body)
            }
        };
        let id = self.module.alloc_term(Term::Have {
            pat,
            ty,
            value,
            body,
        });
        self.link(HirId::Term(id), node);
        id
    }

    fn match_term(&mut self, node: &SyntaxNode) -> TermId {
        let discrs = children_of(node, MATCH_DISCRS)
            .iter()
            .filter_map(|d| term_children(d).first().cloned())
            .map(|d| self.term(&d))
            .collect();
        let arms = self.arms_in(node);
        let id = self.module.alloc_term(Term::Match { discrs, arms });
        self.link(HirId::Term(id), node);
        id
    }

    fn struct_inst(&mut self, node: &SyntaxNode) -> TermId {
        let source = child_of(node, STRUCT_INST_SRC)
            .and_then(|s| term_children(&s).first().cloned())
            .map(|s| self.term(&s));
        let fields = node
            .descendants()
            .filter(|n| n.kind() == STRUCT_INST_FIELD || n.kind() == STRUCT_FIELD)
            .filter_map(|f| {
                let name = tok_text(&f, IDENT)?;
                let value = term_children(&f).first().cloned();
                Some((Name(name), value))
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|(name, value)| FieldInit {
                name,
                value: value.map(|v| self.term(&v)),
            })
            .collect();
        let id = self.module.alloc_term(Term::StructInst { source, fields });
        self.link(HirId::Term(id), node);
        id
    }

    fn set_like(&mut self, node: &SyntaxNode) -> TermId {
        let is_subtype = node.kind() == SUBTYPE;
        let name = Name(
            tok_text(node, IDENT)
                .or(tok_text(node, UNDERSCORE))
                .unwrap_or_default(),
        );
        let ty = self.type_spec(node);
        let binder = self.module.alloc_binder(Binder {
            names: vec![name],
            ty,
            explicitness: Explicitness::Explicit,
            default: None,
        });
        let predicate =
            self.term_or_gap(term_children(node).last().cloned(), node, "set predicate");
        let term = if is_subtype {
            Term::Subtype { binder, predicate }
        } else {
            Term::SetOf { binder, predicate }
        };
        let id = self.module.alloc_term(term);
        self.link(HirId::Term(id), node);
        id
    }

    fn calc_steps(&mut self, node: &SyntaxNode) -> Vec<CalcStep> {
        node.descendants()
            .filter(|n| n.kind() == CALC_STEP)
            .collect::<Vec<_>>()
            .into_iter()
            .map(|step| {
                let kids = term_children(&step);
                let relation = self.term_or_gap(kids.first().cloned(), &step, "calc relation");
                let proof = self.term_or_gap(kids.get(1).cloned(), &step, "calc proof");
                CalcStep { relation, proof }
            })
            .collect()
    }

    /// Every term directly under a bracketed form.
    fn terms_in(&mut self, node: &SyntaxNode) -> Vec<TermId> {
        term_children(node)
            .into_iter()
            .map(|n| self.term(&n))
            .collect()
    }

    /// The `: T` annotation, if written.
    fn type_spec(&mut self, node: &SyntaxNode) -> Option<TermId> {
        let spec = node.children().find(|n| n.kind() == TYPE_SPEC)?;
        let ty = term_children(&spec).first().cloned()?;
        Some(self.term(&ty))
    }

    // ---- Binders and patterns ---------------------------------------------

    /// Every binder under a `BINDERS` group, or directly under the node.
    fn binders_in(&mut self, node: &SyntaxNode) -> Vec<BinderId> {
        let groups: Vec<SyntaxNode> = if node.kind() == BINDERS {
            vec![node.clone()]
        } else {
            children_of(node, BINDERS)
        };
        let mut out = Vec::new();
        for group in groups {
            for child in group.children() {
                if ast::Binder::cast(child.clone()).is_some() {
                    out.push(self.binder(&child));
                }
            }
        }
        // A dependent arrow lists its bracketed binders directly.
        for child in node.children() {
            if matches!(
                child.kind(),
                PAREN_BINDER | IMPLICIT_BINDER | STRICT_IMPLICIT_BINDER | INST_BINDER
            ) {
                out.push(self.binder(&child));
            }
        }
        out
    }

    fn binder(&mut self, node: &SyntaxNode) -> BinderId {
        let explicitness = match node.kind() {
            IMPLICIT_BINDER => Explicitness::Implicit,
            STRICT_IMPLICIT_BINDER => Explicitness::StrictImplicit,
            INST_BINDER => Explicitness::Instance,
            _ => Explicitness::Explicit,
        };
        let names = toks(node, &[IDENT, UNDERSCORE])
            .into_iter()
            .map(Name)
            .collect();
        let ty = self.type_spec(node).or_else(|| {
            // An anonymous instance binder has no `: T`; its contents are the
            // class being required.
            if node.kind() == INST_BINDER {
                term_children(node).first().cloned().map(|n| self.term(&n))
            } else {
                None
            }
        });
        let default = child_of(node, DEFAULT_VALUE)
            .and_then(|d| term_children(&d).first().cloned())
            .map(|d| self.term(&d));
        let id = self.module.alloc_binder(Binder {
            names,
            ty,
            explicitness,
            default,
        });
        self.link(HirId::Binder(id), node);
        id
    }

    /// The first pattern directly under the node, if any.
    fn opt_pat_in(&mut self, node: &SyntaxNode) -> Option<PatId> {
        let pat = node.children().find(|n| {
            matches!(n.kind(), RCASES_PAT | RCASES_TUPLE | RCASES_ALT | DECL_ID)
                || (n.kind() == ANON_CTOR)
        })?;
        Some(self.pat(&pat))
    }

    fn pat(&mut self, node: &SyntaxNode) -> PatId {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || self.pat_inner(node))
    }

    fn pat_inner(&mut self, node: &SyntaxNode) -> PatId {
        let pat = match node.kind() {
            RCASES_PAT => {
                if ast::token(node, MINUS).is_some() {
                    Pat::Discard
                } else if ast::token(node, UNDERSCORE).is_some() {
                    Pat::Hole
                } else {
                    Pat::Name(Name(tok_text(node, IDENT).unwrap_or_default()))
                }
            }
            RCASES_TUPLE | ANON_CTOR | TUPLE => Pat::Tuple(self.sub_pats(node)),
            RCASES_ALT => Pat::Alt(self.sub_pats(node)),
            DECL_ID => Pat::Name(Name(tok_text(node, IDENT).unwrap_or_default())),
            SIMPLE_BINDER => Pat::Name(Name(
                toks(node, &[IDENT, UNDERSCORE])
                    .first()
                    .cloned()
                    .unwrap_or_default(),
            )),
            _ if ast::Term::cast(node.clone()).is_some() => {
                let term = self.term(node);
                Pat::Term(term)
            }
            _ => Pat::Opaque(Self::ptr(node)),
        };
        let id = self.module.alloc_pat(pat);
        self.link(HirId::Pat(id), node);
        id
    }

    /// Nested patterns, treating a term child as a pattern.
    fn sub_pats(&mut self, node: &SyntaxNode) -> Vec<PatId> {
        node.children()
            .filter(|n| {
                matches!(n.kind(), RCASES_PAT | RCASES_TUPLE | RCASES_ALT)
                    || ast::Term::cast(n.clone()).is_some()
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|n| self.pat(&n))
            .collect()
    }

    /// The alternatives under a `MATCH_ALTS` group.
    fn arms_in(&mut self, node: &SyntaxNode) -> Vec<Arm> {
        let alts = match child_of(node, MATCH_ALTS) {
            Some(a) => a,
            None if node.kind() == MATCH_ALTS => node.clone(),
            None => return Vec::new(),
        };
        children_of(&alts, MATCH_ALT)
            .into_iter()
            .map(|alt| {
                let pats = match child_of(&alt, PATTERNS) {
                    Some(p) => p
                        .children()
                        .filter(|n| ast::Term::cast(n.clone()).is_some())
                        .collect::<Vec<_>>()
                        .into_iter()
                        .map(|n| self.pat(&n))
                        .collect(),
                    None => Vec::new(),
                };
                // The right-hand side is a tactic sequence in tactic position
                // and a term otherwise.
                let body = match child_of(&alt, TACTIC_SEQ) {
                    Some(seq) => ArmBody::Tactic(self.tactic_seq(&seq)),
                    None => ArmBody::Term(self.term_or_gap(
                        term_children(&alt).last().cloned(),
                        &alt,
                        "alternative body",
                    )),
                };
                Arm { pats, body }
            })
            .collect()
    }

    // ---- Do notation -------------------------------------------------------

    fn do_seq(&mut self, node: &SyntaxNode) -> Vec<DoStmt> {
        let seq = match child_of(node, DO_SEQ) {
            Some(s) => s,
            None if node.kind() == DO_SEQ => node.clone(),
            None => return Vec::new(),
        };
        seq.children()
            .filter(|n| {
                matches!(
                    n.kind(),
                    DO_LET
                        | DO_LET_ARROW
                        | DO_BIND
                        | DO_REASSIGN
                        | DO_RETURN
                        | DO_IF
                        | DO_FOR
                        | DO_WHILE
                        | DO_REPEAT
                        | DO_TRY
                        | DO_UNLESS
                        | DO_BREAK
                        | DO_CONTINUE
                        | DO_EXPR
                )
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|stmt| self.do_stmt(&stmt))
            .collect()
    }

    fn do_stmt(&mut self, node: &SyntaxNode) -> DoStmt {
        let mutable = ast::token(node, KW_MUT).is_some();
        match node.kind() {
            DO_LET | DO_LET_ARROW => {
                let pat = self
                    .opt_pat_in(node)
                    .unwrap_or_else(|| self.module.alloc_pat(Pat::Hole));
                let ty = self.type_spec(node);
                let value =
                    self.term_or_gap(term_children(node).last().cloned(), node, "let value");
                if node.kind() == DO_LET {
                    DoStmt::Let {
                        pat,
                        ty,
                        value,
                        mutable,
                    }
                } else {
                    DoStmt::LetArrow {
                        pat,
                        ty,
                        value,
                        mutable,
                    }
                }
            }
            DO_BIND => {
                let pat = self
                    .opt_pat_in(node)
                    .unwrap_or_else(|| self.module.alloc_pat(Pat::Hole));
                let value =
                    self.term_or_gap(term_children(node).last().cloned(), node, "bind value");
                DoStmt::Bind { pat, value }
            }
            DO_REASSIGN => {
                let name = Name(tok_text(node, IDENT).unwrap_or_default());
                let value = self.term_or_gap(
                    term_children(node).last().cloned(),
                    node,
                    "reassignment value",
                );
                DoStmt::Reassign { name, value }
            }
            DO_RETURN => DoStmt::Return(self.opt_term(term_children(node).first().cloned())),
            DO_BREAK => DoStmt::Break,
            DO_CONTINUE => DoStmt::Continue,
            DO_IF => {
                let cond =
                    self.term_or_gap(term_children(node).first().cloned(), node, "condition");
                let branches = children_of(node, DO_SEQ);
                let then_branch = branches.first().map(|b| self.do_seq(b)).unwrap_or_default();
                let else_branch = branches.get(1).map(|b| self.do_seq(b));
                DoStmt::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
            DO_FOR => {
                let group = child_of(node, BINDERS);
                let (pat, iterable) = match group {
                    Some(g) => {
                        let terms = term_children(&g);
                        let pat = terms
                            .first()
                            .map(|p| self.pat(p))
                            .unwrap_or_else(|| self.module.alloc_pat(Pat::Hole));
                        let iterable =
                            self.term_or_gap(terms.get(1).cloned(), node, "loop collection");
                        (pat, iterable)
                    }
                    None => {
                        let pat = self.module.alloc_pat(Pat::Hole);
                        let iterable = self.gap(node, "for loop with no binder");
                        (pat, iterable)
                    }
                };
                let body = child_of(node, DO_SEQ)
                    .map(|b| self.do_seq(&b))
                    .unwrap_or_default();
                DoStmt::For {
                    pat,
                    iterable,
                    body,
                }
            }
            DO_WHILE | DO_UNLESS => {
                let cond =
                    self.term_or_gap(term_children(node).first().cloned(), node, "condition");
                let body = child_of(node, DO_SEQ)
                    .map(|b| self.do_seq(&b))
                    .unwrap_or_default();
                DoStmt::While { cond, body }
            }
            DO_TRY => {
                let body = child_of(node, DO_SEQ)
                    .map(|b| self.do_seq(&b))
                    .unwrap_or_default();
                let catches = children_of(node, DO_CATCH)
                    .into_iter()
                    .map(|c| self.do_seq(&c))
                    .collect();
                let finally_branch = child_of(node, DO_FINALLY).map(|f| self.do_seq(&f));
                DoStmt::Try {
                    body,
                    catches,
                    finally_branch,
                }
            }
            DO_EXPR => {
                let term =
                    self.term_or_gap(term_children(node).first().cloned(), node, "statement");
                DoStmt::Expr(term)
            }
            _ => DoStmt::Opaque(Self::ptr(node)),
        }
    }

    // ---- Tactics -----------------------------------------------------------

    fn tactic_seq(&mut self, node: &SyntaxNode) -> TacticId {
        let tactics = node
            .children()
            .filter(|n| ast::Tactic::cast(n.clone()).is_some())
            .collect::<Vec<_>>()
            .into_iter()
            .map(|t| self.tactic(&t))
            .collect();
        let id = self.module.alloc_tactic(Tactic::Seq(tactics));
        self.link(HirId::Tactic(id), node);
        id
    }

    fn tactic(&mut self, node: &SyntaxNode) -> TacticId {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || self.tactic_inner(node))
    }

    fn tactic_inner(&mut self, node: &SyntaxNode) -> TacticId {
        let name = || {
            Name(
                first_tok(node)
                    .map(|t| t.text().to_string())
                    .unwrap_or_default(),
            )
        };
        let tactic = match node.kind() {
            TACTIC_SIMP => Tactic::Simp {
                name: name(),
                only: ast::token(node, KW_ONLY).is_some(),
                args: self.simp_args(node),
                location: self.location(node),
            },
            TACTIC_REWRITE => Tactic::Rewrite {
                name: name(),
                rules: self.rw_rules(node),
                location: self.location(node),
                occurrence: tok_text(node, NUMBER).and_then(|t| t.parse().ok()),
            },
            TACTIC_TERM | TACTIC_TERM_LIST => Tactic::Apply {
                name: name(),
                terms: self.terms_in(node),
                location: self.location(node),
            },
            TACTIC_INTRO => Tactic::Intro {
                name: name(),
                pats: self.sub_pats(node),
            },
            TACTIC_CASES => {
                let targets = child_of(node, TACTIC_TARGETS)
                    .map(|t| self.terms_in(&t))
                    .unwrap_or_default();
                let using_clauses = children_of(node, USING_CLAUSE);
                let using_term = using_clauses
                    .iter()
                    .find(|u| ast::token(u, KW_USING).is_some())
                    .and_then(|u| term_children(u).first().cloned())
                    .map(|t| self.term(&t));
                let generalizing = using_clauses
                    .iter()
                    .filter(|u| ast::token(u, KW_GENERALIZING).is_some())
                    .flat_map(|u| toks(u, &[IDENT]))
                    .map(Name)
                    .collect();
                let with_clause = child_of(node, WITH_CLAUSE);
                let arms = with_clause
                    .as_ref()
                    .map(|w| self.arms_in(w))
                    .unwrap_or_default();
                let pats = with_clause
                    .as_ref()
                    .and_then(|w| child_of(w, PATTERNS))
                    .map(|p| self.sub_pats(&p))
                    .unwrap_or_default();
                Tactic::Cases {
                    name: name(),
                    targets,
                    using_term,
                    generalizing,
                    arms,
                    pats,
                }
            }
            TACTIC_HAVE => Tactic::Have {
                name: name(),
                pat: self.opt_pat_in(node),
                ty: self.type_spec(node),
                value: term_after(node, COLON_EQ).map(|t| self.term(&t)),
            },
            TACTIC_CASE => {
                let tags = child_of(node, CASE_ARGS)
                    .map(|a| toks(&a, &[IDENT, UNDERSCORE, NUMBER]))
                    .unwrap_or_default()
                    .into_iter()
                    .map(Name)
                    .collect();
                let body = self.inner_seq(node);
                Tactic::Case {
                    name: name(),
                    tags,
                    body,
                }
            }
            TACTIC_FOCUS => Tactic::Focus(self.inner_seq(node)),
            TACTIC_SEQ_BRACKETED => return self.inner_seq(node),
            TACTIC_ALT => Tactic::Alt(
                children_of(node, TACTIC_SEQ)
                    .into_iter()
                    .map(|s| self.tactic_seq(&s))
                    .collect(),
            ),
            TACTIC_COMBINATOR => Tactic::Chain(
                node.children()
                    .filter(|n| ast::Tactic::cast(n.clone()).is_some())
                    .collect::<Vec<_>>()
                    .into_iter()
                    .map(|t| self.tactic(&t))
                    .collect(),
            ),
            TACTIC_COMBINATOR_APP => Tactic::Combinator {
                name: name(),
                count: tok_text(node, NUMBER).and_then(|t| t.parse().ok()),
                body: self.inner_seq(node),
            },
            TACTIC_CONV => Tactic::Conv {
                name: name(),
                location: self.location(node),
                pattern: term_after(node, KW_IN).map(|t| self.term(&t)),
                body: self.inner_seq(node),
            },
            TACTIC_SHOW => Tactic::Show(self.term_or_gap(
                term_children(node).first().cloned(),
                node,
                "shown goal",
            )),
            TACTIC_CALC => Tactic::Calc {
                steps: self.calc_steps(node),
            },
            // A tactic with no shape: either it takes no arguments, or the
            // grammar does not model it. Neither is an error.
            TACTIC => Tactic::Opaque {
                name: Some(name()),
                node: Self::ptr(node),
            },
            _ => Tactic::Opaque {
                name: None,
                node: Self::ptr(node),
            },
        };
        let id = self.module.alloc_tactic(tactic);
        self.link(HirId::Tactic(id), node);
        id
    }

    /// The tactic sequence nested inside a tactic.
    fn inner_seq(&mut self, node: &SyntaxNode) -> TacticId {
        match child_of(node, TACTIC_SEQ) {
            Some(seq) => self.tactic_seq(&seq),
            None => {
                let ptr = Self::ptr(node);
                self.module.errors.push(LoweringError {
                    message: "tactic with no nested block".into(),
                    node: ptr,
                });
                self.module.alloc_tactic(Tactic::Opaque {
                    name: None,
                    node: ptr,
                })
            }
        }
    }

    fn location(&mut self, node: &SyntaxNode) -> Option<Location> {
        let loc = child_of(node, LOCATION)?;
        Some(Location {
            hypotheses: toks(&loc, &[IDENT]).into_iter().map(Name).collect(),
            goal: ast::token(&loc, TURNSTILE).is_some()
                || ast::token(&loc, TURNSTILE_ASCII).is_some(),
            everywhere: ast::token(&loc, STAR).is_some(),
        })
    }

    fn simp_args(&mut self, node: &SyntaxNode) -> Vec<SimpArg> {
        let list = match child_of(node, SIMP_ARG_LIST) {
            Some(l) => l,
            None => return Vec::new(),
        };
        children_of(&list, SIMP_ARG)
            .into_iter()
            .map(|arg| {
                if ast::token(&arg, STAR).is_some() {
                    return SimpArg::Wildcard;
                }
                match child_of(&arg, RW_RULE) {
                    Some(rule) => {
                        let removed = ast::token(&rule, MINUS).is_some();
                        let reversed = ast::token(&rule, LEFT_ARROW).is_some()
                            || ast::token(&rule, LEFT_ARROW_ASCII).is_some();
                        let term = self.term_or_gap(
                            term_children(&rule).first().cloned(),
                            &rule,
                            "simp lemma",
                        );
                        if removed {
                            SimpArg::Removed(term)
                        } else {
                            SimpArg::Lemma { term, reversed }
                        }
                    }
                    None => {
                        let term = self.term_or_gap(
                            term_children(&arg).first().cloned(),
                            &arg,
                            "simp lemma",
                        );
                        SimpArg::Lemma {
                            term,
                            reversed: false,
                        }
                    }
                }
            })
            .collect()
    }

    fn rw_rules(&mut self, node: &SyntaxNode) -> Vec<RwRule> {
        let list = match child_of(node, RW_RULE_LIST) {
            Some(l) => l,
            None => return Vec::new(),
        };
        children_of(&list, RW_RULE)
            .into_iter()
            .map(|rule| {
                let reversed = ast::token(&rule, LEFT_ARROW).is_some()
                    || ast::token(&rule, LEFT_ARROW_ASCII).is_some();
                let term =
                    self.term_or_gap(term_children(&rule).first().cloned(), &rule, "rewrite rule");
                RwRule { term, reversed }
            })
            .collect()
    }

    // ---- Items -------------------------------------------------------------

    fn item(&mut self, node: &SyntaxNode) -> ItemId {
        let kind = match node.kind() {
            DEF => ItemKind::Def,
            THEOREM => ItemKind::Theorem,
            ABBREV => ItemKind::Abbrev,
            EXAMPLE => ItemKind::Example,
            INSTANCE => ItemKind::Instance,
            AXIOM => ItemKind::Axiom,
            OPAQUE_DECL => ItemKind::Opaque,
            STRUCTURE => ItemKind::Structure,
            CLASS_DECL => ItemKind::Class,
            INDUCTIVE => ItemKind::Inductive,
            NAMESPACE => ItemKind::Namespace,
            SECTION => ItemKind::Section,
            END_CMD => ItemKind::End,
            IMPORT => ItemKind::Import,
            OPEN_CMD => ItemKind::Open,
            VARIABLE_CMD => ItemKind::Variable,
            UNIVERSE_CMD => ItemKind::Universe,
            _ => ItemKind::Other(Name(
                first_tok(node)
                    .map(|t| t.text().to_string())
                    .unwrap_or_default(),
            )),
        };

        let modifiers_node = child_of(node, DECL_MODIFIERS);
        let doc = modifiers_node
            .as_ref()
            .and_then(|m| tok_text(m, DOC_COMMENT))
            .or_else(|| tok_text(node, DOC_COMMENT));
        let attrs = modifiers_node
            .as_ref()
            .and_then(|m| child_of(m, ATTR_LIST))
            .map(|l| {
                children_of(&l, ATTR)
                    .iter()
                    .map(|a| a.text().to_string())
                    .collect()
            })
            .unwrap_or_default();
        let modifiers = modifiers_node
            .as_ref()
            .map(|m| {
                m.children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .filter(|t| t.kind().is_keyword())
                    .map(|t| Name(t.text().to_string()))
                    .collect()
            })
            .unwrap_or_default();

        let name = child_of(node, DECL_ID)
            .and_then(|id| tok_text(&id, IDENT))
            .or_else(|| match kind {
                // For a namespace or `end`, the bare identifier is the name.
                ItemKind::Namespace | ItemKind::Section | ItemKind::End => tok_text(node, IDENT),
                _ => None,
            })
            .map(Name);

        let sig = child_of(node, DECL_SIG);
        let sig_node = sig.as_ref().unwrap_or(node);
        let binders = self.binders_in(sig_node);
        let ty = self.type_spec(sig_node);

        let body = child_of(node, DECL_BODY);
        let value = body
            .as_ref()
            .and_then(|b| term_children(b).first().cloned())
            .map(|v| self.term(&v));
        let arms = child_of(node, DECL_EQNS)
            .map(|e| self.arms_in(&e))
            .unwrap_or_default();

        let ctors = self.ctors_in(node);
        let fields = self.fields_in(node);
        let deriving = child_of(node, DERIVING_CLAUSE)
            .map(|d| toks(&d, &[IDENT]))
            .unwrap_or_default()
            .into_iter()
            .map(Name)
            .collect();

        // `variable (α) in <command>` scopes one command; `mutual … end`
        // contains several. Collecting all of them rather than the first is what
        // keeps a `mutual` block's later declarations from being dropped
        // silently — nothing would have become `Opaque` to reveal the loss.
        let nested: Vec<ItemId> = node
            .children()
            .filter(|n| ast::Command::cast(n.clone()).is_some())
            .collect::<Vec<_>>()
            .into_iter()
            .map(|inner| self.item(&inner))
            .collect();

        let id = self.module.alloc_item(Item {
            kind,
            name,
            doc,
            attrs,
            modifiers,
            binders,
            ty,
            value,
            arms,
            ctors,
            fields,
            deriving,
            nested,
        });
        self.link(HirId::Item(id), node);
        id
    }

    fn ctors_in(&mut self, node: &SyntaxNode) -> Vec<Ctor> {
        let list = match child_of(node, CTOR_LIST) {
            Some(l) => l,
            None => return Vec::new(),
        };
        children_of(&list, CTOR)
            .into_iter()
            .map(|ctor| Ctor {
                name: Name(tok_text(&ctor, IDENT).unwrap_or_default()),
                binders: self.binders_in(&ctor),
                ty: self.type_spec(&ctor),
                doc: tok_text(&ctor, DOC_COMMENT),
            })
            .collect()
    }

    fn fields_in(&mut self, node: &SyntaxNode) -> Vec<FieldDecl> {
        let list = match child_of(node, STRUCT_FIELD_LIST) {
            Some(l) => l,
            None => return Vec::new(),
        };
        children_of(&list, STRUCT_FIELD)
            .into_iter()
            .map(|field| {
                let name = field
                    .descendants_with_tokens()
                    .filter_map(|it| it.into_token())
                    .find(|t| t.kind() == IDENT)
                    .map(|t| t.text().to_string())
                    .unwrap_or_default();
                let inner = child_of(&field, SIMPLE_BINDER).unwrap_or_else(|| field.clone());
                let ty = field
                    .descendants()
                    .find(|n| n.kind() == TYPE_SPEC)
                    .and_then(|s| term_children(&s).first().cloned())
                    .map(|t| self.term(&t));
                let default = term_after(&inner, COLON_EQ).map(|d| self.term(&d));
                FieldDecl {
                    name: Name(name),
                    binders: self.binders_in(&inner),
                    ty,
                    default,
                    doc: tok_text(&field, DOC_COMMENT),
                }
            })
            .collect()
    }
}
