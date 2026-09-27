//! Walking and rewriting the ids a HIR node refers to.
//!
//! This module is the single place that knows each node's shape. Traversal,
//! structural comparison and id remapping — the last of which rewriting
//! needs — are all derived from [`visit_term`] and its siblings, rather than
//! each carrying its own forty-arm match.
//!
//! Visitors take `&mut` ids so the same functions serve both reading (record
//! what you see) and rewriting (substitute as you go).

use super::*;

/// Receives each id a node refers to, in a stable order.
///
/// Every method has a default, so an implementation overrides only the kinds it
/// cares about.
#[allow(unused_variables)]
pub trait Visitor {
    /// A referenced term.
    fn term(&mut self, id: &mut TermId) {}
    /// A referenced binder.
    fn binder(&mut self, id: &mut BinderId) {}
    /// A referenced pattern.
    fn pat(&mut self, id: &mut PatId) {}
    /// A referenced tactic.
    fn tactic(&mut self, id: &mut TacticId) {}
}

/// Visits the ids a term refers to.
///
/// Takes `&mut dyn Visitor` rather than a generic so the functions can be
/// passed as values, which is what lets structural comparison share one
/// canonicalisation helper across all four node kinds.
pub fn visit_term(term: &mut Term, v: &mut dyn Visitor) {
    match term {
        Term::Ref(_)
        | Term::DotIdent(_)
        | Term::Lit(_)
        | Term::Hole
        | Term::SyntheticHole(_)
        | Term::Sorry
        | Term::Symbol(_)
        | Term::Placeholder
        | Term::Antiquotation(_)
        | Term::Opaque(_) => {}
        Term::Sort { level, .. } => opt_term(level, v),
        Term::App { func, args } => {
            v.term(func);
            for arg in args {
                v.term(&mut arg.value);
            }
        }
        Term::Infix { lhs, rhs, .. } => {
            v.term(lhs);
            v.term(rhs);
        }
        Term::Prefix { operand, .. } | Term::Postfix { operand, .. } => v.term(operand),
        Term::Arrow { domain, codomain } => {
            v.term(domain);
            v.term(codomain);
        }
        Term::DepArrow { binders, codomain } => {
            for b in binders {
                v.binder(b);
            }
            v.term(codomain);
        }
        Term::Fun { binders, body } | Term::Quantifier { binders, body, .. } => {
            for b in binders {
                v.binder(b);
            }
            v.term(body);
        }
        Term::FunAlts { arms } => visit_arms(arms, v),
        Term::Let {
            pat,
            ty,
            value,
            arms,
            body,
        } => {
            v.pat(pat);
            opt_term(ty, v);
            opt_term(value, v);
            visit_arms(arms, v);
            v.term(body);
        }
        Term::Have {
            pat,
            ty,
            value,
            body,
        } => {
            opt_pat(pat, v);
            opt_term(ty, v);
            opt_term(value, v);
            v.term(body);
        }
        Term::Show { ty, proof } => {
            v.term(ty);
            opt_term(proof, v);
        }
        Term::Suffices { pat, ty, proof } => {
            opt_pat(pat, v);
            opt_term(ty, v);
            opt_term(proof, v);
        }
        Term::Match { discrs, arms } => {
            for d in discrs {
                v.term(d);
            }
            visit_arms(arms, v);
        }
        Term::If {
            cond,
            then_branch,
            else_branch,
        } => {
            v.term(cond);
            v.term(then_branch);
            v.term(else_branch);
        }
        Term::Do(stmts) => visit_do(stmts, v),
        Term::By(tactic) => v.tactic(tactic),
        Term::Tuple(items)
        | Term::AnonCtor(items)
        | Term::ListLit(items)
        | Term::ArrayLit(items)
        | Term::SetLit(items)
        | Term::Bracketed { parts: items, .. } => {
            for i in items {
                v.term(i);
            }
        }
        Term::StructInst { source, fields } => {
            opt_term(source, v);
            for field in fields {
                opt_term(&mut field.value, v);
            }
        }
        Term::Subtype { binder, predicate } | Term::SetOf { binder, predicate } => {
            v.binder(binder);
            v.term(predicate);
        }
        Term::Index {
            receiver,
            args,
            proof,
            ..
        } => {
            v.term(receiver);
            for a in args {
                v.term(a);
            }
            opt_term(proof, v);
        }
        Term::Proj { receiver, .. } | Term::Field { receiver, .. } => v.term(receiver),
        Term::Ascription { term, ty } => {
            v.term(term);
            opt_term(ty, v);
        }
        Term::Explicit(inner) => v.term(inner),
        Term::Universes { term, levels } => {
            v.term(term);
            for level in levels {
                v.term(level);
            }
        }
        Term::Calc { steps } => visit_calc(steps, v),
    }
}

/// Visits the ids a binder refers to.
pub fn visit_binder(binder: &mut Binder, v: &mut dyn Visitor) {
    opt_term(&mut binder.ty, v);
    opt_term(&mut binder.default, v);
}

/// Visits the ids a pattern refers to.
pub fn visit_pat(pat: &mut Pat, v: &mut dyn Visitor) {
    match pat {
        Pat::Name(_) | Pat::Hole | Pat::Discard | Pat::Opaque(_) => {}
        Pat::Tuple(pats) | Pat::Alt(pats) => {
            for p in pats {
                v.pat(p);
            }
        }
        Pat::Term(term) => v.term(term),
        Pat::As { pat, .. } => v.pat(pat),
    }
}

/// Visits the ids a tactic refers to.
pub fn visit_tactic(tactic: &mut Tactic, v: &mut dyn Visitor) {
    match tactic {
        Tactic::Opaque { .. } => {}
        Tactic::Seq(tactics) | Tactic::Chain(tactics) | Tactic::Alt(tactics) => {
            for t in tactics {
                v.tactic(t);
            }
        }
        Tactic::Simp { args, .. } => {
            for arg in args {
                match arg {
                    SimpArg::Lemma { term, .. } | SimpArg::Removed(term) => v.term(term),
                    SimpArg::Wildcard => {}
                }
            }
        }
        Tactic::Rewrite { rules, .. } => {
            for rule in rules {
                v.term(&mut rule.term);
            }
        }
        Tactic::Apply { terms, .. } => {
            for t in terms {
                v.term(t);
            }
        }
        Tactic::Intro { pats, .. } => {
            for p in pats {
                v.pat(p);
            }
        }
        Tactic::Cases {
            targets,
            using_term,
            arms,
            pats,
            ..
        } => {
            for t in targets {
                v.term(t);
            }
            opt_term(using_term, v);
            visit_arms(arms, v);
            for p in pats {
                v.pat(p);
            }
        }
        Tactic::Have { pat, ty, value, .. } => {
            opt_pat(pat, v);
            opt_term(ty, v);
            opt_term(value, v);
        }
        Tactic::Case { body, .. } | Tactic::Combinator { body, .. } => v.tactic(body),
        Tactic::Focus(body) => v.tactic(body),
        Tactic::Conv { pattern, body, .. } => {
            opt_term(pattern, v);
            v.tactic(body);
        }
        Tactic::Show(term) => v.term(term),
        Tactic::Calc { steps } => visit_calc(steps, v),
    }
}

/// Visits the ids an item refers to.
pub fn visit_item(item: &mut Item, v: &mut dyn Visitor) {
    for b in &mut item.binders {
        v.binder(b);
    }
    opt_term(&mut item.ty, v);
    opt_term(&mut item.value, v);
    visit_arms(&mut item.arms, v);
    for ctor in &mut item.ctors {
        for b in &mut ctor.binders {
            v.binder(b);
        }
        opt_term(&mut ctor.ty, v);
    }
    for field in &mut item.fields {
        for b in &mut field.binders {
            v.binder(b);
        }
        opt_term(&mut field.ty, v);
        opt_term(&mut field.default, v);
        visit_arms(&mut field.arms, v);
    }
}

fn opt_term(id: &mut Option<TermId>, v: &mut dyn Visitor) {
    if let Some(id) = id {
        v.term(id);
    }
}

fn opt_pat(id: &mut Option<PatId>, v: &mut dyn Visitor) {
    if let Some(id) = id {
        v.pat(id);
    }
}

fn visit_arms(arms: &mut [Arm], v: &mut dyn Visitor) {
    for arm in arms {
        for p in &mut arm.pats {
            v.pat(p);
        }
        match &mut arm.body {
            ArmBody::Term(t) => v.term(t),
            ArmBody::Tactic(t) => v.tactic(t),
            ArmBody::Do(stmts) => visit_do(stmts, v),
        }
    }
}

fn visit_calc(steps: &mut [CalcStep], v: &mut dyn Visitor) {
    for step in steps {
        v.term(&mut step.relation);
        v.term(&mut step.proof);
    }
}

fn visit_do(stmts: &mut [DoStmt], v: &mut dyn Visitor) {
    for stmt in stmts {
        match stmt {
            DoStmt::Break | DoStmt::Continue | DoStmt::Opaque(_) => {}
            DoStmt::Let {
                pat,
                ty,
                value,
                else_branch,
                ..
            }
            | DoStmt::LetArrow {
                pat,
                ty,
                value,
                else_branch,
                ..
            } => {
                v.pat(pat);
                opt_term(ty, v);
                v.term(value);
                if let Some(stmts) = else_branch {
                    visit_do(stmts, v);
                }
            }
            DoStmt::Bind { pat, value } => {
                v.pat(pat);
                v.term(value);
            }
            DoStmt::Reassign { value, .. } => v.term(value),
            DoStmt::Return(term) => opt_term(term, v),
            DoStmt::Expr(term) => v.term(term),
            DoStmt::Match { discrs, arms } => {
                for d in discrs {
                    v.term(d);
                }
                visit_arms(arms, v);
            }
            DoStmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                v.term(cond);
                visit_do(then_branch, v);
                if let Some(b) = else_branch {
                    visit_do(b, v);
                }
            }
            DoStmt::For {
                pat,
                iterable,
                body,
            } => {
                v.pat(pat);
                v.term(iterable);
                visit_do(body, v);
            }
            DoStmt::While { cond, body } => {
                v.term(cond);
                visit_do(body, v);
            }
            DoStmt::Try {
                body,
                catches,
                finally_branch,
            } => {
                visit_do(body, v);
                for c in catches {
                    visit_do(c, v);
                }
                if let Some(f) = finally_branch {
                    visit_do(f, v);
                }
            }
        }
    }
}

/// Collects the ids a node refers to, without changing them.
#[derive(Debug, Default)]
pub struct Collect {
    /// Referenced terms, in order.
    pub terms: Vec<TermId>,
    /// Referenced binders, in order.
    pub binders: Vec<BinderId>,
    /// Referenced patterns, in order.
    pub pats: Vec<PatId>,
    /// Referenced tactics, in order.
    pub tactics: Vec<TacticId>,
}

impl Visitor for Collect {
    fn term(&mut self, id: &mut TermId) {
        self.terms.push(*id);
    }
    fn binder(&mut self, id: &mut BinderId) {
        self.binders.push(*id);
    }
    fn pat(&mut self, id: &mut PatId) {
        self.pats.push(*id);
    }
    fn tactic(&mut self, id: &mut TacticId) {
        self.tactics.push(*id);
    }
}

/// Replaces every id with its position in traversal order.
///
/// Canonicalising this way is what makes structural comparison possible: two
/// nodes with the same shape differ only in which arena slots their children
/// happen to occupy, and this erases exactly that difference.
#[derive(Debug, Default)]
pub(crate) struct Canonicalize {
    next: u32,
}

impl Visitor for Canonicalize {
    fn term(&mut self, id: &mut TermId) {
        *id = TermId::from_raw(self.take());
    }
    fn binder(&mut self, id: &mut BinderId) {
        *id = BinderId::from_raw(self.take());
    }
    fn pat(&mut self, id: &mut PatId) {
        *id = PatId::from_raw(self.take());
    }
    fn tactic(&mut self, id: &mut TacticId) {
        *id = TacticId::from_raw(self.take());
    }
}

impl Canonicalize {
    fn take(&mut self) -> u32 {
        let n = self.next;
        self.next += 1;
        n
    }
}
