-- the LFSC proofs specifically from CVC4


import .sexp
import .smtlib
-- set_option trace.eqn_compiler.elim_match true

namespace cvc4

attribute [reducible]
def var := string

attribute [reducible]
def error := string

@[derive decidable_eq]
inductive lit
| pos : var → lit
| neg : var → lit


def clause := list lit

inductive resolution : Type
| Q : resolution × resolution → var → resolution
| R : resolution × resolution → var → resolution
| atom : var → resolution

-- ast or asf
structure ast_f : Type :=
(tf : bool)
(atom : var)
(var : var)

structure satlem :=
(as : list ast_f)
(arg : sexp)
(var : var)

structure ass_term :=
(var : var)
(sort : sort)

structure ass_th_holds :=
(var : var)
(term : term)

structure lat :=
(var : var)
(term : term)

structure th_let_pf :=
(var : var)
(term : term)

structure decl_atom :=
(exp : sexp)
(atom : var)
(var : var)

attribute [reducible]
def parser (α : Type) := sexp → except error (α × sexp)
attribute [reducible]
def matcher (α : Type) := sexp → except error α

structure proof : Type :=
  (ass_term : list ass_term)
  (ass_th_holds : list ass_th_holds)
  (lat : list lat)
  (th_let_pf : list th_let_pf)
  (decl_atom : list decl_atom)
  (sat_lem : list satlem)
  (resolutions : resolution)

def match_ass_term : parser ass_term
| (. [! "%", ! v, . [! "term", ! s], t]) := except.ok (ass_term.mk v s, t)
| (_) := except.error "not ass_term"

def match_ass_th_holds : parser ass_th_holds
| (. [! "%", ! v, . [! "th_holds", t], t']) := prod.mk <$> (ass_th_holds.mk v <$> (from_sexp t)) <*>  return t'
| (_) := except.error "not th_holds"

def match_lat : parser lat
| (. [! "@", ! v, t, t']) := prod.mk <$> (lat.mk v <$> (from_sexp t)) <*> return t'
| (_) := except.error "not lat"

def match_th_let_pf : parser th_let_pf
| (. [! "th_let_pf", ! "_", . [! "trust_f", t], . [! "\\", ! v, t']]) := prod.mk <$> (th_let_pf.mk v <$> (from_sexp t)) <*> return t'
| (_) := except.error "not th_let_pf"

def match_decl_atom : parser decl_atom
| (. [! "decl_atom", e, . [! "\\", ! v, . [! "\\", ! a, t]]]) := except.ok (decl_atom.mk e v a, t)
| (_) := except.error "not decl_atom"

def match_ast_f : parser ast_f
| (. [! s, ! "_", ! "_", ! "_", ! a, . [! "\\", ! v, t]]) := match s with
| "ast" := except.ok (ast_f.mk true a v, t)
| "asf" := except.ok (ast_f.mk false a v, t)
| _ := except.error "not ast nor asf"
end
| (_) := except.error "not ast nor asf"

def foldr_core {α β : Type} (f : α → β → β) (p : parser α) (b : β) : ∀ (reps : ℕ), parser β
| 0 := λ e, except.error "too deep recursion"
| (reps+1) := λ e, (do (a, e') ← p e, (b, e'') ← foldr_core reps e', return $ (f a b, e''))

mutual def size_of_list_sexp, size_of_sexp
with size_of_list_sexp : list sexp → ℕ
| [] := 1
| (e :: l) := size_of_sexp e + size_of_list_sexp l
with size_of_sexp : sexp → ℕ
| (! _) := 1
| . l := size_of_list_sexp l
| # _ := 1

def foldr {α β : Type} (f : α → β → β) (p : parser α) (b : β) : parser β :=
λ e, foldr_core f p b (size_of_sexp e) e

-- match until not longer match
def many {α : Type} (p : parser α) :  parser (list α) :=
foldr list.cons p []

def match_satlem : parser satlem
| (. [! "satlem", ! "_", ! "_", t0, . [! "\\", ! v, t1]]) := do
  (l, arg) ← many match_ast_f t0,
  return (satlem.mk l arg v, t1)
| (_) := except.error "not satlem"

def match_resolution : matcher resolution
| (. [! q_r, ! "_", ! "_", t0, t1, ! v]) := (do
  r0 ← match_resolution t0,
  r1 ← match_resolution t1,
  match q_r with
  | "Q" := (except.ok $ resolution.Q (r0, r1) v : except string resolution)
  | "R" := (except.ok $ resolution.R (r0, r1) v : except string resolution)
  | _ := (except.error "not resolution" : except string resolution)
  end)
| (_) := except.error "not resolution"
end cvc4
