-- the LFSC proofs specifically from CVC4
import ..sexp
import ..smtlib
import .types

-- set_option trace.eqn_compiler.elim_match true

universes u v

namespace parse
def error := string
attribute [reducible]
def parser (α : Type) := sexp → except error (α × sexp)
attribute [reducible]
def matcher (α : Type) := sexp → except error α

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

def string_to_qr : string → except string rq
| "Q" := except.ok rq.q
| "R" := except.ok rq.r
| _ := except.error "neither Q or R"

--TODO: remove meta
-- lean's induction elaborator is very weak, to make this def without meta, we will need a parsing state along with recursing
meta mutual def match_res_list, match_res
with match_res_list : list sexp → except string (res string)
| [! rq_, ! "_", ! "_", t0, t1, ! v] := res.node <$> (string_to_qr rq_) <*> (match_res t0) <*> (match_res t1) <*> (except.ok v)
| _ := except.error "not resolution"
with match_res : sexp → except string (res string)
| (. l) := match_res_list l
| (! v) := except.ok $ res.leaf v
| (_) := except.error "not resolution"

def match_header : parser unit
| (. [! "proof", t]) := except.ok $ ((), t)
| (_) := except.error "unrecognized header"

meta def match_proof : matcher (proof string) := λ t, do
  (_, t) ← match_header t,
  (ass_term_, t) ← many match_ass_term t,
  (ass_th_hold_, t) ← many match_ass_th_holds t,
  (lat_, t) ← many match_lat t,
  (th_let_pf_, t) ← many match_th_let_pf t,
  (decl_atom_, t) ← many match_decl_atom t,
  (satlem_, t) ← many match_satlem t,
  res_ ← match_res t,
  return $ proof.mk ass_term_ ass_th_hold_ lat_ th_let_pf_ decl_atom_ satlem_ res_

meta instance : has_from_sexp (proof string) :=
⟨ match_proof ⟩

end parse
