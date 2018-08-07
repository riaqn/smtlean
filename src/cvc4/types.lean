import ..sexp
import ..smtlib
-- variables as in literals
attribute [reducible]
def var := string

attribute [reducible]
def error := string

@[derive decidable_eq]
inductive lit
| pos : var → lit
| neg : var → lit

def clause := list lit

inductive rq
| r -- pos and neg
| q -- neg and pos

inductive res : Type
| node : rq → res → res → var → res
| leaf : string → res

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

-- let var be a proof of term, without actually proving it
structure th_let_pf :=
(var : var)
(term : term)

structure decl_atom :=
(exp : sexp) -- is of type term
(atom : var)
(var : var)

structure proof : Type :=
(ass_term : list ass_term)
(ass_th_holds : list ass_th_holds)
(lat : list lat)
(th_let_pf : list th_let_pf)
(decl_atom : list decl_atom)
(sat_lem : list satlem)
(resolutions : res)

