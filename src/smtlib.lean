import system.io
import .sexp
import .common

open io.proc

universe u

structure declare : Type :=
  (symbol : string)
  (sort : string)

attribute [reducible]
def sort := string

-- term as in smtlib
inductive term : Type
| literal : literal → term
| symbol : symbol → term
| app : symbol → list term → term -- application


-- a value assignment in model
structure value :=
(symbol : symbol)
(sort : sort)
(term : term)

-- a model is a list of assignments
def model := list value

inductive cmd : Type
| assert : term → cmd
| check_sat : cmd
| exit : cmd
| set_logic : string -> cmd
| declare_const : declare -> cmd
| get_model : cmd
| get_proof : cmd


mutual def term_from_sexp, list_term_from_sexp
with term_from_sexp : sexp → except string term 
| (! s) := except.ok $ term.symbol s
| (# lit) := except.ok $ term.literal lit
| (. (! func) :: l) := term.app func <$> monad.sequence (list_term_from_sexp l)
| _ := except.error "doesn't seem like a term"
with list_term_from_sexp : list sexp → list (except string term)
| [ ] := []
| (e :: l') := term_from_sexp e :: list_term_from_sexp l'

instance : has_from_sexp string :=
⟨ λ e, match e with
| ! x := except.ok x
| _ := except.error "doesn't look like a string"
end
⟩

instance : has_from_sexp term :=
⟨ term_from_sexp ⟩

instance : has_from_sexp value :=
⟨ λ e, match e with
| . [ ! "define-fun", symbol, . [], sort, term] := value.mk <$> (from_sexp symbol) <*>  (from_sexp sort) <*> (from_sexp term)
| _ := except.error "doesn't looks like a assignment"
end
⟩

instance : has_from_sexp model :=
⟨ λ e, match e with
| . (! "model") :: l := monad.sequence $ l.map from_sexp
| _ := except.error "doesn't seem like a model"
end
⟩

mutual def term_to_sexp, list_term_to_sexp
with term_to_sexp : term → sexp
| (term.literal l) := # l
| (term.symbol i) := ! i
| (term.app f l) := . (! f) :: list_term_to_sexp l
with list_term_to_sexp : list term → list sexp
| [ ] := [ ]
| (t :: l') := term_to_sexp t :: list_term_to_sexp l'

instance : has_to_sexp term :=
⟨ term_to_sexp ⟩

instance : has_to_sexp value :=
⟨ λ v, . [ ! v.symbol, ! v.sort, to_sexp v.term ]⟩ 

instance : has_to_sexp model :=
⟨ λ m, . ( (! "model") :: m.map to_sexp )⟩

instance has_to_string_via_sexp {α : Type } [has_to_sexp α] : has_to_string α :=
⟨ λ a, to_string $ to_sexp a ⟩

instance has_from_buffer_via_sexp {α : Type _} [has_from_sexp α] : has_from_buffer α :=
⟨ λ s, do
  e ← from_buffer s,
  from_sexp e
⟩

def cmd_to_sexp : cmd → sexp
| (cmd.assert t) := . [! "assert" ,  term_to_sexp t]
| (cmd.check_sat) := . [! "check-sat"]
| (cmd.exit) := . [! "exit"]
| (cmd.set_logic s) := . [! "set-logic", ! s]
| (cmd.declare_const d) := . [! "declare-const", ! d.symbol, ! d.sort ]
| (cmd.get_model) := . [! "get-model"]
| (cmd.get_proof) := . [! "get-proof"]

instance : has_to_sexp cmd :=
⟨ cmd_to_sexp ⟩


attribute [reducible]
def proof := sexp

def solve_type := io (except parse_error (except proof model))

def solve (declares : list declare) (asserts : list term) : solve_type := 
do child ← io.proc.spawn{
    cmd := "cvc4",
    args := ["--lang=smt2.6", "--no-interactive", "--produce-models", "--proof"],
    stdin := io.process.stdio.piped,
    stdout := io.process.stdio.piped,
    stderr := io.process.stdio.inherit
   },

  let stdin := child.stdin,
  let stdout := child.stdout,

  -- yes you need to flush - a trick that costed me two hours
  let write_cmd := λ c : cmd, (io.fs.put_str_ln stdin $ to_string c) >> io.fs.flush stdin,

  write_cmd $ cmd.set_logic "QF_LIA",
  monad.mapm' (λ d, write_cmd $ cmd.declare_const d) declares,
  monad.mapm' (λ t, write_cmd $ cmd.assert t) asserts,

  write_cmd $ cmd.check_sat,
  sat ← buffer.to_string <$> io.fs.get_line stdout,
  r ← match sat with
  | "sat\n" := do
    write_cmd $ cmd.get_model,
    io.fs.close stdin,
    cb ← io.fs.read_to_end stdout,
    let model' := (from_buffer cb : except parse_error model),
    match model' with
    | except.ok m := (return $ except.ok $ except.ok m : solve_type)
    | except.error e := (return $ except.error e : solve_type)
    end
  | "unsat\n" := do
    write_cmd $ cmd.get_proof,
    io.fs.close stdin,
    cb <- io.fs.read_to_end stdout,
    io.put_str_ln cb.to_string,
    let prf' := (from_buffer cb : except parse_error sexp),
    match prf' with
    | except.ok prf := (return $ except.ok $ except.error prf : solve_type)
    | except.error e := (return $ except.error e : solve_type)
    end
  | _ := do
  write_cmd $ cmd.exit,
  io.fs.close stdin,
  return $ except.error $ string.append "strange satisfiability "  sat
  end,
  io.fs.close stdout,

  _ ← io.proc.wait child,
  return r

def test_solve : io unit :=
do
  r ← solve [] [term.symbol "false"],
  io.put_str_ln $ to_string r

#eval test_solve
