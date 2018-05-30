import system.io

open io.proc

universe u
variable α : Sort u
variable r : α → α → Prop

inductive binary : Type
| and
| or

instance binary_to_string : has_to_string binary :=
⟨ λ op, match op with | (binary.and) := "and" | (binary.or) := "or" end ⟩


inductive unary : Type
| not

instance : has_to_string unary :=
⟨λ op : unary, match op with | unary.not := "not" end⟩

inductive term : Type
| const : bool → term
| binary : binary → term → term → term
| unary : unary → term → term

inductive cmd : Type
| assert : term → cmd
| check_sat : cmd

-- binary tree representation of S-expression
inductive sexp : Type
| nil : sexp
| leaf : string → sexp
| node : sexp → sexp → sexp

-- list representation of S-exp
inductive sexp' : Type
| atom : string → sexp'
| list : list sexp' → sexp'

prefix . :1 := sexp'.list
prefix ! :2 := sexp'.atom

def sexp'_to_sexp : sexp' → sexp
| (sexp'.atom s) := sexp.leaf s
| (sexp'.list []) := sexp.nil
| (sexp'.list (list.cons e l')) := sexp.node (sexp'_to_sexp e)  (sexp'_to_sexp $ sexp'.list l')

def term2sexp' : term → sexp'
| (term.const ff) := ! "false"
| (term.const tt) := ! "true"
| (term.binary op t0 t1) := . [! to_string op, term2sexp' t0, term2sexp' t1]
| (term.unary op t') := . [! to_string op, term2sexp' t']

def sexp_to_string : sexp → bool → string
| (sexp.nil) b := cond b ")" "()"
| (sexp.leaf s) b := cond b " " "" ++ s
| (sexp.node e0 e1) tt := " " ++ (sexp_to_string e0 ff) ++ (sexp_to_string e1 tt)
| (sexp.node e0 e1) ff := "(" ++ (sexp_to_string e0 ff) ++ (sexp_to_string e1 tt)

def cmd2sexp : cmd → sexp'
| (cmd.assert t) := . [! "assert" ,  term2sexp' t]
| (cmd.check_sat) := . [! "check-sat"]

instance : has_to_string sexp :=
⟨ λ e, sexp_to_string e ff⟩

instance : has_to_string sexp' :=
⟨λ e, to_string $ sexp'_to_sexp e⟩

#eval (to_string $ . [! "and",  . [! "or", (. [ ]), ! "a"], ! "b"])

instance : has_to_string cmd :=
⟨λ c, to_string $ cmd2sexp c⟩


def parse_error := string
instance :  has_to_string parse_error :=
⟨λ e : string, to_string e⟩

def stack (α : Type u) : Type u := list α

def conclude' {α : Type u} : stack α → list α → list α
| (x :: xs) l := conclude' xs (x :: l)
| [] l := l

def conclude {α : Type u} : stack α → list α := assume s, conclude' s list.nil

structure parse_state : Type :=
  (atom : stack char) -- the occuring atom in reverse order
  (list : stack (stack sexp')) -- the stack of occuring lists

instance except_has_to_string {α β : Type} [has_to_string α] [has_to_string β] : has_to_string (except α β) :=
⟨λ e, match e with
| except.error a := "ERROR : " ++ to_string a
| except.ok b := "OK : " ++ to_string b
end
⟩


--TODO: make all the parsing function in (stateT parse_state (either parse_error) sexp)'

-- append a new char to the occuring atom
def append_atom : parse_state → char → parse_state := assume p c, parse_state.mk (c :: p.atom) p.list

-- end the occuring atom
-- nothing if it's empty
def conclude_atom : parse_state → except parse_error parse_state :=
assume p, match p.list with
| l :: ls := except.ok $ parse_state.mk [] (( let atom := conclude p.atom in
    --catch : empty list has size 1
                                 if atom.sizeof > 1 then ((sexp'.atom (string_imp.mk atom)) :: l)
                                 else l) :: ls)
| [] := except.error "no list to conlude into"
end  

def conclude_list : parse_state → except parse_error parse_state :=
assume p,
do
  p' <- conclude_atom p,
  match p'.list with
  | l0 :: l1 :: ls := except.ok $ parse_state.mk (p'.atom) ((sexp'.list (conclude l0) :: l1)::ls)
  | _ := except.error $ "stack too shallow to conclude"
  end

def introduce_list : parse_state → except parse_error parse_state :=
assume p,
do
  p' <- conclude_atom p,
  except.ok $ parse_state.mk (p'.atom) ([] :: p'.list)

def sexp'_from_string : list char → parse_state → except parse_error sexp'
| (c :: s') p := match c with
                 | ' ' := conclude_atom p >>= sexp'_from_string s'
                 | '(' := introduce_list p >>= sexp'_from_string s'
                 | ')' := conclude_list p >>= sexp'_from_string s'
                 | _ := return (append_atom p c) >>= sexp'_from_string s'
                 end 
| ([]) p := do
  p' <- conclude_atom p,
  match p'.list with
  | [] := except.error "maybe too many right paratheis"
  | [l] := match l with
           | [] := except.error "there is nothing"
           | [e] := except.ok e
           | _ := except.error (string.append  "there is too many; wrap it with () if you mean a list\n" (l.to_string))
           end
  | l := except.error $ string.append "maybe too many left paranthesis\n" (l.to_string)
  end

class has_from_string (α : Type _) :=
(from_string : string → except parse_error α)

instance sexp'_have_from_string : has_from_string sexp' :=
⟨λ s, sexp'_from_string s.data $ parse_state.mk [] [[]]⟩

#eval (to_string $ (@has_from_string.from_string sexp' sexp'_have_from_string "(and (or () b  )  c)"))

def solve (ts : list term) : io string :=
do child <- io.proc.spawn{
    cmd := "cvc4",
    args := ["--smtlib", "--no-interactive"],
    stdin := io.process.stdio.piped,
    stdout := io.process.stdio.piped,
    stderr := io.process.stdio.inherit
   },

  let stdin := child.stdin,
  let stdout := child.stdout,

  let write_cmd := λ c : cmd, io.fs.write stdin $ string.to_char_buffer $ to_string c ++ "\n",

  monad.mapm' (λ t, write_cmd $ cmd.assert t) ts,
  write_cmd $ cmd.check_sat,

  buffer.to_string <$> io.fs.get_line stdout

