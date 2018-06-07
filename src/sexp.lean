import .common

universe u

-- list representation of S-exp
inductive sexp : Type
| atom : string → sexp
| list : list sexp → sexp

prefix . :1 := sexp.list
prefix ! :2 := sexp.atom

class has_from_sexp (α : Type _) :=
(from_sexp {} : sexp → except string α )

export has_from_sexp (from_sexp)

class has_to_sexp (α : Type _) :=
(to_sexp {} : α → sexp)
export has_to_sexp (to_sexp)

-- sexp → string
mutual def sexp_to_string, list_sexp_to_string
with sexp_to_string : sexp → string
| (sexp.atom s) := s
| (sexp.list l) := "(" ++ (string.intercalate " " (list_sexp_to_string l) ) ++ ")"
with list_sexp_to_string : list sexp → list string
| [ ] := []
| (t :: l') := sexp_to_string t :: list_sexp_to_string l'

instance : has_to_string sexp :=
⟨ sexp_to_string ⟩



-- string → sexp
--TODO: make all the parsing function in (stateT parse_state (either parse_error) sexp)'
attribute [reducible]
def stack (α : Type u) : Type u := list α

def conclude' {α : Type u} : stack α → list α → list α
| (x :: xs) l := conclude' xs (x :: l)
| [] l := l

def conclude {α : Type u} : stack α → list α := assume s, conclude' s list.nil

structure parse_state : Type :=
(atom : stack char) -- the occuring atom in reverse order
(list : stack (stack sexp)) -- the stack of occuring lists

-- append a new char to the occuring atom
def append_atom : parse_state → char → parse_state := assume p c, parse_state.mk (c :: p.atom) p.list

-- end the occuring atom
-- nothing if it's empty
def conclude_atom : parse_state → except parse_error parse_state :=
assume p, match p.list with
| l :: ls := except.ok $ parse_state.mk [] (( let atom := conclude p.atom in
    --catch : empty list has size 1
                                 if atom.sizeof > 1 then ((sexp.atom (string_imp.mk atom)) :: l)
                                 else l) :: ls)
| [] := except.error "no list to conlude into"
end  

def conclude_list : parse_state → except parse_error parse_state :=
assume p,
do
  p' <- conclude_atom p,
  match p'.list with
  | l0 :: l1 :: ls := except.ok $ parse_state.mk (p'.atom) ((sexp.list (conclude l0) :: l1)::ls)
  | _ := except.error $ "stack too shallow to conclude"
  end

def introduce_list : parse_state → except parse_error parse_state :=
assume p,
do
  p' <- conclude_atom p,
  except.ok $ parse_state.mk (p'.atom) ([] :: p'.list)

def sexp_from_string : list char → parse_state → except parse_error sexp
| (c :: s') p := match c with -- FIXME: duplication
                 | ' ' := conclude_atom p >>= sexp_from_string s'
                 | '\t' := conclude_atom p >>= sexp_from_string s'
                 | '\n' := conclude_atom p >>= sexp_from_string s'
                 | '\x0d' := conclude_atom p >>= sexp_from_string s'
                 | '(' := introduce_list p >>= sexp_from_string s'
                 | ')' := conclude_list p >>= sexp_from_string s'
                 | _ := return (append_atom p c) >>= sexp_from_string s'
                 end 
| ([]) p := do
  p' <- conclude_atom p,
  match p'.list with
  | [] := except.error "too many right parenthesis"
  | [l] := match l with
           | [] := except.error "there is nothing"
           | [e] := except.ok e
           | _ := except.error (string.append  "there is too many; wrap it with () if you mean a list\n" (l.to_string))
           end
  | l := except.error $ string.append "too many left parenthesis\n" (l.to_string)
  end


instance sexp_havs_from_string : has_from_string sexp :=
⟨λ s, sexp_from_string s.data $ parse_state.mk [] [[]]⟩
