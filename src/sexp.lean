import data.buffer.parser
import .common

universe u

attribute [reducible]
def symbol := string

inductive literal : Type
| num : nat → literal
| str : string → literal

instance : has_to_string literal :=
⟨ λ lit, match lit with
| literal.num n := "<SOME NAT>"
| literal.str s := "\"" ++ s ++ "\""
end
⟩

-- list representation of S-exp
inductive sexp : Type
| symbol : symbol → sexp
| literal : literal → sexp
| list : list sexp → sexp

prefix . :1 := sexp.list
prefix ! :2 := sexp.symbol
prefix # :3 := sexp.literal

class has_from_sexp (α : Type _) :=
(from_sexp {} : sexp → except string α )

export has_from_sexp (from_sexp)

class has_to_sexp (α : Type _) :=
(to_sexp {} : α → sexp)
export has_to_sexp (to_sexp)

-- sexp → string
mutual def sexp_to_string, list_sexp_to_string
with sexp_to_string : sexp → string
| (sexp.literal lit) := to_string lit
| (sexp.symbol s) := s
| (sexp.list l) := "(" ++ (string.intercalate " " (list_sexp_to_string l) ) ++ ")"
with list_sexp_to_string : list sexp → list string
| [ ] := []
| (t :: l') := sexp_to_string t :: list_sexp_to_string l'

instance : has_to_string sexp :=
⟨ sexp_to_string ⟩

#eval (to_string $ . [! "and",  . [! "or", (. [ ]), ! "a"], ! "b"])

namespace parse
open parser

inductive lexicon : Type
| symbol : symbol → lexicon
| literal : literal → lexicon
| left : lexicon
| right : lexicon
| comment : string → lexicon
| whitespaces : lexicon

def parse_whitespace : parser unit := one_of' ['\x09', '\x0a', '\x0d', '\x20']

def parse_comment : parser string :=
do ch ';',
   s ← many $ sat $ λ c, ¬ ((c = '\x0a') || (c = '\x0d')),
   ch '\x0a' <|> ch '\x0d',
   return s.as_string

def parse_letter : parser char := sat $ λ c, (c ≥ 'a') && (c ≤ 'z') || (c ≥ 'A') && (c ≤ 'Z')

def parse_digit : parser char := sat $ λ c, (c ≥ '0') && (c ≤ '9')

def parse_punc : parser char := one_of ['~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/', ':', '\\']

def parse_symbol : parser symbol :=
do s ← parse_letter <|> parse_punc,
   l ← many (parse_letter <|> parse_digit <|> parse_punc),
   return (s :: l).as_string

-- TODO: parse_literal
def parse_lexicon : parser lexicon :=
  (lexicon.symbol <$> parse_symbol) <|> (ch '(' >> return lexicon.left) <|> (ch ')' >> return lexicon.right) <|> (lexicon.comment <$> parse_comment) <|> ((many1 parse_whitespace) >> return lexicon.whitespaces)

def parse_lexicons : parser (list lexicon) :=
do many parse_lexicon

--TODO: make all the parsing function in (stateT parse_state (either parse_error) sexp)'
attribute [reducible]
def stack (α : Type u) : Type u := list α

def conclude' {α : Type u} : stack α → list α → list α
| (x :: xs) l := conclude' xs (x :: l)
| [] l := l

def conclude {α : Type u} : stack α → list α := assume s, conclude' s list.nil

attribute [reducible]
def parse_state : Type := stack (stack sexp) -- the stack of occuring lists

def conclude_list : parse_state → except parse_error parse_state
| (l0 :: l1 :: ls) := except.ok $ ((sexp.list (conclude l0) :: l1)::ls)
| _ := except.error $ "stack too shallow to conclude"

def introduce_list : parse_state → except parse_error parse_state :=
assume p, except.ok $ ([] :: p)

def append_list (e : sexp) :  parse_state  → except parse_error parse_state 
| (l :: ls) := except.ok $ ((e :: l) :: ls)
| _ := except.error $ "no list to append to"

def sexp_from_lexicons : list lexicon → parse_state → except parse_error sexp
| (l :: ls) p := match l with
                 | lexicon.whitespaces := sexp_from_lexicons ls p
                 | lexicon.comment _ := sexp_from_lexicons ls p
                 | lexicon.symbol s :=  append_list (sexp.symbol s) p >>= sexp_from_lexicons ls
                 | lexicon.literal lit := append_list (sexp.literal lit) p >>= sexp_from_lexicons ls
                 | lexicon.left := introduce_list p >>= sexp_from_lexicons ls
                 | lexicon.right := conclude_list p >>= sexp_from_lexicons ls
                 end
| ([]) p := do
  match p with
  | [] := except.error "too many right parenthesis"
  | [l] := match l with
           | [] := except.error "there is nothing"
           | [e] := except.ok e
           | _ := except.error (string.append  "there is too many; wrap it with () if you mean a list\n" (l.to_string))
           end
  | l := except.error $ string.append "too many left parenthesis\n" (l.to_string)
  end

instance : has_from_buffer sexp :=
⟨λ cb,  (match run parse_lexicons cb with
| sum.inl e := except.error e
| sum.inr a := except.ok a
end
) >>= (λ ls, sexp_from_lexicons ls [[]])
⟩

end parse

#eval to_string (from_string "(and (or () b  )  c)" : except parse_error sexp)
