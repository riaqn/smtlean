import ..smtlib

import .sig.sat
import .sig.smt
import .sig.th_base

namespace reflect

attribute [reducible]
meta def pvar := string

attribute [reducible]
meta def atom := string

@[derive decidable_eq]
meta structure lit := (var : pvar) (pol : bool)

attribute [reducible]
meta def clause := list lit

meta inductive type
| holds : clause → type
| th_holds : term → type
| term : sort → type

meta structure context :=
(stack : list (pvar × option type)) -- currently we only care the type of clauses
(atoms : rbmap atom pvar)

meta def list.rfind {α β : Type} [decidable_eq β]: list α → (α → β) → β → option (nat ×  α) :=
λ l f b, match l with
| [] := option.none
| (a :: l') := if f a = b then return (0, a) else
               do (n, a) ← list.rfind l' f b,
                  return (n+1, a)
end

-- erase the first one
meta def list.erase1 {α : Type} [decidable_eq α] : list α → α → option (nat × list α) :=
λ l a, match l with
| [] := option.none
| (a' :: l') := if a' = a then return (0, l')
                else do (n, l') ← list.erase1 l' a,
                        return (n + 1, a' :: l')
end

meta def context.push (c : context) (v : pvar) (ty : option type) := context.mk ((v, ty) :: c.stack) c.atoms
meta def context.bind (c : context) (a : atom) (v : pvar):= context.mk c.stack (c.atoms.insert a v)
meta def context.a2v (c : context) (a : atom) : option pvar := c.atoms.find a
meta def context.v2ty (c : context) (v : pvar) : option (nat × option type) := (λ x, (prod.fst x, prod.snd $ prod.snd x) ) <$> list.rfind c.stack prod.fst v
meta def context.v2n (c : context) (v : pvar) : option nat := prod.fst <$> context.v2ty c v

meta def mk_context : context := context.mk [] $ mk_rbmap atom pvar

meta def is_some {α β : Type} :  option α → β → except β α := λ o s, match o with
| option.some o' := except.ok o'
| _ := except.error s
end

attribute [reducible]
meta def error := format

meta def reflect (α : Type) := context → α → except error pexpr
meta def parse (α : Type) := sexp → except error α

meta def app := @expr.app ff
meta def lam := λ v ty t, @expr.lam ff v (binder_info.default) ty t
meta def var := @expr.var ff
meta def xxx := pexpr.mk_placeholder
meta def elet := @expr.elet ff
meta def apps' : list pexpr → pexpr  → pexpr
| [] := id
| (x :: xs) := λ f, apps' xs (app f x)

meta def apps := flip apps'

meta def ref_clause : reflect clause := λ c cl, match cl with
| [] := return ``(false)
| (lit.mk pv tt) :: xs := do n ← is_some (c.v2n pv) "pvar not bound",
                             e ← ref_clause c xs,
                             return $ ``(%%(var n) ∨ %%(e))
| (lit.mk pv ff) :: xs := do n ← is_some (c.v2n pv) "pvar not bound",
                             e ← ref_clause c xs,
                             return $ ``((¬ %%(var n)) ∨ %%(e))
end

def R {α:Prop} (β γ : Prop) : (α ∨ β) → (¬ α ∨ γ) → (β ∨ γ)
| (or.inl a) (or.inl na) := match na a with end
| _ (or.inr c) := or.inr c
| (or.inr b) _ := or.inl b

def Q {α : Prop} (β γ : Prop) : (¬ α ∨ β) → (α ∨ γ) → (β ∨ γ)
| (or.inl na) (or.inl a) := match na a with end
| _ (or.inr c) := or.inr c
| (or.inr b) _ := or.inl b

def or.swap {α β γ : Prop} : α ∨ (β ∨ γ) → β ∨ (α ∨ γ) := (or.assoc.mp) ∘ (or.imp_left (or_comm α β).mp) ∘ (or.assoc.mpr)

-- proves swap n and n+1 doesn't change meaning
meta def gen_swap : nat → pexpr
| 0 := ``(or.swap)
| (n + 1) := ``(or.imp_right %%(gen_swap n))

-- proves pushing n to the left-most doesn't change meaning
meta def gen_push : nat → pexpr
| 0 := ``(id)
| (n + 1) := ``(%%(gen_push n) ∘ %%(gen_swap n))

-- proves 
meta def gen_line : nat → pexpr
| 0 :=``(id)
| (n + 1) := ``(or.assoc.mp ∘ (or.imp_right %%(gen_line n)))

meta structure config :=
(env : environment)

-- mostly option.none except for clauses
meta def ref_proof (cfg : config) : context → sexp → except error (pexpr × option type) := λ c p,

let
is_holds : option type → string → except error clause := (λ ty s, match ty with
| option.some $ type.holds $ cl := except.ok cl
| _ := except.error $ s ++ "expect holds"
end),

as := (λ a v p' (pol : bool),
do (p', ty') ← ref_proof (c.push v option.none) p',
cl ← is_holds ty' "as",
pv ← match c.a2v a with
| option.some pv := return pv
| _ := except.error $ "atom not bound"
end,
let f:= if pol then ``(sig.asf) else ``(sig.ast),
return $ (apps f [xxx, xxx, lam v xxx p'], option.some $ type.holds $ (lit.mk pv pol) :: cl)
),

res := (λ p0 p1 pv pol, do (p0, ty0) ← ref_proof c p0,
(p1, ty1) ← ref_proof c p1,
cl0 ← is_holds ty0 "R ty0",
cl1 ← is_holds ty1 "R ty1",
(n0, cl0') ← is_some (list.erase1 cl0 (lit.mk pv pol)) "R cl0",
(n1, cl1') ← is_some (list.erase1 cl1 (lit.mk pv $ not pol)) "R cl1",
let r := if pol then ``(R) else ``(Q),
return $ (``((false_or _).mp $ %%(gen_push $ cl0.length - 1) $ %%(gen_line $ cl0.length - 1) $ %%(r) _ _ (%%(gen_push n0) %%p0) (%%(gen_push n1) %%p1)), option.some $ type.holds $ cl0' ++ cl1')
),

find_sig : symbol → except error pexpr := (λ f, do let n := mk_str_name "sig" f,
                                                  match cfg.env.get n with
| exceptional.success _  := return $ @expr.local_const ff name.anonymous n binder_info.default xxx
| exceptional.exception _ _ := except.error $ has_to_format.to_format ("theroem not found", f)
end)


in match p with
| . [!"%", ! v, ty, p'] := do (ty, _) ← ref_proof c ty,
                              (p', _) ← ref_proof (c.push v option.none) p',
                              return $ (lam v ty p', option.none)
| . [!"\\", !v, p'] := do (p', _) ← ref_proof (c.push v option.none) p',
                          return $ (lam v xxx p', option.none)
| . [!":", ty, p'] := ref_proof c p' -- actually use the type ascription
| . [!"@", ! v, t, p'] := do (t, _) ← ref_proof c t,
                             (p'_, _) ← ref_proof (c.push v option.none) p',
                             return $ (elet (mk_simple_name v) xxx t p'_, option.none)
| . [!"decl_atom", for, . [!"\\", !pv, . [!"\\", !a, p']]] := do (for, _) ← ref_proof c for,
                                                                (p', _) ← ref_proof ((c.push pv option.none).bind a pv) p',
                                                                return $ (app (lam pv xxx p') for, option.none)
| . [!"satlem", _, _, p0, . [!"\\", !v, p1]] := do (p0, ty0) ← ref_proof c p0,
                                                   (p1, ty1) ← ref_proof (c.push v $ ty0) p1,
                                                   return (``(sig.satlem _ _ %%p0 %%(lam v xxx p1)), ty1)
| . [!"ast", _, _, _, !a, . [!"\\", !v, p']] := as a v p' ff
| . [!"asf", _, _, _, !a, . [!"\\", !v, p']] := as a v p' tt
| . [!"clausify_false", p'] := do (p', _) ← ref_proof c p',
                                  return (``(sig.clausify_false %%(p')), option.some $ type.holds [])
| . [!"satlem_simplify", _, _, _, p0, . [!"\\", !v, p1]] := do (p0, ty0) ← ref_proof c p0,
                                                               (p1, ty1) ← ref_proof (c.push v ty0) p1,
                                                               return (``(sig.satlem_simplify _ _ %%p0 %%(lam v xxx p1)), ty1)
| . [!"R", _, _, p0, p1, !pv] := res p0 p1 pv tt
| . [!"Q", _, _, p0, p1, !pv] := res p0 p1 pv ff
| ! "_" := return (xxx, option.none)
| ! v := match c.v2ty v with
         | option.some (n, ty) := return (var n, ty)
         | option.none := do f ← find_sig v, return (f, option.none)
         end
| . ((! f) :: xs) := do f ← find_sig f,
                        rs ← monad.mapm (ref_proof c) xs,
                        let ps := rs.map (λ x, x.fst),
                        return (apps f ps , option.none)
| _ := except.error $ "unrecognized proof" ++ (to_string p)
end

meta def ref_check (cfg : config) : sexp → except error (pexpr × option type) := λ p,
match p with
| . [!"check", p'] := ref_proof cfg mk_context p'
| _ := except.error "has to start with 'check'"
end


end reflect
