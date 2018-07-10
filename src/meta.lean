universes u
attribute [reducible]
def var := string

@[derive decidable_eq]
inductive lit
| pos : var → lit
| neg : var → lit

def clause := list lit

meta inductive rq
| r -- pos and neg
| q -- neg and pos

meta inductive res
| leaf : expr → res
| node : rq → res × res → var → res

meta def list_at {α : Type u} : nat → list α → α
| 0 (x :: xs) := x
| (n + 1) (x :: xs) := list_at n xs
| _ _ := undefined_core "list_at: too short"

meta def list_len {α : Type u} : list α → nat
| [] := 0
| (x :: xs) := list_len xs + 1

meta def list_del {α : Type u} : nat → list α → list α
| 0 (x :: xs) := xs
| (n + 1) (x :: xs) := x :: (list_del n xs)
| _ _ := undefined_core "list_del: too short"

meta def list_app {α : Type u} : list α → list α → list α
| []
l := l
| (x :: xs) l := x :: (list_app xs l)

meta def list_find' {α : Type u} (x : α) [decidable_eq α]: nat → list α → nat
| _ [] := undefined_core "list_find: too short"
| n (y :: ys) := if x = y then n else list_find' (n + 1) ys

meta def list_find {α : Type u} (x : α) [decidable_eq α]: list α → nat := list_find' x 0

def dis_comm {α β γ : Prop} : α ∨ (β ∨ γ) → β ∨ (α ∨ γ)
| (or.inl a) := or.inr $ or.inl a
| (or.inr (or.inl b)) := or.inl b
| (or.inr (or.inr c)) := or.inr $ or.inr c

def dis_cong {α β γ : Prop} : (β → γ) → α ∨ β  → α ∨ γ
| _ (or.inl a) := or.inl a
| f (or.inr b) := or.inr $ f b

def dis_false {α : Prop} : false ∨ α → α
| (or.inl f) := match f with end
| (or.inr a) := a

def dis_assoc {α β γ : Prop} : (α ∨ β) ∨ γ → α ∨ (β ∨ γ)
| (or.inl $ or.inl a) := or.inl a
| (or.inl $ or.inr b) := or.inr $ or.inl b
| (or.inr c) := or.inr $ or.inr c

-- (gen_swap n) proves swaping n and n+1 doesn't change the meaning of clause
meta def gen_swap : nat → pexpr
| 0 := ``(dis_comm)
| (n + 1) := ``(dis_cong %%(gen_swap n))

-- (gen_push n) proves pushing n to the first literal doesn't change meaning
meta def gen_push : nat → pexpr
| 0 := ``(id)
| (n + 1) := ``(%%(gen_push n) ∘ %%(gen_swap n) )

meta def gen_line : nat → pexpr
| 0 := ``(id)
| (n + 1) := ``(dis_assoc ∘ (dis_cong %%(gen_line n)))

def cl_R {α β γ : Prop} : (α ∨ β) → (¬ α ∨ γ) → (β ∨ γ)
| (or.inl a) (or.inl na) := match na a with end
| _ (or.inr c) := or.inr c
| (or.inr b) _ := or.inl b

def cl_Q {α β γ : Prop} : (¬ α ∨ β) → (α ∨ γ) → (β ∨ γ)
| (or.inl na) (or.inl a) := match na a with end
| _ (or.inr c) := or.inr c
| (or.inr b) _ := or.inl b

meta def gen_res (cls : rbmap expr clause) : res → pexpr × clause
| (res.leaf v) := match cls.find_entry v with
                    | option.none := undefined_core "wrong"
                    | option.some (v, cl) := (``(%%v), cl)
                    end
| (res.node rq_ (r0, r1) v) := let (p0, cl0) := gen_res r0,
                            (p1, cl1) := gen_res r1,
                            (n0, n1) := (match (rq_ : rq) with
                                         | rq.r := (list_find (lit.pos v) cl0, list_find (lit.neg v) cl1)
                                         | rq.q := (list_find (lit.neg v) cl0, list_find (lit.pos v) cl1)
                                        end : (nat × nat))
                        in
                          (``(dis_false $ %%(gen_push (list_len cl0 - 1)) $ %%(gen_line (list_len cl0 - 1)) $ cl_R (%%(gen_push n0) %%p0) (%%(gen_push n1) %%p1)), list_app (list_del n0 cl0)  (list_del n1 cl1))

def test_gen_res {α β γ : Prop} : (α ∨ (γ ∨ false)) → (β ∨ (¬ γ ∨ false)) → (¬ α ∨ false) → (¬ β ∨ false) → false :=
by do 
  v0 ← tactic.intro `p0,
  v1 ← tactic.intro `p1,
  v2 ← tactic.intro `p2,
  v3 ← tactic.intro `p3,
  let m := ((((mk_rbmap expr clause).insert v0 [lit.pos "α", lit.pos "γ"]).insert v1 [lit.pos "β", lit.neg "γ"]).insert v2 [lit.neg "α"]).insert v3 [lit.neg "β"],
  let r := res.node rq.r ((res.node rq.r ((res.node rq.r (res.leaf v0, res.leaf v1) "γ"), (res.leaf v2)) "α"), (res.leaf v3)) "β",
  let k := gen_res m r,
  let p := k.fst,
  (tactic.to_expr p) >>= tactic.apply
