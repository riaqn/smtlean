namespace sig

attribute [reducible]
def type := Type

attribute [reducible]
def formula := Prop

attribute [reducible]
def th_holds : Prop → Prop :=  id

def true := true
def false := false

def not := not
def and := and
def or := or
def impl := (->)
def iff := (↔)
def xor := xor
def ifte := ite

def sort := Type

def term : sort → Type := id

def Bool : sort := bool

def clausify_false (x : false) : false := x
def th_let_pf (α : Prop) (x : α) (y : α → false) : false := y x

def p_app := @coe_sort bool coe_sort_bool

-- natural deduction rules; Used for CNF
def iff_symm (α : Prop) : α ↔ α := iff.intro id id
def contra (α : Prop) (a : α) (na : ¬ α): false := na a
def truth : true := true.intro
def not_not_intro (α : Prop) (a : α) : ¬ ¬ α := λ na, na a
def not_not_elim (α : Prop) (x : ¬ ¬ α) : α := classical.by_contradiction x

-- or elimination
def or_elim_1 (α β : Prop) (na : ¬ α) (ab : α ∨ β) : β :=
match ab with
| or.inl a := match na a with end
| or.inr b := b
end

def or_elim_2 (α β : Prop) (nb : ¬ β) (ab : α ∨ β) : α :=
match ab with
| or.inl a := a
| or.inr b := match nb b with end
end

def not_or_elim (α β : Prop) (x : ¬ (α ∨ β)) : ¬ α ∧ ¬ β := and.intro (λ a, x $ or.inl a) (λ b, x $ or.inr b)

-- and elimination
def and_elim_1 (f1 : Prop) (f2 : Prop) (u : f1 ∧ f2) : f1 := u.elim (λ x y, x)
def and_elim_2 (f1 : Prop) (f2 : Prop) (u : f1 ∧ f2) : f2 := u.elim (λ x y, y)
def not_and_elim (α β : Prop) (x : ¬ (α ∧ β)) : ¬ α ∨ ¬ β := match classical.em α with
| or.inl a := or.inr (λ b, x $ and.intro a b)
| or.inr na := or.inl na
end

-- impl elimination
def impl_intro (α β : Prop) (x : α → β) : α → β := x
def impl_elim (α β : Prop) (f : α → β) : ¬ α ∨ β := match classical.em α with
| or.inl a := or.inr $ f a
| or.inr na := or.inl na
end
def not_impl_elim (α β : Prop) (x : ¬ (α → β)) : α ∧ ¬ β := and.intro (classical.by_contradiction $ λ na, x (λ a, match na a with end)) (λ b, x $ λ a, b)

-- iff elimination
def iff_elim_1 (α β : Prop) (x : α ↔ β) : ¬ α ∨ β := match classical.em α with
| or.inl a := or.inr $ x.mp a
| or.inr na := or.inl na
end

def iff_elim_2 (α β : Prop) (x : α ↔ β) : α ∨ ¬ β := match classical.em β with
| or.inl b := or.inl $ x.mpr b
| or.inr nb := or.inr nb
end

def not_iff_elim (α β : Prop) (x : ¬ (α ↔ β)) : α ↔ (¬ β) := iff.intro (λ a b, x $ iff.intro (λ a, b) (λ b, a)) (λ nb, classical.by_contradiction $ λ na, x $ iff.intro (λ a, match na a with end) (λ b, match nb b with end))

-- xor elimination
def xor_elim_1 (α β : Prop) (x : xor α β) : ¬ α ∨ ¬ β := match x with
| or.inl (and.intro a nb) := or.inr nb
| or.inr (and.intro b na) := or.inl na
end

def xor_elim_2 (α β : Prop) (x : xor α β) : α ∨ β := match x with
| or.inl (and.intro a nb) := or.inl a
| or.inr (and.intro b na) := or.inr b
end

def not_xor_elim (α β : Prop) (x : ¬ (xor α β)) : α ↔ β := iff.intro (λ a, classical.by_contradiction $ λ nb, x $ or.inl (and.intro a nb)) (λ b, classical.by_contradiction $ λ na, x $ or.inr (and.intro b na))

-- For theory lemmas
def ast (α β : Prop) (f : α → β) : ¬ α ∨ β := match classical.em α with
| or.inl a := or.inr $ f a
| or.inr na := or.inl na
end

def asf (α β : Prop) (f : ¬ α → β) : α ∨ β := match classical.em α with
| or.inl a := or.inl a
| or.inr na := or.inr $ f na
end


end sig
