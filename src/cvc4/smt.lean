
namespace sig
def and_elim_1 (f1 : Prop) (f2 : Prop) (u : f1 ∧ f2) : f1 := u.elim (λ x y, x)
def and_elim_2 (f1 : Prop) (f2 : Prop) (u : f1 ∧ f2) : f2 := u.elim (λ x y, y)
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

def not_not_intro (α : Prop) (a : α) : ¬ ¬ α := λ na, na a

def impl_elim (α β : Prop) (f : α → β) : ¬ α ∨ β := match classical.em α with
| or.inl a := or.inr $ f a
| or.inr na := or.inl na
end

end sig
