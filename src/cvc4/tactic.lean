
import ..smtlib
import .solve
import .reflect


@[inline] def bimpl : bool → bool → bool
| tt ff  := ff
| _ _ := tt

def b2p := reflect.p_app

meta def prop_to_formula  : expr → tactic term := λ t, match t with
| `(%%(t0) → %%(t1)) := term.app "=>" <$> monad.sequence [prop_to_formula t0, prop_to_formula t1]
| `(%%(t0) ∧ %%(t1)) := term.app "and" <$> monad.sequence [prop_to_formula t0, prop_to_formula t1]
| `(%%(t0) ∨ %%(t1)) := term.app "or" <$> monad.sequence [prop_to_formula t0, prop_to_formula t1]
| `(¬ %%(t')) := term.app "not" <$> monad.sequence [prop_to_formula t']
| `(coe_sort %%(t')) := prop_to_formula t'
| `(false) := return $ term.symbol "false"
| `(true) := return $ term.symbol "true"
| expr.local_const n m bi ty := return $ term.symbol m.to_string
| _ := tactic.fail ("unrecognized prop", t)
end

meta def target_to_query : expr → tactic query := λ t, match t with
| expr.pi n bi ty t' := do sr ← match ty with
                           | `(bool) := return $ option.some "Bool"
                           | _ := do return $ option.none
                           end,
                           match sr with
                           | option.some sr := do _ ← tactic.intro n,
                                                  v ← tactic.mk_local' n bi ty,
                                                  let t' := t'.instantiate_var v,
                                                  k ← target_to_query t',
                                                  return $ query.mk ((declare.mk n.to_string sr) :: k.declares) k.asserts
                           | option.none := do k ← prop_to_formula t,
                                               return $ query.mk [] [term.app "not" [k]]
                           end
| _ := do k ← prop_to_formula t,
          return $ query.mk [] [term.app "not" [k]]
end

meta def prove : tactic unit :=
do tg ← tactic.target,
   q ← target_to_query tg,
   r ← tactic.unsafe_run_io $ solve q,
   match r with
   | except.error e := tactic.fail e
   | except.ok (except.ok model) := tactic.fail $ to_string model
   | except.ok (except.error proof) := match reflect.ref_check proof with
                                    | except.error e := tactic.fail e
                                    | except.ok (t, _) := do
                                    tactic.to_expr ``(classical.by_contradiction) >>= tactic.apply,
                                    tactic.to_expr t >>= tactic.apply,
                                    tactic.repeat $ (do _ ← tactic.apply `(true.intro), return ())
                                    end
   end


def test : (∀ (a: bool) (b : bool), ¬ (a ∧ ¬ b ∧ (a → b))) := by do prove
