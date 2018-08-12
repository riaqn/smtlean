
import ..smtlib
import .solve
import .reflect


@[inline] def bimpl : bool → bool → bool
| tt ff  := ff
| _ _ := tt

def b2p := reflect.p_app

meta def prop_to_formula  : list declare → expr → tactic term := λ d t, match t with
| `(%%(t0) → %%(t1)) := term.app "=>" <$> monad.sequence [prop_to_formula d t0, prop_to_formula (declare.mk "" "" :: d) t1]
| `(%%(t0) ∧ %%(t1)) := term.app "and" <$> monad.sequence [prop_to_formula d t0, prop_to_formula d t1]
| `(%%(t0) ∨ %%(t1)) := term.app "or" <$> monad.sequence [prop_to_formula d t0, prop_to_formula d t1]
| `(¬ %%(t')) := term.app "not" <$> monad.sequence [prop_to_formula d t']
| `(coe_sort %%(t')) := prop_to_formula d t'
| `(false) := return $ term.symbol "false"
| `(true) := return $ term.symbol "true"
| expr.local_const n m bi ty := return $ term.symbol n.to_string
| expr.var i := match d.nth i with
                | option.none := tactic.fail ("unbound", i)
                | option.some k := return $ term.symbol k.symbol
                end
| _ := tactic.fail ("unrecognized prop", t)
end

meta def target_to_query : list declare → expr → tactic query := λ d t, match t with
| expr.pi n bi ty t' := do sr ← match ty with
                           | `(bool) := return $ option.some "Bool"
                           | _ := do return $ option.none
                           end,
                           match sr with
                           | option.some sr := do _ ← tactic.intro n,
                                                  target_to_query (declare.mk n.to_string sr :: d) t'
                           | option.none := do k ← prop_to_formula d t,
                                               return $ query.mk d.reverse [term.app "not" [k]]
                           end
| _ := do k ← prop_to_formula d t,
          return $ query.mk d.reverse [term.app "not" [k]]
end

meta def prove : tactic unit :=
do tg ← tactic.target,
   q ← target_to_query [] tg,
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
