import .solve
import .reflect

def test_solve : solve_type := solve [declare.mk "a" "Bool", declare.mk "b" "Bool"] [term.symbol "a", term.app "not" [term.symbol "b"], term.app "=>" [term.symbol "a", term.symbol "b"]]

def test_reflect := by do
k ← tactic.unsafe_run_io test_solve,
match k with
| except.error e := tactic.fail e
| except.ok (except.error proof) := match reflect.ref_check reflect.mk_context proof with
                                    | except.error e := tactic.fail e
                                    | except.ok (p, _) := tactic.to_expr p >>= tactic.infer_type >>= tactic.trace
                                    end
| except.ok (except.ok model) := tactic.fail "actually expecting a proof"
end
