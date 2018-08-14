import ..smtlib

def solve_type := io (except string (except sexp model))

def solve (q : query) : solve_type :=
do child ← io.proc.spawn{
    cmd := "cvc4",
    args := ["--lang=smt2.6", "--no-interactive", "--produce-models", "--proof"],
    stdin := io.process.stdio.piped,
    stdout := io.process.stdio.piped,
    stderr := io.process.stdio.inherit
   },

  let stdin := child.stdin,
  let stdout := child.stdout,

  -- yes you need to flush - a trick that costed me two hours
  let write_cmd := λ c : cmd, (do
  (io.fs.put_str_ln stdin $ to_string c) >> io.fs.flush stdin
  ),

  write_cmd $ cmd.set_logic "QF_LIA",
  monad.mapm' (λ d, write_cmd $ cmd.declare_const d) q.declares,
  monad.mapm' (λ t, write_cmd $ cmd.assert t) q.asserts,

  write_cmd $ cmd.check_sat,
  sat ← buffer.to_string <$> io.fs.get_line stdout,
  r ← match sat with
  | "sat\n" := do
    write_cmd $ cmd.get_model,
    io.fs.close stdin,
    cb ← io.fs.read_to_end stdout,
    let model' := (from_buffer cb : except parse_error model),
    match model' with
    | except.ok m := (return $ except.ok $ except.ok m : solve_type)
    | except.error e := (return $ except.error e : solve_type)
    end
  | "unsat\n" := do
    write_cmd $ cmd.get_proof,
    io.fs.close stdin,
    cb <- io.fs.read_to_end stdout,
    io.put_str_ln cb.to_string,
    let prf' := (from_buffer cb : except parse_error sexp),
    match prf' with
    | except.ok prf := (return $ except.ok $ except.error prf : solve_type)
    | except.error e := (return $ except.error e : solve_type)
    end
  | _ := do
  write_cmd $ cmd.exit,
  io.fs.close stdin,
  return $ except.error $ string.append "strange satisfiability "  sat
  end,
  io.fs.close stdout,

  _ ← io.proc.wait child,
  return r

