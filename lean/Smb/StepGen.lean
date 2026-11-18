import Smb.Symbolic

/-!
# Per-opcode effect lemmas for the plain machine

`gen_step_tail_lemmas lo hi` adds, for each opcode `op` in `[lo, hi)`, a theorem

    Smb.StepLemma.tail_XX : ∀ pc a x y sp p ram prg cyc bad,
      (CPU.stepTail op).run ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ = <closed form>

where the closed form is computed once, here, by `sym_exec` on a fully symbolic state. A
symbolic run then uses one `rw` per instruction instead of re-deriving the instruction from
the CPU code: the `simp` work and its proof term are paid once per opcode, at library build
time. Since the plain machine never branches on addresses, the lemmas need no hypotheses.
-/
namespace Smb.StepLemma
open Lean Elab Command Term Meta

def lemmaName (op : Nat) : Name :=
  .str `Smb.StepLemma s!"tail_{(Nat.toDigits 16 op).asString |>.pushn '0' 0 |> fun d => if d.length < 2 then "0" ++ d else d}"

elab "gen_step_tail_lemmas" lo:num hi:num : command => do
  for op in [lo.getNat:hi.getNat] do
    liftTermElabM do
      let opLit := Syntax.mkNumLit (toString op)
      let fnStx ← `(fun (pc : UInt16) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool) =>
          (CPU.stepTail (σ := Plain) ($opLit : UInt8)).run ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩)
      let fn ← instantiateMVars (← elabTermAndSynthesize fnStx none)
      lambdaTelescope fn fun xs lhs => do
        let rhs ← mkFreshExprMVar (← inferType lhs)
        let goal ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs rhs)
        -- `sym_exec` rewrites the left side to `R`; `rfl` on `R = ?rhs` then assigns `?rhs := R`.
        let rest ← Tactic.run goal.mvarId! (Tactic.evalTactic (← `(tactic| sym_exec [CPU.stepTail])))
        for g in rest do g.refl
        let rhs ← instantiateMVars rhs
        if rhs.hasMVar then throwError "gen_step_tail_lemmas: opcode {op}: right side not determined"
        let ty ← mkForallFVars xs (← mkEq lhs rhs)
        let prf ← mkLambdaFVars xs (← instantiateMVars goal)
        addDecl <| .thmDecl { name := lemmaName op, levelParams := [], type := ty, value := prf }

end Smb.StepLemma
