import Smb.Routine.OffscreenBits
import Smb.Routine.ScrollPost

/-! Normalize the callee's named value equations, never the surrounding
`runTo` goal. Simplifying the latter can unfold a symbolic continuation. -/
namespace Smb.Symbolic
open Lean Elab Tactic Meta

elab "normalize_offscreen_hyps" : tactic => withMainContext do
  let mut names : Array Name := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← isProp d.type) && !d.type.isForall then
      names := names.push d.userName
  for n in names do
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| try sym_exec [Smb.Routine.gxoBits, Smb.Routine.gxoY,
      Smb.Routine.gxoR, Smb.Routine.gxoL, Smb.Routine.objX, Smb.Routine.objPage,
      Smb.Routine.offBits, Smb.Routine.edgePageDiff] at $(mkIdent n):ident))

end Smb.Symbolic
