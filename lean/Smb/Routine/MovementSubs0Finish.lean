import Smb.Routine.MovementSubs0Defs

/-! Recreate the small safety fact that exact-mode summary generation records
for a path's accumulated interrupt checks. The proof is checked independently
and keeps irrelevant symbolic-memory hypotheses out of the SAT problem. -/
namespace Smb.Symbolic
open Lean Elab Tactic Meta

elab "settle_run_bad " h:ident : tactic => withMainContext do
  let goals ← getGoals
  let g ← getMainGoal
  let ht ← instantiateMVars (← getLocalDeclFromUserName h.getId).type
  let some (_, lhs, _) := ht.eq? | throwError "settle_run_bad: expected a run equation"
  let state := lhs.appArg!.appArg!
  unless state.isAppOfArity ``Smb.Plain.mk 5 do
    throwError "settle_run_bad: expected a Plain state"
  let bad := state.getArg! 4
  let ty ← mkEq bad (toExpr false)
  let proof ← mkFreshExprMVar ty
  setGoals [proof.mvarId!]
  -- Inline the named bad-value chain before filtering. Dropping its defining
  -- equalities first would leave an unconstrained Boolean instead of the
  -- accumulated interrupt checks.
  evalTactic (← `(tactic| subst_vars))
  let sub ← getMainGoal
  let drop ← sub.withContext do
    let vars := (collectFVars {} (← instantiateMVars (← sub.getType))).fvarIds
    let mut drop := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if d.userName == h.getId || d.userName.toString.startsWith "hx_" ||
          !(← isProp t) || t.isForall ||
          !(collectFVars {} t).fvarIds.any vars.contains then
        drop := drop.push d.fvarId
    return drop
  let sub ← sub.tryClearMany drop
  setGoals [sub]
  evalTactic (← `(tactic| (fun_congr; bv_decide (config := { enums := false }))))
  unless (← getGoals).isEmpty do throwError "settle_run_bad: safety fact remains open"
  let g' ← g.assert `hsettled ty (← instantiateMVars proof)
  setGoals ((← g'.intro1P).2 :: goals.tail)

end Smb.Symbolic
