import Smb.Symbolic
import Smb.StepLemmas

/-!
# `sym_run`: instruction-by-instruction symbolic execution

`sym_exec` on a whole run lets terms grow without bound: every flag value is an expression
built on the previous one, and `simp` keeps rewalking it. `sym_run h` instead advances the
hypothesis `h : ((CPU.runTo stop n).run S).2 = f` one instruction at a time:

1. If `S.pc = stop`, the path ends: `f := S`.
2. Otherwise it executes one `CPU.step` on the literal state `S` with `sym_exec`.
3. A branch on symbolic data yields `cond b A B`; the path splits by cases on `b`, and the
   path condition is kept (reverted into the goal) for the final check.
4. Each changed `A`, `X`, `Y`, `S` and `bad` gets a fresh name, with the defining equation
   reverted into the goal. The working context therefore stays small, and side conditions
   discharged inside `sym_exec` see only the names. `p` and the cycle count stay terms that
   `sym_exec` keeps small (see `Smb.Simprocs`); so does `S ± k`. The post-instruction IRQ
   check reduces to the initial `p &&& 4 == 0`, which the caller passes as `hI`.

Each finished path leaves a goal `eqns → path conditions → Q S_final`, for `bv_decide`.
-/
namespace Smb.Symbolic
open Lean Elab Tactic Meta

/-- Debug trace: appends to the file named by `SYMRUN_DEBUG` (Lean captures stderr while
elaborating, so prints there are lost if the process is killed). -/
def dbg (msg : String) : IO Unit := do
  if let some path ← IO.getEnv "SYMRUN_DEBUG" then
    IO.FS.withFile path .append fun h => h.putStrLn msg

theorem of_not_eq_false {c : Bool} (h : (!c) = false) : c = true := by cases c <;> simp_all

private def isAtom (e : Expr) : Bool :=
  e.isFVar || e.isAppOf ``OfNat.ofNat || e.isLit || e.isConst

private def hypSides (h : Name) : TacticM (Expr × Expr) := withMainContext do
  let d ← getLocalDeclFromUserName h
  let ty ← instantiateMVars d.type
  let some (_, lhs, rhs) := ty.eq? | throwError "sym_run: {h} is not an equation"
  return (lhs, rhs)

private def fresh (base : String) : TacticM Name := withMainContext do
  return (← getLCtx).getUnusedName (Name.mkSimple base)

/-- Solve the goal list `[main, side]` produced by a conditional `rw` with `tac` on `side`. -/
private def rwWithSide (rw : Syntax) (side : Syntax) : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic rw
    let gs ← getGoals
    match gs with
    | [main, sideG] =>
      setGoals [sideG]
      evalTactic side
      unless (← getGoals).isEmpty do throwError "side goal left"
      setGoals [main]
      return true
    | [main] => setGoals [main]; return true
    | _ => throwError "unexpected goals"
  catch _ =>
    saved.restore
    return false

/-- Replace every *structural* occurrence of `e` in the hypotheses `hyps` (and the goal) by
a fresh variable `v`, adding `hv : e = v`. Unlike `generalize`, this never searches for
definitionally equal subterms; that search unfolded bit arithmetic down to `Nat` and
dominated the running time. -/
private def abstractIn (hyps : List Name) (e : Expr) (vName hvName : Name) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let fvs ← hyps.mapM fun n => return (← getLocalDeclFromUserName n).fvarId
    let (reverted, g1) ← g.revert fvs.toArray (preserveOrder := true)
    g1.withContext do
      let T ← g1.getType
      let τ ← inferType e
      let g2ty ← withLocalDeclD vName τ fun v => do
        withLocalDeclD hvName (← mkEq e v) fun hv => do
          mkForallFVars #[v, hv] (T.replace fun t => if t == e then some v else none)
      let g2 ← mkFreshExprSyntheticOpaqueMVar g2ty
      g1.assign (mkApp2 g2 e (← mkEqRefl e))
      let (_, g3) ← g2.mvarId!.introNP (2 + reverted.size)
      replaceMainGoal [g3]

/-- Give fresh names to the non-atomic register values and `bad` of the literal state on the
left of `hS`, reverting their defining equations. `p` and the cycle count stay as terms:
`sym_exec` keeps them small (latest setter of each flag; one literal or `cond` of literals
added to the initial count), and naming them would chain every flag test to all earlier
instructions. -/
private def nameFields (hS : Name) : TacticM Unit := do
  -- (name, register index, or the `Plain.mk` field index when `none` is not given)
  let fields : List (String × Sum Nat Nat) :=
    [("a", .inl 1), ("x", .inl 2), ("y", .inl 3), ("sp", .inl 4), ("bad", .inr 4)]
  for (base, idx) in fields do
    let (lhs, _) ← hypSides hS
    unless lhs.isAppOfArity ``Plain.mk 5 do throwError "sym_run: not a literal state:{indentExpr lhs}"
    let regs := lhs.getArg! 0
    unless regs.isAppOfArity ``Regs.mk 6 do throwError "sym_run: registers not literal:{indentExpr regs}"
    let e := match idx with
      | .inl i => regs.getArg! i
      | .inr i => lhs.getArg! i
    if isAtom e then continue
    -- `S ± k` stays a term, so a pull after a push reads the slot it pushed.
    if base == "sp" && (e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6) &&
        e.appFn!.appArg!.isFVar && isAtom e.appArg! then continue
    let v ← fresh base
    let hv ← fresh ("h" ++ base)
    abstractIn [hS] e v hv
    evalTactic (← `(tactic| revert $(mkIdent hv):ident))

/-- The first `cond` in `e` whose condition is symbolic and closed (no bound variables). -/
private partial def findCond? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``cond 4 then
    let b := e.getArg! 1
    if !b.hasLooseBVars && !(b.isConstOf ``Bool.true || b.isConstOf ``Bool.false) then some b
    else e.getAppArgs.findSome? findCond?
  else match e with
    | .app f a => (findCond? f).orElse fun _ => findCond? a
    | .lam _ t b _ => (findCond? t).orElse fun _ => findCond? b
    | .forallE _ t b _ => (findCond? t).orElse fun _ => findCond? b
    | .letE _ t v b _ => ((findCond? t).orElse fun _ => findCond? v).orElse fun _ => findCond? b
    | .mdata _ b => findCond? b
    | .proj _ _ b => findCond? b
    | _ => none

/-- The literal opcode in a `CPU.stepTail op` subterm. -/
private partial def findStepTailOp? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``CPU.stepTail 3 then
    match e.appArg! with
    | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
    | _ => none
  else match e with
    | .app f a => (findStepTailOp? f).orElse fun _ => findStepTailOp? a
    | .mdata _ b => findStepTailOp? b
    | .proj _ _ b => findStepTailOp? b
    | _ => none

/-- Clear the hypotheses named `hx_…`: a theorem's large conditions, there for a callee's `assumption`.
They do not help the SAT solver and can stop it preprocessing at all. -/
elab "clear_hx" : tactic => do
  let g ← getMainGoal
  let ids ← g.withContext do
    return (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.userName.toString.startsWith "hx_" then acc.push d.fvarId else acc
  replaceMainGoal [← g.tryClearMany ids]

/-- Close the main goal if its path conditions and definitions are contradictory. The extra
simp facts (code bytes, …) are cleared first: they only feed `sym_exec`, and in a `bv_decide`
problem they are hundreds of irrelevant equations. -/
private def pruned (extra : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic (← `(tactic| intros))
    -- Clear the large facts only (code bytes: hundreds of irrelevant equations for the SAT
    -- solver); small ones, such as a callee's I-flag fact, can matter for the path.
    for e in extra.getElems do
      if let `(Lean.Parser.Tactic.simpLemma| $i:ident) := e then
        let big ← withMainContext do
          match (← getLCtx).findFromUserName? i.getId with
          | some d => return (← instantiateMVars d.type).approxDepth > 12 || (← instantiateMVars d.type).sizeWithoutSharing > 200
          | none => return false
        if big then evalTactic (← `(tactic| try clear $i:ident))
    evalTactic (← `(tactic| (clear_hx; exfalso; bv_decide (config := { enums := false }))))
    return (← getGoals).isEmpty
  catch _ =>
    saved.restore
    return false

/-- While the state on the left of `hS` is not a literal, split on a symbolic condition
in it and simplify each case. Returns the resulting goals. -/
private partial def splitAll (hS : Name) (extra : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") :
    TacticM (List MVarId) := do
  let (lhs, _) ← hypSides hS
  if lhs.isAppOfArity ``Plain.mk 5 then return ← getGoals
  let some b := findCond? lhs | throwError "sym_run: stuck, and no condition to split on:{indentExpr lhs}"
  let hb ← fresh "hpath"
  let bStx ← withMainContext <| Term.TermElabM.run' (Term.exprToSyntax b)
  evalTactic (← `(tactic| cases $(mkIdent hb):ident : $bStx))
  let mut out := []
  for g in ← getGoals do
    setGoals [g]
    -- Drop the case if the path so far makes it impossible (one SAT call per split).
    if ← pruned extra then continue
    -- On the `true` side of `x == lit` for a named value `x`, replace `x` by the literal, so
    -- that addresses and values built from it become literal too.
    let (neg, eqn) := if b.isAppOfArity ``not 1 then (true, b.appArg!) else (false, b)
    if eqn.isAppOfArity ``BEq.beq 4 && (eqn.getArg! 2).isFVar && (eqn.getArg! 3).isAppOf ``OfNat.ofNat then
      let side ← withMainContext do
        let ty ← instantiateMVars (← getLocalDeclFromUserName hb).type
        return ty.isAppOfArity ``Eq 3 && (ty.getArg! 2).isConstOf ``Bool.true
      if side != neg then
        let hbI := mkIdent hb
        if neg then
          evalTactic (← `(tactic| have hsubst := eq_of_beq (Smb.Symbolic.of_not_eq_false $hbI)))
        else
          evalTactic (← `(tactic| have hsubst := eq_of_beq $hbI))
        evalTactic (← `(tactic| subst hsubst))
    evalTactic (← `(tactic| sym_exec [$(mkIdent hb):ident, $extra,*] at $(mkIdent hS):ident))
    evalTactic (← `(tactic| revert $(mkIdent hb):ident))
    out := out ++ (← splitAll hS extra)
  return out

/-- The literal PC of the state on the left of `h : ((runTo stop n).run S).2 = f`, if any. -/
private def statePc? (h : Name) : TacticM (Option Nat) := do
  let (lhs, _) ← hypSides h
  let S := lhs.appArg!.appArg!
  unless S.isAppOfArity ``Plain.mk 5 do return none
  let regs := S.getArg! 0
  unless regs.isAppOfArity ``Regs.mk 6 do return none
  match regs.getArg! 0 with
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => return some n
  | _ => return none

/-- Run `tac` only if the context has a hypothesis `hstop`, without error recovery (an unknown
identifier would otherwise be logged and replaced by `sorry`, and count as success). -/
elab "with_hstop " tac:tactic : tactic => withMainContext do
  if (← getLCtx).findFromUserName? `hstop |>.isNone then throwError "no hstop"
  Term.withoutErrToSorry <| evalTactic tac

/-- Side conditions `pc ≠ stop` / `pc = stop`: literal, or for a symbolic `stop` from
`hstop : ∀ a, (lo₁ ≤ a && a ≤ hi₁ || …) = true → a ≠ stop` (the routine's code ranges). -/
def stopSide : TacticM Syntax := `(tactic| first
  | ((try dsimp only) <;> decide_closed)
  | with_hstop (dsimp only; exact $(mkIdent `hstop) _ (by decide)))

/-- Discharge a hypothesis of a called routine's theorem in the caller's context. The caller's
extra simp facts (e.g. index definitions) are unfolded before `bv_decide`. -/
def callSide (extra : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") : TacticM Syntax := `(tactic| first
  | assumption
  | decide_closed
  -- The callee's code ranges avoid a literal caller `stop` …
  | (intro a h he; subst he; revert h; decide)
  -- … or the caller's own range hypothesis covers them.
  | with_hstop (clear_hx; intro a h; apply $(mkIdent `hstop); revert h; bv_decide (config := { enums := false }))
  -- (Not `simp [extra] at *`: that would rewrite the facts in `extra` away.)
  | (clear_hx; intros; (try simp only [bne] at *); (try sym_exec [bne, $extra,*]);
     first | done | bv_decide (config := { enums := false })))

/-- A theorem about a called routine: its entry PC (the literal PC of the start state). -/
private partial def callEntry? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``Regs.mk 6 then
    match e.getArg! 0 with
    | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
    | _ => none
  else match e with
    | .app f a => (callEntry? f).orElse fun _ => callEntry? a
    | .forallE _ t b _ => (callEntry? t).orElse fun _ => callEntry? b
    | .lam _ t b _ => (callEntry? t).orElse fun _ => callEntry? b
    | _ => none

/-- At a called routine's entry, replace its execution by its theorem:
`thm … : ∃ j p', ((runTo stop (m + K)).run S).2 = ((runTo stop (j + m)).run F).2 ∧ I-flag`.
Returns the name of the new I-flag fact, to be used by later `sym_exec` calls. -/
private def applyCall (h : Name) (thm : Ident)
    (extra : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") : TacticM Name := do
  -- The path's definitions and conditions, reverted into the goal so far, become hypotheses:
  -- the callee's preconditions are discharged from them.
  evalTactic (← `(tactic| intros))
  withMainContext do
  let e ← elabTerm thm none
  let (mvars, _, ty) ← forallMetaTelescope (← inferType e)
  -- ∃ j w₁ … wₖ, lhs = rhs ∧ _   (the witnesses: flags, and any other unspecified results)
  let mut body := ty
  let mut nEx := 0
  while body.isAppOfArity ``Exists 2 do
    let .lam _ _ b _ := body.appArg! | throwError "sym_run: {thm}: unexpected shape"
    body := b
    nEx := nEx + 1
  unless nEx ≥ 1 do throwError "sym_run: {thm} is not a call theorem"
  let some (eqn, _) := body.app2? ``And | throwError "sym_run: {thm}: unexpected shape"
  let some (_, lhs, _) := eqn.eq? | throwError "sym_run: {thm}: unexpected shape"
  if lhs.hasLooseBVars then throwError "sym_run: {thm}: the start state depends on the witnesses"
  let (hl, _) ← hypSides h
  -- Compare the literal parts of the fuels first: unifying `?m + K` with `e + k` for `k < K`
  -- makes `isDefEq` unfold `Nat.add` step by step and effectively hang.
  let litPart (f : Expr) : Option Nat :=
    if f.isAppOfArity ``HAdd.hAdd 6 then (f.appArg!.nat?).orElse fun _ => f.appArg!.rawNatLit? else f.nat?
  let fuelOf (e : Expr) : Option Expr :=
    let run := e.appArg!.appFn!.appArg!
    if run.isAppOf ``CPU.runTo then some run.appArg! else none
  if let (some fc, some fl) := (fuelOf hl, fuelOf lhs) then
    if let (some kc, some kl) := (litPart (← instantiateMVars fc), litPart fl) then
      if kc < kl then
        throwError "sym_run: not enough fuel for {thm}: {kc} left, it needs {kl} (raise the fuel)"
  let t0 ← IO.monoMsNow
  dbg s!"matching {thm.getId}"
  unless ← isDefEq lhs hl do throwError "sym_run: {thm} does not match the state at its entry"
  if (← IO.monoMsNow) - t0 > 1000 then dbg s!"slow match for {thm.getId} ({(← IO.monoMsNow) - t0} ms)"
  -- Discharge the remaining hypotheses in the caller's context.
  let side ← callSide extra
  for mv in mvars do
    let mv := mv.mvarId!
    unless ← mv.isAssigned do
      let saved ← getGoals
      setGoals [mv]
      let t0 ← IO.monoMsNow
      dbg s!"discharging for {thm.getId}: {← ppExpr (← mv.getType)}"
      try evalTactic side catch _ =>
        -- for the error message: what is left after simplification
        let left ← try
            evalTactic (← `(tactic| (intros; (try simp only [bne] at *); (try sym_exec [bne, $extra,*]))))
            pure (← getGoals).head?
          catch _ => pure none
        let leftTy ← match left with
          | some g => g.getType
          | none => mv.getType
        throwError "sym_run: cannot discharge a hypothesis of {thm}:{indentExpr (← mv.getType)}\nafter simplification:{indentExpr leftTy}"
      if (← IO.monoMsNow) - t0 > 1000 then
        dbg s!"slow side goal for {thm.getId} ({(← IO.monoMsNow) - t0} ms)"
      setGoals saved
  let pf ← instantiateMVars (mkAppN e mvars)
  let hc ← fresh "hcall"; let hI ← fresh "hI"
  let g ← getMainGoal
  let g ← g.assert hc (← inferType pf) pf
  let (_, g) ← g.intro1P
  replaceMainGoal [g]
  -- Name the witnesses `j`, then `p`, `w`, `w`, … (fresh), and the two facts.
  let mut pats : Array (TSyntax `rcasesPat) := #[]
  for i in [0:nEx] do
    let n ← fresh (if i == 0 then "j" else if i == 1 then "p" else "w")
    pats := pats.push (← `(rcasesPat| $(mkIdent n):ident))
    -- reserve the name so the next `fresh` differs
    let g ← getMainGoal
    let (_, g) ← (← g.assert n (mkConst ``True) (mkConst ``True.intro)).intro1P
    replaceMainGoal [g]
  pats := pats.push (← `(rcasesPat| $(mkIdent hc):ident))
  pats := pats.push (← `(rcasesPat| $(mkIdent hI):ident))
  -- drop the placeholder names again before destructuring
  for pt in pats.extract 0 nEx do
    if let `(rcasesPat| $i:ident) := pt then evalTactic (← `(tactic| clear $i:ident))
  evalTactic (← `(tactic| obtain ⟨$pats,*⟩ := $(mkIdent hc)))
  evalTactic (← `(tactic| rw [$(mkIdent hc):ident] at $(mkIdent h):ident; clear $(mkIdent hc)))
  -- Fuel `j + (m + k)` → `j + m + k`, so that later steps can match `n + 1`.
  evalTactic (← `(tactic| try simp only [← Nat.add_assoc] at $(mkIdent h):ident))
  return hI

/-- While the A, X or Y register of the state on the left of `hS` contains a closed `cond`,
split on it (before the value is named and the condition hidden in its definition). Callee
closed forms stay folded, so this splits on few conditions, each once per path. -/
private partial def splitIndex (hS : Name) (extra : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") :
    TacticM (List MVarId) := do
  let (lhs, _) ← hypSides hS
  unless lhs.isAppOfArity ``Plain.mk 5 && (lhs.getArg! 0).isAppOfArity ``Regs.mk 6 do return ← getGoals
  let regs := lhs.getArg! 0
  -- Only opaque predicates (`startsJump ram`, `skidStops ram`, …), not raw comparisons: those
  -- are data, and splitting on them multiplies paths for nothing.
  let isOpaque (b : Expr) : Bool :=
    b.getAppFn.isConst && ![``BEq.beq, ``bne, ``decide, ``not, ``and, ``or].contains b.getAppFn.constName!
  let pick (e : Expr) : Option Expr := (findCond? e).filter isOpaque
  let some b := ((pick (regs.getArg! 1)).orElse fun _ => pick (regs.getArg! 2)).orElse
      fun _ => pick (regs.getArg! 3) | return ← getGoals
  dbg s!"index split on {← ppExpr b}"
  let hb ← fresh "hpath"
  let bStx ← withMainContext <| Term.TermElabM.run' (Term.exprToSyntax b)
  evalTactic (← `(tactic| cases $(mkIdent hb):ident : $bStx))
  let mut out := []
  for g in ← getGoals do
    setGoals [g]
    if ← pruned extra then continue
    evalTactic (← `(tactic| sym_exec [$(mkIdent hb):ident, $extra,*] at $(mkIdent hS):ident))
    evalTactic (← `(tactic| revert $(mkIdent hb):ident))
    out := out ++ (← splitIndex hS extra)
  return out

/-- Advance one path until it stops (at `stop`, or at `target` if given); returns the
finished goals. -/
private partial def runPath (h : Name) (extra : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",")
    (target : List Nat) (calls : Array (Nat × Ident)) : TacticM (List MVarId) := do
  let hId := mkIdent h
  evalTactic (← `(tactic| try simp only [runToLit] at $hId:ident))
  let pc ← statePc? h
  dbg s!"pc {pc.map fun n => String.ofList (Nat.toDigits 16 n)}"
  if let some pc := pc then
    if target.contains pc then return ← getGoals
  -- A called routine with a theorem: use it instead of executing its code.
  if let some pc := pc then
    if let some (_, thm) := calls.find? (·.1 == pc) then
      let hI ← applyCall h thm extra
      let extra := extra.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent hI):ident))
      return ← runPath h extra target calls
  let side ← stopSide
  -- Stop here?
  if ← rwWithSide (← `(tactic| rw [runTo_snd_stop] at $hId:ident)) side then
    evalTactic (← `(tactic| subst $hId:ident))
    return ← getGoals
  unless ← rwWithSide (← `(tactic| rw [runTo_snd_step] at $hId:ident)) side do
    let (lhs, _) ← hypSides h
    -- An indirect jump whose target depends on a condition (e.g. `JumpEngine` on a state
    -- that this path computed as a `cond`): split on it, as at a branch.
    let S := lhs.appArg!.appArg!
    if S.isAppOfArity ``Plain.mk 5 && (S.getArg! 0).isAppOfArity ``Regs.mk 6 then
      if let some b := findCond? ((S.getArg! 0).getArg! 0) then
        dbg s!"pc split on {← ppExpr b}"
        let hb ← fresh "hpath"
        let bStx ← withMainContext <| Term.TermElabM.run' (Term.exprToSyntax b)
        evalTactic (← `(tactic| cases $(mkIdent hb):ident : $bStx))
        let mut done := []
        for g in ← getGoals do
          setGoals [g]
          if ← pruned extra then continue
          dbg "pc split: case kept"
          -- Simplify the *state* only: `sym_exec` on the whole run would unfold `runTo` and
          -- execute the remaining fuel symbolically from a non-literal PC.
          let (lhs', _) ← hypSides h
          abstractIn [h] lhs'.appArg!.appArg! `symPcState `symPcEq
          evalTactic (← `(tactic| sym_exec [$(mkIdent hb):ident, $extra,*] at $(mkIdent `symPcEq):ident))
          evalTactic (← `(tactic| subst $(mkIdent `symPcEq):ident))
          dbg "pc split: simplified"
          evalTactic (← `(tactic| revert $(mkIdent hb):ident))
          done := done ++ (← runPath h extra target calls)
        return done
      -- A PC given by a definition (a callee summary's `NAME_pc …`): unfold it and retry; its
      -- `bif`s are then split on as above.
      let pcE := (S.getArg! 0).getArg! 0
      if let some c := pcE.getAppFn.constName? then
        if c != ``OfNat.ofNat && c != ``cond then
          dbg s!"pc unfold {c}"
          evalTactic (← `(tactic| simp only [$(mkIdent c):ident] at $hId:ident))
          return ← runPath h extra target calls
    throwError "sym_run: cannot advance (out of fuel, or the PC is not a literal):{indentExpr lhs}"
  -- Execute one instruction on the literal state.
  let (lhs, _) ← hypSides h
  let next := lhs.appArg!.appArg!
  let hS := `symS
  abstractIn [h] next `symNext hS
  -- Fetch the opcode, apply that opcode's effect lemma, and tidy the literal parts.
  evalTactic (← `(tactic| sym_exec [$extra,*] at $(mkIdent hS):ident))
  let (lhs, _) ← hypSides hS
  let some op := findStepTailOp? lhs
    | throwError "sym_run: opcode not determined after fetch:{indentExpr lhs}"
  evalTactic (← `(tactic| rw [$(mkIdent (StepLemma.lemmaName op)):ident] at $(mkIdent hS):ident))
  evalTactic (← `(tactic| sym_exec [$extra,*] at $(mkIdent hS):ident))
  -- Split on symbolic conditions (branches, page crossings) until the state is literal.
  let paths ← splitAll hS extra
  -- A register holding a conditional value (e.g. `JumpEngine`'s state read through a callee's
  -- closed form): split on it now, before it is named and the condition hidden.
  let paths ← paths.flatMapM fun g => do setGoals [g]; splitIndex hS extra
  let mut done := []
  for g in paths do
    setGoals [g]
    nameFields hS
    evalTactic (← `(tactic| subst $(mkIdent hS):ident))
    done := done ++ (← runPath h extra target calls)
  return done

/-- `sym_run h [simp facts] (until pc | until [pc, …])? (calls [thm, …])?`: symbolic execution of
the run in `h`. With `until`, paths end at those PCs instead of at the run's `stop`. Each `calls` theorem
replaces the execution of the routine at its entry PC. -/
syntax symUntil := &" until " (num <|> ("[" num,* "]"))
syntax symCalls := &" calls " "[" ident,* "]"
syntax "sym_run" ident ("[" Lean.Parser.Tactic.simpLemma,* "]")? (symUntil)? (symCalls)? : tactic
elab_rules : tactic
  | `(tactic| sym_run $h:ident $[[$extra,*]]? $[$u:symUntil]? $[$c:symCalls]?) => do
    let extra := extra.getD ⟨#[]⟩
    let target : List Nat ← match u with
      | none => pure []
      | some u => match u with
        | `(symUntil| until $t:num) => pure [t.getNat]
        | `(symUntil| until [$ts,*]) => pure (ts.getElems.map (·.getNat)).toList
        | _ => throwUnsupportedSyntax
    let cs : Array Ident ← match c with
      | some c => match c with
        | `(symCalls| calls [$ids,*]) => pure ids.getElems
        | _ => throwUnsupportedSyntax
      | none => pure #[]
    let calls ← cs.mapM fun (c : Ident) => do
      -- Instantiated: a theorem specialised by `have h := thm r` has a metavariable type.
      let ty ← withMainContext do instantiateMVars (← inferType (← elabTerm c none))
      let some pc := callEntry? ty | throwError "sym_run: no entry PC found in {c}"
      return ((pc, c) : Nat × Ident)
    setGoals (← runPath h.getId extra target calls)

/-- Applications `f a` of a free variable `f` to a closed argument, in `e` (each shared
subterm visited once). -/
partial def collectFApps (e : Expr) : StateM (Std.HashSet Expr × Array Expr) (Std.HashSet Expr × Array Expr) := do
  let rec go (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
    let (vis, acc) ← get
    if vis.contains e then return
    set (vis.insert e, acc)
    if e.isApp && e.appFn!.isFVar && !e.appArg!.hasLooseBVars then
      modify fun (v, a) => (v, a.push e)
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  go e
  get

/-- Ackermann's reduction for `bv_decide`, which treats `ram e₁` and `ram e₂` as unrelated
atoms: for every pair of applications of a free memory function (`UInt16 → UInt8`, e.g.
`ram`, `prg`) to different index terms in the goal and hypotheses, add
`e₁ = e₂ → f e₁ = f e₂`. -/
elab "fun_congr" : tactic => withMainContext do
  let g ← getMainGoal
  let mut apps : Std.HashMap FVarId (Array Expr) := {}
  let mut seen : Std.HashSet Expr := {}
  let mut todo : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← isProp d.type) then todo := todo.push (← instantiateMVars d.type)
  let ty := mkForall `i .default (mkConst ``UInt16) (mkConst ``UInt8)
  let mut found : Array Expr := #[]
  for t in todo do
    found := (collectFApps t).run' ({}, #[]) |>.2 |> (found ++ ·)
  for e in found do
      if seen.contains e then continue
      seen := seen.insert e
      let f := e.appFn!.fvarId!
      unless ← isDefEq (← inferType e.appFn!) ty do continue
      apps := apps.insert f ((apps.getD f #[]).push e.appArg!)
  let mut g := g
  for (f, idxs) in apps.toList do
    for i in [0:idxs.size] do
      for j in [i+1:idxs.size] do
        let (a, b) := (idxs[i]!, idxs[j]!)
        let fe := mkFVar f
        let hTy ← mkArrow (← mkEq a b) (← mkEq (mkApp fe a) (mkApp fe b))
        let pf ← withLocalDeclD `h (← mkEq a b) fun h => do
          mkLambdaFVars #[h] (← mkCongrArg fe h)
        let g' ← g.assert `hcongr hTy pf
        let (_, g'') ← g'.intro1P
        g := g''
  replaceMainGoal [g]

/-- Succeeds iff the goal is an equation between register files. -/
elab "is_regs_eq" : tactic => withMainContext do
  let some (ty, _, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq? | throwError "not an equation"
  unless ty.isConstOf ``Regs do throwError "not a register equation"

/-- On a goal `∃ j, ∃ p', ((runTo stop F).run S).2 = ((runTo stop (j + m)).run S').2 ∧ _`, supply
`j := F - m` and rewrite `F - m + m` to `F`, so that the two runs have the same fuel. -/
elab "call_fuel" : tactic => withMainContext do
  let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
  let some (_, body) := tgt.app2? ``Exists | throwError "call_fuel: not ∃:{indentExpr tgt}"
  let .lam _ _ body _ := body.consumeMData | throwError "call_fuel: unexpected shape"
  -- skip the other witnesses
  let mut body := body.consumeMData
  while body.isAppOfArity ``Exists 2 do
    let .lam _ _ b _ := body.appArg!.consumeMData | throwError "call_fuel: unexpected shape"
    body := b.consumeMData
  let some (eqn, _) := body.app2? ``And | throwError "call_fuel: unexpected shape"
  let some (_, lhs, _) := eqn.consumeMData.eq? | throwError "call_fuel: unexpected shape"
  -- lhs = Prod.snd (StateT.run (CPU.runTo stop F) S)
  let run := lhs.appArg!.appFn!.appArg!
  unless run.isAppOf ``CPU.runTo do throwError "call_fuel: no runTo in{indentExpr lhs}"
  let fuel := run.appArg!
  let fuelStx ← Term.exprToSyntax fuel
  evalTactic (← `(tactic| refine ⟨$fuelStx - $(mkIdent `m), ?_⟩))
  evalTactic (← `(tactic| rw [Nat.sub_add_cancel (by omega)]))

/-- Finish a call theorem's path: `∃ j p', run = run' F ∧ I-flag`, where the path's run is in
the goal (after `subst`). The end state is compared field by field (RAM pointwise), after
unfolding `defs` and evaluating literal index arithmetic so that both sides name the same RAM
cells. -/
macro "call_finish" " [" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (try simp only [bne] at *)
  call_fuel
  repeat apply Exists.intro
  apply And.intro
  · congr 2
    all_goals (try congr 1)
    all_goals first
      | rfl
      | (funext i; (try sym_exec [bne, $defs,*]); fun_congr; bv_decide (config := { enums := false }))
      -- Registers field by field (which also assigns the flags witness `p'`) …
      | (is_regs_eq; congr 1 <;> (try sym_exec [bne, $defs,*]) <;> fun_congr <;> bv_decide (config := { enums := false }))
      -- … everything else whole: `congr` would split `a + b = c + d` into `a = c`, `b = d`.
      | ((try sym_exec [bne, $defs,*]) <;> fun_congr <;> bv_decide (config := { enums := false }))
  · bv_decide (config := { enums := false })))

/-- `call_finish`, unfolding `defs` in the path hypotheses too: callers whose path conditions
mention a callee's closed form (the split was on it) must see the same atoms on both sides. -/
macro "call_finish_all" " [" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (try sym_exec [bne, $defs,*] at *)
  call_finish [$defs,*]))

/-- Finish a path of a *reach* theorem, `∃ j t, run = run' t ∧ P t`: `t` is the path's end
state, and `P t` is checked by `bv_decide` after unfolding `defs`. -/
macro "reach_finish" " [" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (try simp only [bne] at *)
  call_fuel
  refine ⟨_, rfl, ?_⟩
  (try sym_exec [bne, $defs,*])
  fun_congr
  bv_decide (config := { enums := false })))

/-- `reach_finish`, unfolding `defs` in the hypotheses too: when paths were split on an opaque
predicate (`skidStops R'`), the goal and the path conditions must name the same atoms. -/
macro "reach_finish_all" " [" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (try simp only [bne] at *)
  call_fuel
  refine ⟨_, rfl, ?_⟩
  (try sym_exec [bne, $defs,*] at *)
  fun_congr
  bv_decide (config := { enums := false })))

end Smb.Symbolic
