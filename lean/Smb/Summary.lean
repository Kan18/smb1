import Smb.SymRun

/-!
# `sym_summary`: a routine's closed form, read off its symbolic execution

`sym_summary NAME h [facts] until … calls […]` runs `sym_run` on `h` and turns the finished
paths into definitions instead of leaving them as goals. For each path it takes the path
conditions (`b = true/false`, and `e = lit` where a split substituted a literal for a named
value) and the end state, inlines the names `sym_run` gave to
intermediate values (`e = a_1`), and expresses everything in terms of the inputs: the free
variables of the start state. The paths are then folded field by field into
`bif path₁ then value₁ else bif path₂ then value₂ else … valueₙ` (RAM pointwise), and defined
as `NAME_pc`, `NAME_a`, `NAME_x`, `NAME_y`, `NAME_s`, `NAME_ram`, `NAME_cyc`, `NAME_bad`, each
a function of the inputs some definition uses (logged), in their order. The flags are not defined: call theorems give them as
an existential `p'` with only the I flag known. A register or the cycle count that depends on
a callee result its call theorem leaves unspecified is not defined either (reported) (`set_option sym_summary.print true`
logs their source). Before folding, each term is simplified with `sym_exec`'s simp set
(after inlining, a branch's flag-shaped test often reduces to a value test), every `bif` test
and path conjunct the hypotheses settle is replaced by its value (one `bv_decide` per distinct
test, given only the hypotheses about its variables), each conjunct the others imply is
dropped, and a value shared by all later paths needs no test.

This replaces hand-written closed forms and cycle formulas. It proves nothing: a call theorem
stated with these definitions is proved as before (`call_finish [NAME_…]`), so a generator
bug shows up as a failed proof, never as a wrong theorem. The path conditions are those of
`sym_run`, including its pruning: the last path's condition is not tested (it is the `else`).
Run it through the command `sym_summarize`, which elaborates a statement and tactic block
like `example` but keeps the definitions (an `example` discards its environment changes):

```
sym_summarize js (m : Nat) (a x y sp p : UInt8) … : ∃ j t, run … = run … t ∧ True := by
  simp only [CodeAt, jumpspringCode, UInt16.reduceAdd] at hcode
  generalize hrun : … = f
  sym_summary js hrun [hcode, hI, hx] until 47362
```

## One run, generating and proving: `sym_theorem` and `exact`

The two steps above execute the routine symbolically twice. The command `sym_theorem` runs it once:

```
sym_theorem ms2_call (binders…) : ((CPU.runTo stop (m + 600)).run S).2 := by
  …
  generalize hrun : ((CPU.runTo stop (m + 600)).run S).2 = f
  sym_summary ms2 hrun [facts] until … calls […] exact finish (exact_finish ms2)
```

The statement after the binders is only the run; the theorem `∃ j p' …, run = run' END ∧ (p' &&& 4 == 0) = false`
is written by `sym_summary`, once it has the definitions (`END`: the definitions applied to the inputs,
undefined fields existential). During the tactics the target is `sym_post f` for a local `sym_post`, which
`sym_theorem` replaces in the finished proof. Each path stays a goal instead of being admitted, and `finish`
proves it.

With `exact`, conditions and values stay as the paths computed them (names inlined, not simplified), so
that `exact_finish` needs no second simplification and no comparison of expanded formulas. It rewrites with the
path's own split facts to decide the fold's conditions, in order up to the first true one, using SAT
only on a condition rewriting leaves undecided, and closes the path by `rfl`. A test that reads a
callee's unspecified flags but stops depending on them when simplified is kept in simplified form, with its proof as a
path fact; so is a settled value. Definitions in this form are for proofs: derive a readable formula separately
when a game question needs one.

`summary_interface NAME` then gives callers a way not to expand `NAME_ram`: the addresses it may write, an
opaque byte at each, and a read lemma. `summary_regs NAME` proves the stack pointer and `bad` pass through.
`summary_go NAME ADDR EXIT` gives a theorem per exit, under a hypothesis naming it, so that a caller has no PC to split on.
`summary_reach NAME ADDR` states the end state directly, at `stop = ADDR`.

**Compose by segments.** A flat run's branches multiply; a segment's summary folds them into one end state, so its caller does not
(`PlayerCtrlA`, `MovementSwim`). The entry flags `p` count as a callee's result in tests, since in a caller they are one: a test independent of
`p` must not take it as an input. Large hypotheses are named `hx_…`: `clear_hx` drops them before `bv_decide`.
-/
namespace Smb.Symbolic
open Lean Elab Tactic Meta

register_option sym_summary.raw : Bool := {
  defValue := false
  descr := "sym_summary: keep each path's values raw (names inlined only) instead of simplified"
}

register_option sym_summary.print : Bool := {
  defValue := false
  descr := "sym_summary: log the source of the generated definitions"
}

/-- A marker for simplifying a term with `sym_exec`: `simp at (h : Keep t)` rewrites inside `t`. -/
def Keep {α : Sort _} (_ : α) : Prop := True

/-- `e` without the dead branches of `bif true`/`bif false`, which can mention a callee's unspecified result. -/
private partial def dropDead (e : Expr) : Expr :=
  e.replace fun t =>
    if t.isAppOfArity ``cond 4 then
      if (t.getArg! 1).isConstOf ``Bool.false then some (dropDead (t.getArg! 3))
      else if (t.getArg! 1).isConstOf ``Bool.true then some (dropDead (t.getArg! 2))
      else none
    else none

/-- `a = b`, opaque to `subst_vars`: a settled value whose right side is an input variable. -/
def Settled (a b : Bool) : Prop := a = b

/-- Stands for a callee's unspecified RAM witness (`∃ w, … sideRam w …`) in an exact-mode path's RAM:
the definitions take a parameter `w` in its place, and the theorem's statement is `∃ … w, …`. -/
def ramWitness : UInt16 → UInt8 := fun _ => 0

/-- The state `S` in `h : ((runTo stop n).run S).2 = f`. -/
private def runState (ty : Expr) : MetaM Expr := do
  let some (_, lhs, _) := ty.eq? | throwError "sym_summary: not an equation:{indentExpr ty}"
  return lhs.appArg!.appArg!

/-- Replace the defined variables in `e` until none is left. -/
private partial def inline (defs : Std.HashMap FVarId Expr) (e : Expr) : Expr :=
  let e' := e.replace fun t => if t.isFVar then defs.get? t.fvarId! else none
  if e' == e then e else inline defs e'

private def mkAnd (a b : Expr) : Expr := mkApp2 (mkConst ``and) a b
private def mkNot (a : Expr) : Expr := mkApp (mkConst ``not) a

/-- The value the hypotheses of `g0` (its propositions, except `h` and the `∀` ones) force on the
closed Bool `c`, if `bv_decide` finds one. -/
private def settle (g0 : MVarId) (h : Name) (c : Expr) : TacticM (Option Bool) := do
  for (val, lit) in [(true, ``Bool.true), (false, ``Bool.false)] do
    let saved ← saveState
    try
      let m ← g0.withContext do
        let ty ← mkEq c (mkConst lit)
        -- Keep only hypotheses about the test's variables (the code bytes, say, only matter
        -- when the test reads `prg`).
        let vars := (collectFVars {} c).fvarIds
        let mut drop := #[]
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let t ← instantiateMVars d.type
          if d.userName == h || d.userName.toString.startsWith "hx_" || !(← isProp t) || t.isForall ||
              !(collectFVars {} t).fvarIds.any vars.contains then drop := drop.push d.fvarId
        let m ← mkFreshExprMVar ty
        m.mvarId!.tryClearMany drop
      setGoals [m]
      evalTactic (← `(tactic| (fun_congr; bv_decide (config := { enums := false }))))
      if (← getGoals).isEmpty then
        saved.restore
        return some val
    catch _ => pure ()
    saved.restore
  return none

/-- A proof of `c = val` from the hypotheses of `g0` (filtered as in `settle`), kept: unlike
`settle`, the state (`bv_decide`'s auxiliary declarations) is not restored on success. -/
private def settleProofTo (g0 : MVarId) (h : Name) (c rhs : Expr) : TacticM (Option Expr) := do
  let saved ← saveState
  try
    let goals ← getGoals
    let (m0, m) ← g0.withContext do
      let ty ← mkEq c rhs
      let vars := (collectFVars {} c).fvarIds
      let mut drop := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if d.userName == h || d.userName.toString.startsWith "hx_" || !(← isProp t) || t.isForall ||
            !(collectFVars {} t).fvarIds.any vars.contains then drop := drop.push d.fvarId
      let m0 ← mkFreshExprMVar ty
      return (m0, ← m0.mvarId!.tryClearMany drop)
    setGoals [m]
    evalTactic (← `(tactic| (fun_congr; bv_decide (config := { enums := false }))))
    let ok := (← getGoals).isEmpty
    setGoals goals
    if ok then return some (← instantiateMVars m0)
  catch _ => pure ()
  saved.restore
  return none

private def settleProof (g0 : MVarId) (h : Name) (c : Expr) (val : Bool) : TacticM (Option Expr) :=
  settleProofTo g0 h c (toExpr val)

/-- Check flag independence in the original context, before symbolic-path facts exist.
The fresh flag byte is arbitrary; even consistent leaf facts can otherwise hide a dependency. -/
private def flagsIndependent (g0 : MVarId) (h : Name) (p : FVarId)
    (guard zeroGuard : Expr) : TacticM Bool := do
  let saved ← saveState
  let ok ← try
    g0.withContext do
      withLocalDeclD `flagProbe (mkConst ``UInt8) fun q => do
        let freshGuard := guard.replace fun t => if t.isFVar && t.fvarId! == p then some q else none
        let probe ← mkFreshExprMVar (mkConst ``True)
        return (← settleProofTo probe.mvarId! h freshGuard zeroGuard).isSome
    catch _ => pure false
  saved.restore
  return ok

/-- `x` simplified by `sym_exec`'s simp set, in `g0`'s context. After inlining, flag-shaped tests
that were built from named values can simplify further (e.g. a `Z` test to a value test). -/
private def simpSym (g0 : MVarId) (x : Expr) : TacticM Expr := do
  let saved ← saveState
  try
    let m ← g0.withContext do mkFreshExprMVar (← mkArrow (← mkAppM ``Keep #[x]) (mkConst ``True))
    let (hk, g) ← m.mvarId!.intro1
    setGoals [g]
    let hId := mkIdent ((← g.getDecl).lctx.get! hk).userName
    evalTactic (← `(tactic| sym_exec [] at $hId:ident))
    let g ← getMainGoal
    let r ← g.withContext do
      let some d := (← getLCtx).findFromUserName? hId.getId | return x
      let t ← instantiateMVars d.type
      return if t.isAppOfArity ``Keep 2 then t.appArg! else x
    saved.restore
    return r
  catch _ =>
    saved.restore
    return x

/-- `x` rewritten with the hypotheses `facts` of `g`'s context (and Boolean basics), in `g`'s
context: the same rewriting `summary_finish` does with the path's facts. -/
private def simpFacts (g : MVarId) (facts : Array FVarId) (x : Expr) : TacticM Expr := do
  if facts.isEmpty then return x
  let saved ← saveState
  try
    let m ← g.withContext do mkFreshExprMVar (← mkArrow (← mkAppM ``Keep #[x]) (mkConst ``True))
    let (hk, g') ← m.mvarId!.intro1
    setGoals [g']
    let names ← g'.withContext do facts.mapM fun f => return mkIdent (← f.getDecl).userName
    let hId := mkIdent ((← g'.getDecl).lctx.get! hk).userName
    let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
    evalTactic (← `(tactic| simp only [Bool.or_false, Bool.false_or, Bool.and_true, Bool.true_and,
      Bool.not_false, Bool.not_true, $lemmas,*] at $hId:ident))
    let r ← (← getMainGoal).withContext do
      let some d := (← getLCtx).findFromUserName? hId.getId | return x
      let t ← instantiateMVars d.type
      return if t.isAppOfArity ``Keep 2 then t.appArg! else x
    saved.restore
    return r
  catch _ =>
    saved.restore
    return x

/-- `x` with the definitions `names` unfolded and then simplified by `sym_exec`'s simp set, in
`g`'s context. -/
private def unfoldSym (g : MVarId) (names : Array Name) (x : Expr) : TacticM Expr := do
  if names.isEmpty then return x
  let saved ← saveState
  try
    let m ← g.withContext do mkFreshExprMVar (← mkArrow (← mkAppM ``Keep #[x]) (mkConst ``True))
    let (hk, g') ← m.mvarId!.intro1
    setGoals [g']
    let hId := mkIdent ((← g'.getDecl).lctx.get! hk).userName
    let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    evalTactic (← `(tactic| simp only [$lemmas,*] at $hId:ident))
    evalTactic (← `(tactic| try sym_exec [] at $hId:ident))
    let r ← (← getMainGoal).withContext do
      let some d := (← getLCtx).findFromUserName? hId.getId | return x
      let t ← instantiateMVars d.type
      return if t.isAppOfArity ``Keep 2 then t.appArg! else x
    saved.restore
    return r
  catch _ =>
    saved.restore
    return x

/-- Replace each closed `bif c then t else e` in `x` whose test the hypotheses settle by the
branch taken (one `bv_decide` per distinct test, cached in `cache`). -/
private def pruneConds (g0 : MVarId) (h : Name) (cache : IO.Ref (Std.HashMap Expr (Option Bool)))
    (x : Expr) : TacticM Expr := do
  let lctx := (← g0.getDecl).lctx
  Meta.transform x (post := fun t => do
    unless t.isAppOfArity ``cond 4 do return .continue
    let c := t.getArg! 1
    if c.hasLooseBVars || c.hasMVar || c.hasAnyFVar (fun fv => !lctx.contains fv) then return .continue
    let r ← match (← cache.get).get? c with
      | some r => pure r
      | none => do
        let r ← settle g0 h c
        cache.modify (·.insert c r)
        pure r
    match r with
    | some true => return .done (t.getArg! 2)
    | some false => return .done (t.getArg! 3)
    | none => return .continue)

/-- Applications of callee closed forms (constants in `Smb.Routine`, such as `jumpRam` or
`frictionDir`) in `e` that mention no bound variable: kept opaque while simplifying, so that a
summary contains them exactly as the path computed them, the same terms the exactness proof
sees (simplifying inside them made the two sides differ). -/
private partial def opaqueTerms (e : Expr) : StateT (Std.HashSet Expr × Array Expr) MetaM Unit := do
  if (← get).1.contains e then return
  let isOpaque : Bool := match e.getAppFn.constName? with
    | some c => (`Smb.Routine).isPrefixOf c && e.isApp && !e.hasLooseBVars
    | none => false
  if isOpaque then
    modify fun (s, a) => (s.insert e, a.push e)
    return
  match e with
  | .app f a => opaqueTerms f; opaqueTerms a
  | .lam _ t b _ => opaqueTerms t; opaqueTerms b
  | .forallE _ t b _ => opaqueTerms t; opaqueTerms b
  | .letE _ t v b _ => opaqueTerms t; opaqueTerms v; opaqueTerms b
  | .mdata _ b => opaqueTerms b
  | .proj _ _ b => opaqueTerms b
  | _ => pure ()

/-- Run `k` with the opaque terms of `es` replaced by fresh local variables in `g0`'s context
(`k` gets a goal in that context, and the abstracted terms), and put the terms back in its
results. -/
private def withOpaques (g0 : MVarId) (es : Array Expr)
    (k : MVarId → Array Expr → TacticM (Array Expr)) : TacticM (Array Expr) := do
  let (_, (_, terms)) ← (es.forM opaqueTerms).run ({}, #[])
  g0.withContext do
    let tys ← terms.mapM fun t => (inferType t : MetaM Expr)
    withLocalDeclsDND (tys.mapIdx fun i ty => (Name.mkSimple s!"opq{i}", ty)) fun fvs => do
      let tbl : Std.HashMap Expr Expr := (terms.zip fvs).foldl (init := {}) fun m (t, v) => m.insert t v
      let abs := es.map fun e => e.replace fun t => tbl.get? t
      let g ← mkFreshExprMVar (mkConst ``True)
      let out ← k g.mvarId! abs
      return out.map fun e => e.replaceFVars fvs terms

syntax symFinish := " finish " "(" tacticSeq ")"
syntax symExact := &" exact"
syntax "sym_summary" ident ident ("[" Lean.Parser.Tactic.simpLemma,* "]")? (symUntil)? (symCalls)? (symExact)? (symFinish)? : tactic
elab_rules : tactic
  | `(tactic| sym_summary $name:ident $h:ident $[[$extra,*]]? $[$u:symUntil]? $[$c:symCalls]? $[$ex:symExact]? $[$fin:symFinish]?) => do
    -- `exact`: conditions and values as the paths computed them (names inlined, not simplified).
    -- Each path's condition is the conjunction of its own split tests, so a path's exactness
    -- proof only rewrites with its own facts (`exact_finish`).
    let exactMode := ex.isSome
    let extra := extra.getD ⟨#[]⟩
    -- With `finish (tac)` (under `sym_theorem`): the target is `?post f`, the call theorem's
    -- statement still to be written. Each path is kept as a goal instead of being admitted;
    -- once the definitions exist, `?post` becomes the statement and `tac` proves each path.
    -- One symbolic execution serves both the generation and the proof.
    let finTac ← fin.mapM fun f => match f with
      | `(symFinish| finish ($t)) => pure t
      | _ => throwUnsupportedSyntax
    let post? ← if finTac.isNone then pure none else do
      let t := (← instantiateMVars (← getMainTarget)).consumeMData
      let .fvar post := t.getAppFn | throwError "sym_summary finish: the target is not `sym_post f` (use `sym_theorem`):{indentExpr t}"
      if t.getAppNumArgs != 1 then throwError "sym_summary finish: the target is not `sym_post f`:{indentExpr t}"
      pure (some post)
    let runEq ← withMainContext do instantiateMVars (← getLocalDeclFromUserName h.getId).type
    -- The inputs: the free variables of the start state, in order of appearance.
    let g0 ← getMainGoal
    let (inputs, before) ← withMainContext do
      let S ← runState (← instantiateMVars (← getLocalDeclFromUserName h.getId).type)
      let fvs := (collectFVars {} S).fvarIds
      let lctx ← getLCtx
      let ordered := lctx.foldl (init := #[]) fun acc d => if fvs.contains d.fvarId then acc.push d.fvarId else acc
      return (ordered, (lctx.foldl (init := ({} : Std.HashSet FVarId)) fun s d => s.insert d.fvarId))
    match u, c with
    | some u, some c => evalTactic (← `(tactic| sym_run $h [$extra,*] $u:symUntil $c:symCalls))
    | some u, none => evalTactic (← `(tactic| sym_run $h [$extra,*] $u:symUntil))
    | none, some c => evalTactic (← `(tactic| sym_run $h [$extra,*] $c:symCalls))
    | none, none => evalTactic (← `(tactic| sym_run $h [$extra,*]))
    -- Each finished path: its condition and end state, in terms of the inputs.
    -- Per path: conditions, and pc, a, x, y, s, cycles, bad, RAM (`none`: not determined).
    -- The definitions keep each path's values as the path computed them (names inlined), so that
    -- `summary_finish` proves them exact by rewriting with the path's own facts and `rfl`.
    let mut leaves : Array (Array Expr × Array (Option Expr)) := #[]
    let mut pending : Array MVarId := #[]
    for g in ← getGoals do
      let (_, g) ← g.intros
      let settled ← IO.mkRef (#[] : Array (Name × Expr × Expr))
      let leaf ← g.withContext do
        let mut defs : Std.HashMap FVarId Expr := {}
        let mut conds : Array Expr := #[]
        for d in ← getLCtx do
          if before.contains d.fvarId || d.isImplementationDetail then continue
          let ty ← instantiateMVars d.type
          let some (_, l, r) := ty.eq? | continue
          if r.isFVar && !before.contains r.fvarId! then defs := defs.insert r.fvarId! l
          else if r.isConstOf ``Bool.true then conds := conds.push l
          else if r.isConstOf ``Bool.false then conds := conds.push (mkNot l)
          -- A named value that a split replaced by a literal (`e = 5`): also a path condition.
          else if d.userName != h.getId then
            if let some c ← observing? (mkAppM ``BEq.beq #[l, r]) then conds := conds.push c
        let some hd := (← getLCtx).findFromUserName? h.getId
          | throwError "sym_summary: a path ended without `{h.getId}` (use `until`)"
        let S := inline defs (← runState (← instantiateMVars hd.type))
        -- Callee results that a call theorem leaves unspecified (its flags `p'`) are neither
        -- inputs nor named values. Hypotheses about them are facts the callee guarantees (its I
        -- flag), not path conditions: dropped. A value may use one only if the path's facts
        -- settle it away (the interrupt check after a call), else the field is not defined.
        let foreign (e : Expr) : Array FVarId := (collectFVars {} e).fvarIds.filter (!before.contains ·)
        -- Simplify first (callee closed forms opaque): a flag test can mention a callee's flags
        -- and mask them out entirely. A condition still about a callee result must be one of the
        -- callee's guarantees (true by the path's facts); a real test on such a value would make
        -- the fold wrong, so it is an error.
        -- The entry flags count like a callee result: in a caller, `p` is the unspecified flags of
        -- the callee before it, so a test only reading bits independent of `p` must not take it.
        let flagInput ← g.withContext do inputs.filterM fun fv => return (← fv.getDecl).userName == `p
        let aboutFlags (t : Expr) : Bool := flagInput.any fun fv => t.containsFVar fv
        let rawConds := conds.map (inline defs)
        let simpd ← if exactMode then pure rawConds else
          withOpaques g rawConds fun g' es => es.mapM (simpSym g')
        let mut conds' := #[]
        for c in simpd do
          if exactMode then
            if (foreign c).isEmpty && !aboutFlags c then conds' := conds'.push c; continue
            -- A test on a callee result: must be one of its guarantees, true by the facts.
            let c' ← withOpaques g #[c] fun g' es => es.mapM (simpSym g')
            let c' ← if (foreign c'[0]!).isEmpty && !aboutFlags c'[0]! then pure c'[0]! else do
              let (_, (_, terms)) ← (opaqueTerms c'[0]!).run ({}, #[])
              let names := terms.filterMap fun t =>
                if (foreign t).isEmpty && !aboutFlags t then none else t.getAppFn.constName?
              unfoldSym g names c'[0]!
            -- Simplified, it no longer depends on the callee (the flag test masks out the callee's
            -- bits): a real test, kept in its simplified form with its proof as a path fact.
            if (foreign c').isEmpty && !aboutFlags c' then
              let some pf ← settleProof g h.getId c' true
                | throwError "sym_summary exact: could not prove a simplified test:{indentExpr c'}"
              settled.modify (·.push (`hcond, ← mkEq c' (toExpr true), pf))
              conds' := conds'.push c'
              continue
            -- First prove that the original guard agrees for every fresh flag byte,
            -- using only the pre-execution context. A true-on-this-path test is insufficient.
            if (foreign c).isEmpty then
              let c0 := c'.replace fun t => if t.isFVar && flagInput.contains t.fvarId! then some (toExpr (0 : UInt8)) else none
              if flagInput.size == 1 && (← flagsIndependent g0 h.getId flagInput[0]! c c0) then
                if let some pf ← settleProof g h.getId c0 true then
                  settled.modify (·.push (`hcond, ← mkEq c0 (toExpr true), pf))
                  conds' := conds'.push c0
                  continue
              -- A real test on the entry flags.
              conds' := conds'.push c
              continue
            -- Still about the callee's result: must be one of its guarantees.
            if (← settle g h.getId c') == some true then continue
            throwError "sym_summary exact: a path condition depends on a callee result:{indentExpr c}"
          -- A callee's helper applied to a callee result (`bbFlags … p'`, of which a branch
          -- tests only bits that do not depend on `p'`): unfold the helpers around it and
          -- simplify again. (The exactness proof then needs `call_finish_all` with them.)
          let c ← if (foreign c).isEmpty && !aboutFlags c then pure c else do
            let (_, (_, terms)) ← (opaqueTerms c).run ({}, #[])
            let names := terms.filterMap fun t =>
              if (foreign t).isEmpty && !aboutFlags t then none else t.getAppFn.constName?
            unfoldSym g names c
          if (foreign c).isEmpty then conds' := conds'.push c
          else if (← settle g h.getId c) != some true then
            throwError "sym_summary: a path condition depends on a callee result left unspecified:{indentExpr c}"
        let fix (e0 : Expr) : TacticM (Option Expr) := do
          let e := if exactMode then dropDead e0 else e0
          if (foreign e).isEmpty && !(exactMode && aboutFlags e) then return some e
          -- Exact mode: `bad` with the post-instruction I-flag checks, which come to the input `bad`.
          if exactMode && (← inferType e).isConstOf ``Bool then
            let badInput ← g.withContext do inputs.filterM fun fv => return (← fv.getDecl).userName == `bad
            if let some b := badInput[0]? then
              if let some pf ← settleProofTo g h.getId e0 (mkFVar b) then
                settled.modify (·.push (`hsettled, mkApp2 (mkConst ``Settled) e0 (mkFVar b), pf))
                return some (mkFVar b)
          if (foreign e).isEmpty then return some e
          if (← inferType e).isConstOf ``Bool then
            if let some b ← settle g h.getId e then
              -- Exact mode: keep the proof as a fact of the path, which `exact_finish` rewrites
              -- with first (instead of proving the equation again).
              if exactMode then
                let some pf ← settleProof g h.getId e0 b
                  | throwError "sym_summary exact: could not re-prove a settled value"
                settled.modify (·.push (`hsettled, ← mkEq e0 (toExpr b), pf))
              return some (toExpr b)
          return none
        let regs := S.getArg! 0
        let mut fs : Array (Option Expr) := #[]
        for k in [0:5] do fs := fs.push (← fix (regs.getArg! k))
        fs := fs.push (← fix (S.getArg! 3))   -- cycles
        fs := fs.push (← fix (S.getArg! 4))   -- bad
        -- Exact mode: one callee RAM witness may appear in the RAM.
        let ramS ← if exactMode then do
            let fns ← (foreign (S.getArg! 1)).filterM fun fv => return (← fv.getType).isForall
            let some w := fns[0]? | pure (S.getArg! 1)
            unless fns.size == 1 do throwError "sym_summary exact: more than one callee RAM witness"
            pure ((S.getArg! 1).replaceFVarId w (mkConst ``ramWitness))
          else pure (S.getArg! 1)
        unless (foreign ramS).isEmpty do
          throwError "sym_summary: the RAM depends on a callee result left unspecified"
        fs := fs.push (some ramS)    -- RAM
        return (conds', fs)
      leaves := leaves.push leaf
      let mut g := g
      for (nm, ty, pf) in ← settled.get do
        let g' ← g.assert nm ty pf
        g := (← g'.intro1P).2
      if post?.isSome then pending := pending.push g else g.admit
    setGoals []
    if leaves.isEmpty then throwError "sym_summary: no finished paths"
    let conj (bs : Array Expr) : Expr := (bs.foldl (init := (none : Option Expr)) fun acc b =>
      some (match acc with | none => b | some a => mkAnd a b)).getD (mkConst ``Bool.true)
    -- Simplify each path under the theorem's hypotheses, with callee closed forms opaque:
    -- `sym_exec`'s simp set (a flag test becomes a value test), tests the hypotheses settle
    -- replaced by their value, conjuncts the others imply dropped.
    let paths ← if exactMode then pure (leaves.map fun (conds, fs) => (conj conds, fs)) else leaves.mapM fun (conds, fs) => do
      let defined := fs.filterMap id
      let out ← withOpaques g0 (conds ++ defined) fun g es => do
        let cache ← IO.mkRef ({} : Std.HashMap Expr (Option Bool))
        let mut kept := #[]
        for b in es[0:conds.size] do
          let b ← pruneConds g h.getId cache (← simpSym g b)
          if (← settle g h.getId b) != some true then kept := kept.push b
        let order := (List.range kept.size).toArray.qsort fun i j => kept[i]!.approxDepth > kept[j]!.approxDepth
        let mut drop : Std.HashSet Nat := {}
        for i in order do
          let others := (List.range kept.size).filter (fun j => j != i && !drop.contains j) |>.map (kept[·]!)
          let imp := mkApp2 (mkConst ``or) (mkNot (conj others.toArray)) kept[i]!
          if (← settle g h.getId imp) == some true then drop := drop.insert i
        let kept' := (List.range kept.size).filter (!drop.contains ·) |>.map (kept[·]!) |>.toArray
        -- Values simplified by `sym_exec`'s simp set (callee closed forms opaque), which the
        -- comparison in `summary_finish` redoes on the path's own end state; or raw (names
        -- inlined only, `sym_summary.raw`), closed by `rfl` (small routines only: raw values with
        -- nested callee closed forms are too large to compare).
        let raw := sym_summary.raw.get (← getOptions)
        let vals ← es[conds.size:].toArray.mapM fun v => if raw then pure v else simpSym g v
        return #[conj kept'] ++ vals
      let mut i := 1
      let mut fs' := #[]
      for f? in fs do
        match f? with
        | some _ => fs' := fs'.push (some out[i]!); i := i + 1
        | none => fs' := fs'.push none
      return (out[0]!, fs')
    -- Fold the paths field by field and define each field as a function of the inputs. The
    -- path conditions are definitions of their own (`NAME_c0`, …), which `summary_finish` decides
    -- one at a time: a small SAT problem each, never together with the values.
    g0.withContext do
      let used0 := paths.foldl (init := ({} : Std.HashSet FVarId)) fun s (c, fs) =>
        (fs.filterMap id |>.push c).foldl (fun s e => (collectFVars {} e).fvarIds.foldl (·.insert ·) s) s
      let params := (inputs.filter used0.contains).map mkFVar
      -- Each definition takes only the inputs it uses, so that a RAM form does not seem to depend on
      -- a cycle count the same summary's cycle field uses.
      let paramsOf (v : Expr) : Array Expr :=
        let fvs := (collectFVars {} v).fvarIds
        (inputs.filter fvs.contains).map mkFVar
      let addDef (declName : Name) (v : Expr) : MetaM Unit := do
        let v' ← withLocalDeclD `w (← inferType (mkConst ``ramWitness)) fun w => do
          let body ← mkLambdaFVars (paramsOf v) (v.replace fun t => if t.isConstOf ``ramWitness then some w else none)
          if v.find? (·.isConstOf ``ramWitness) |>.isSome then mkLambdaFVars #[w] body else pure body
        let v := v'
        let ty ← inferType v
        addDecl (.defnDecl (mkDefinitionValEx declName [] ty v (.regular 0) .safe [declName]))
        enableRealizationsForConst declName
        -- Irreducible: `rfl` and `congr` in proofs would otherwise try to unfold these terms
        -- definitionally (minutes); `simp only [NAME_…]` unfolds them by their equations.
        setReducibilityStatus declName .irreducible
      let mut condApps : Array Expr := #[]
      for i in [0:paths.size - 1] do
        let cName := (← getCurrNamespace) ++ name.getId.appendAfter s!"_c{i}"
        addDef cName paths[i]!.1
        condApps := condApps.push (mkAppN (mkConst cName) (paramsOf paths[i]!.1))
      let field (k : Nat) (get : Expr → MetaM Expr) : MetaM (Option Expr) := do
        let some vals := paths.mapM (fun (_, fs) => fs[k]!) | return none
        let vals ← vals.mapM get
        let mut out := vals.back!
        for i in (List.range (paths.size - 1)).reverse do
          -- The same value on this path as on all later ones: no test needed.
          if vals[i]! == out then continue
          out ← mkAppM ``cond #[condApps[i]!, vals[i]!, out]
        return some out
      let mut values : Array (String × Expr) := #[]
      let mut undetermined := #[]
      for (k, n) in [(0, "pc"), (1, "a"), (2, "x"), (3, "y"), (4, "s"), (5, "cyc"), (6, "bad")] do
        match ← field k pure with
        | some v => values := values.push (n, v)
        | none =>
          if n == "pc" || n == "bad" then
            let some i := (List.range paths.size).find? (fun i => paths[i]!.2[k]!.isNone) | unreachable!
            throwError "sym_summary: on path {i}, the {n} depends on a callee result left unspecified"
          undetermined := undetermined.push n
      -- RAM pointwise: `fun i => bif path₁ then ram₁ i else …`.
      let ramV ← withLocalDeclD `i (mkConst ``UInt16) fun i => do
        let some body ← field 7 (fun r => return r.beta #[i]) | unreachable!
        mkLambdaFVars #[i] body
      values := values.push ("ram", ramV)
      let mut src := ""
      for (n, v) in values do
        let declName := (← getCurrNamespace) ++ name.getId.appendAfter ("_" ++ n)
        addDef declName v
        let fmt ← withOptions (fun o => o.setBool `pp.funBinderTypes true) <| ppExpr v
        src := src ++ s!"def {declName} :=\n  {fmt}\n\n"
      let sig := ← params.mapM fun p => return (← p.fvarId!.getDecl).userName
      -- The end state for the call theorem, ready to paste: undefined fields are the
      -- existentials `p'` (flags) and `c'` (cycles, when undefined), as in `summary_finish`.
      let mut fldArgs : Std.HashMap String String := {}
      for (f, v) in values do
        let ns ← (paramsOf v).mapM fun p => return toString (← p.fvarId!.getDecl).userName
        fldArgs := fldArgs.insert f (" ".intercalate ns.toList)
      let fldArgs' := fldArgs
      let fld (f : String) (dflt : String) : String :=
        match fldArgs'[f]? with
        | some a => (s!"{name.getId}_{f} {a}").trimAsciiEnd.toString
        | none => dflt
      let prgName := (← inputs.findM? fun fv => return (← fv.getDecl).userName == `prg).map (fun _ => "prg") |>.getD "prg"
      let endState := s!"⟨⟨{fld "pc" "?"}, {fld "a" "a'"}, {fld "x" "x'"}, {fld "y" "y'"}, {fld "s" "s'"}, p'⟩, {fld "ram" "?"}, {prgName}, {fld "cyc" "c'"}, {fld "bad" "?"}⟩"
      logInfo m!"sym_summary {name.getId} end state: {endState}"
      logInfo m!"sym_summary {name.getId}: {paths.size} paths; definitions take {sig}{
        if undetermined.isEmpty then m!"" else m!"; not defined (they depend on callee results the callee theorems leave unspecified): {undetermined}"}"
      if sym_summary.print.get (← getOptions) then logInfo m!"{src}"
      let some post := post? | return
      -- The statement: `fun f => ∃ j p' [a' …] [c'], f = run (j + m) END ∧ (p' &&& 4 == 0) = false`,
      -- `END` the definitions applied to the inputs, undefined fields existential.
      let some (_, lhs, _) := runEq.eq? | throwError "sym_summary: not an equation"
      let some r := lhs.find? (·.isAppOfArity ``Smb.CPU.runTo 4) | throwError "sym_summary finish: no `runTo` in{indentExpr lhs}"
      let n := r.appArg!
      unless n.isAppOfArity ``HAdd.hAdd 6 do throwError "sym_summary finish: the fuel is not `m + K`:{indentExpr n}"
      let m := n.getArg! 4
      let S ← runState runEq
      let regs0 := S.getArg! 0
      let ns ← getCurrNamespace
      let defApp (f : String) : Option Expr := (values.find? (fun (v : String × Expr) => v.1 == f)).map fun v =>
        mkAppN (mkConst (ns ++ name.getId.appendAfter ("_" ++ f))) (paramsOf v.2)
      let regNames := #["pc", "a", "x", "y", "s"]
      let mut binders : Array (Name × (Array Expr → TacticM Expr)) :=
        #[(`j, fun _ => pure (mkConst ``Nat)), (`p', fun _ => pure (mkConst ``UInt8))]
      for k in [1:5] do
        if (defApp regNames[k]!).isNone then
          binders := binders.push (Name.mkSimple (regNames[k]! ++ "'"), fun _ => pure (mkConst ``UInt8))
      if (defApp "cyc").isNone then binders := binders.push (`c', fun _ => pure (mkConst ``UInt64))
      let hasW := values.any fun (_, v) => (v.find? (·.isConstOf ``ramWitness)).isSome
      if hasW then binders := binders.push (`w, fun _ => inferType (mkConst ``ramWitness))
      let Q ← withLocalDeclD `f (← inferType S) fun f => withLocalDeclsD binders fun xs => do
        let j := xs[0]!
        let p' := xs[1]!
        let mut i := 2
        let mut rs : Array Expr := #[]
        for k in [0:5] do
          match defApp regNames[k]! with
          | some e => rs := rs.push e
          | none => rs := rs.push xs[i]!; i := i + 1
        let cyc := (defApp "cyc").getD xs[i]!
        let some ramV := values.find? (·.1 == "ram") | unreachable!
        let ramConst := mkConst (ns ++ name.getId.appendAfter "_ram")
        let ram := if hasW then mkAppN (mkApp ramConst xs.back!) (paramsOf ramV.2) else mkAppN ramConst (paramsOf ramV.2)
        let some bad := defApp "bad" | unreachable!
        let F := mkAppN S.getAppFn #[mkAppN regs0.getAppFn (rs.push p'), ram, S.getArg! 2, cyc, bad]
        let jm ← mkAppM ``HAdd.hAdd #[j, m]
        let lhs' := lhs.replace fun e => if e == n then some jm else if e == S then some F else none
        let flag ← Term.elabTermEnsuringType (← `(($(mkIdent `p') &&& 4 == 0) = false)) (mkSort 0)
        let flag ← instantiateMVars flag
        let mut body ← mkAppM ``And #[← mkEq f lhs', flag]
        for x in xs.reverse do body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]
        mkLambdaFVars #[f] body
      -- `Q` may use only the theorem's arguments: the locals declared before `sym_post`.
      let postIdx := (← post.getDecl).index
      for fv in (collectFVars {} Q).fvarIds do
        unless (← fv.getDecl).index < postIdx do
          throwError "sym_summary finish: the statement uses {mkFVar fv}, not a theorem argument"
      -- Handed to `sym_theorem` through a named metavariable.
      let carrier ← mkFreshExprMVar (← inferType Q) (userName := `sym_theorem_post)
      carrier.mvarId!.assign Q
      logInfo m!"sym_summary {name.getId} statement:{indentExpr (Q.beta #[mkConst `f]).headBeta}"
      for g in pending do
        -- The path's goal `sym_post f'` is closed by a proof of `Q f'`; `sym_theorem` replaces
        -- `sym_post` by `Q` in the whole proof, which makes the types agree.
        let tgt := (← instantiateMVars (← g.getType)).consumeMData
        let h ← g.withContext do mkFreshExprMVar (Q.beta #[tgt.appArg!]).headBeta
        g.assign h
        setGoals [h.mvarId!]
        evalTactic finTac.get!
        unless (← getGoals).isEmpty do throwError "sym_summary finish: a path is not proved"
      setGoals []

/-- `sym_summarize NAME binders : type := by tactics`: elaborate like `example`, keeping the
definitions that `sym_summary` adds. Nothing else is declared. -/
elab "sym_summarize " _n:ident sig:declSig " := " "by " tac:tacticSeq : command => do
  Command.runTermElabM fun _ => do
    let (binders, type) := expandDeclSig sig
    Term.elabBinders binders.getArgs fun _ => do
      let ty ← Term.elabType type
      Term.synthesizeSyntheticMVarsNoPostponing
      let goal ← mkFreshExprMVar ty
      Term.runTactic goal.mvarId! (← `(Lean.Parser.Term.byTactic| by $tac)) .term


/-- `e` with every `fun x => f x` (anywhere) reduced to `f`. -/
partial def etaAll (e : Expr) : Expr :=
  e.replace fun t => match t with
    | .lam .. => let t' := t.eta; if t' != t then some (etaAll t') else none
    | _ => none

/-- The first differing pair of subterms, comparing by hash (metavariables match anything). -/
partial def firstDiff (a b : Expr) : Option (Expr × Expr) :=
  if a.hash == b.hash || a.isMVar || b.isMVar then none else
  match a, b with
  | .app .., .app .. =>
    if a.getAppFn.hash != b.getAppFn.hash || a.getAppNumArgs != b.getAppNumArgs then some (a, b)
    else (a.getAppArgs.zip b.getAppArgs).findSome? fun (x, y) =>
      -- report the enclosing application when the difference is an atom
      match firstDiff x y with
      | some (x', y') => if (x'.isApp && !x'.isAppOf ``OfNat.ofNat) || x'.isLambda then some (x', y') else some (a, b)
      | none => none
  | .lam _ t x _, .lam _ u y _ => (firstDiff t u).orElse fun _ => firstDiff x y
  | _, _ => some (a, b)

/-- Close `lhs = rhs` by `rfl` only if the sides agree up to eta; otherwise report where they differ
and fail, instead of letting `rfl` unfold for a long time. -/
elab "eq_check" : tactic => withMainContext do
  let some (_, l, r) := (← instantiateMVars (← getMainTarget)).eq? | throwError "eq_check: not an equation"
  match firstDiff (etaAll (dropDead l)) (etaAll (dropDead r)) with
  | none => evalTactic (← `(tactic| rfl))
  | some (a, b) =>
    throwError "eq_check: the sides differ at{indentExpr a}\nand{indentExpr b}"

/-- The exactness proof of a path for `sym_summary … exact`: inline the names (`subst_vars`), unfold
the summary's field definitions, and decide the fold's conditions in order up to the first true one: by
rewriting with the path's split facts (`t = true/false`, `e = lit`), or else by SAT on that condition alone.
Then compare by `rfl`. The values are never simplified or compared by SAT; only the I flag may still use it. -/
elab "exact_finish " n:ident : tactic => do
  let env ← getEnv
  let ns ← getCurrNamespace
  let pre := (ns ++ n.getId).toString ++ "_"
  let names := env.constants.fold (init := #[]) fun acc c _ =>
    let s := c.toString
    if s.startsWith pre && !(s.drop pre.length).toString.contains '.' then acc.push c else acc
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| subst_vars))
  -- The values the generator settled (`hsettled : e = b`), before anything rewrites inside `e`.
  let hs := mkIdent `hsettled
  evalTactic (← `(tactic| (repeat ((try simp only [Settled] at $hs:ident); (try simp only [$hs:ident] at ⊢); clear $hs:ident))))
  -- Facts about a negation, `(!x) = true`, as facts about `x`, which other paths test.
  evalTactic (← `(tactic| (try simp only [Bool.not_eq_true', Bool.not_eq_false'] at *)))
  let isCond (c : Name) : Bool :=
    let suf := ((c.toString).drop pre.length).toString
    suf.startsWith "c" && suf.length > 1 && (suf.drop 1).all Char.isDigit
  let idx (c : Name) : Nat := (((c.toString).drop (pre.length + 1)).toString).toNat!
  let condNames := (names.filter isCond).qsort (idx · < idx ·)
  let fieldNames := names.filter (!isCond ·)
  let mkThms (g : MVarId) : TacticM SimpTheorems := g.withContext do
    -- Only the path facts and the `bif`/`&&` basics: a lemma that rewrote inside a split test
    -- (`!!b`, literal arithmetic) would stop the fact about it from matching.
    let mut thms : SimpTheorems := {}
    for c in [``Bool.cond_true, ``Bool.cond_false, ``Bool.and_true, ``Bool.true_and,
        ``Bool.and_false, ``Bool.false_and, ``Bool.not_true, ``Bool.not_false] do
      thms ← thms.addConst c
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, l, r) := ty.eq? | continue
      if r.isConstOf ``Bool.true || r.isConstOf ``Bool.false || (!l.isFVar && r.isRawNatLit) ||
          (!l.isFVar && (r.isAppOf ``OfNat.ofNat)) then
        thms ← thms.add (.fvar d.fvarId) #[] (mkFVar d.fvarId)
    return thms
  let mkCtx (thms : SimpTheorems) : MetaM Simp.Context := do
    Simp.mkContext (config := { decide := false, maxSteps := 10000000 })
      (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  -- Unfold the fields, not the path conditions (also `NAME_ram` not applied to an address).
  let g0 ← getMainGoal
  let mut g ← g0.withContext do
    let tgt ← instantiateMVars (← g0.getType)
    g0.replaceTargetDefEq (← Core.betaReduce (← deltaExpand tgt fieldNames.contains))
  -- Decide the conditions in order, up to the first true one: by rewriting with the path's facts,
  -- or else on their own by SAT (exclusions that only hold semantically, such as `t == 0` against
  -- `t + 61 == 0`).
  let base ← mkThms g
  for c in condNames do
    let tgt ← instantiateMVars (← g.getType)
    let some t := tgt.find? (·.isAppOf c) | continue
    let (ty, pf, val?) ← g.withContext do
      let body ← Core.betaReduce (← deltaExpand t (· == c))
      let (r, _) ← Meta.simp body (← mkCtx base)
      if r.expr.isConstOf ``Bool.true || r.expr.isConstOf ``Bool.false then
        let b := r.expr.isConstOf ``Bool.true
        return (← mkEq t r.expr, ← r.getProof, some b)
      if let some p ← settleProof g `_none body true then return (← mkEq t (toExpr true), p, some true)
      if let some p ← settleProof g `_none body false then return (← mkEq t (toExpr false), p, some false)
      return (mkConst ``True, mkConst ``True.intro, none)
    let some val := val? | continue
    let g' ← g.assert `hc ty pf
    g := (← g'.intro1P).2
    if val then break
  let thms ← mkThms g
  -- With one path there may be nothing to rewrite, which `simpGoal` reports as an error.
  let gEnd? : Option MVarId ← try
      let (r, _) ← g.withContext do simpGoal g (← mkCtx thms) (simprocs := #[])
      pure (r.map (·.2))
    catch _ => pure (some g)
  let some gEnd := gEnd? | return
  setGoals [gEnd]
  evalTactic (← `(tactic| call_fuel))
  evalTactic (← `(tactic| repeat apply Exists.intro))
  evalTactic (← `(tactic| apply And.intro))
  evalTactic (← `(tactic| · eq_check))
  evalTactic (← `(tactic| · first | assumption | (simp only [bne, Bool.not_eq_true'] at *; assumption) | bv_decide (config := { enums := false })))
  -- A path without a callee RAM witness: any `w`.
  evalTactic (← `(tactic| all_goals exact fun _ => 0))

/-- `sym_theorem NAME binders : run := by tactics`, with `sym_summary … finish (tac)` among the
tactics: the call theorem `NAME : ∀ binders, ∃ j p' …, run = run (j + m) END ∧ (p' &&& 4 == 0) = false`
(`run` is `((CPU.runTo stop (m + K)).run S).2`), whose end state `END` the summary generates. The
statement is left open (`?post run`) until `sym_summary` has the definitions; one symbolic
execution then both generates and proves them. -/
elab "sym_theorem " n:ident sig:declSig " := " "by " tac:tacticSeq : command => do
  Command.runTermElabM fun _ => do
    let (binders, type) := expandDeclSig sig
    Term.elabBinders binders.getArgs fun xs => do
      let run ← Term.elabTerm type none
      Term.synthesizeSyntheticMVarsNoPostponing
      let run ← instantiateMVars run
      -- The statement is a local `sym_post` while the tactics run (a metavariable in the target
      -- slows every step of `sym_run`); `sym_summary` provides it at the end.
      withLocalDeclD `sym_post (← mkArrow (← inferType run) (mkSort 0)) fun post => do
        let goal ← mkFreshExprMVar (mkApp post run)
        Term.runTactic goal.mvarId! (← `(Lean.Parser.Term.byTactic| by $tac)) .term
        let some carrier := (← getMCtx).findUserName? `sym_theorem_post
          | throwError "sym_theorem: no `sym_summary … finish` provided the statement"
        let Q ← instantiateMVars (mkMVar carrier)
        let val ← instantiateMVars goal
        let val := val.replaceFVar post Q
        let ty := (Q.beta #[run]).headBeta
        if ty.hasMVar || val.hasMVar then throwError "sym_theorem: the statement or proof is incomplete"
        -- The binders' types may still hold instantiated metavariables (numerals' instances).
        let ty ← instantiateMVars (← mkForallFVars xs ty)
        let val ← instantiateMVars (← mkLambdaFVars xs val)
        let declName := (← getCurrNamespace) ++ n.getId
        addDecl (.thmDecl { name := declName, levelParams := [], type := ty, value := val })

/-- Finish a path of a call theorem stated with `sym_summary NAME`'s definitions. Inline the names
`sym_run` gave to intermediate values (`subst_vars`), unfold the field definitions, decide each
path condition `NAME_cᵢ …` on its own (`bv_decide` with the path's facts; `extra` is unfolded
there too), rewrite with the answers so that each field is this path's value, simplify both sides
with `sym_exec`'s simp set (as the generator did) and compare. -/
elab "summary_finish " n:ident " [" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let env ← getEnv
  let ns ← getCurrNamespace
  let resolve (suffix : String) : Option Name :=
    [ns ++ n.getId.appendAfter suffix, n.getId.appendAfter suffix].find? env.contains
  let fields := ["_pc", "_a", "_x", "_y", "_s", "_ram", "_bad", "_cyc"].filterMap resolve
  let fieldLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    fields.toArray.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $(mkIdent f):ident)
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| subst_vars))
  evalTactic (← `(tactic| (try simp only [bne] at *)))
  evalTactic (← `(tactic| simp only [$fieldLemmas,*]))
  -- The path conditions in the goal, in order.
  let target ← instantiateMVars (← getMainTarget)
  let isCond (c : Name) : Bool := (c.toString.splitOn (n.getId.toString ++ "_c")).length > 1
  let apps := (target.foldConsts #[] fun c acc => if isCond c then acc.push c else acc)
  let mut hyps : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for c in apps do
    -- every application of `c` in the goal (one, the arguments being the inputs)
    let some t := (target.find? fun e => e.isAppOf c) | continue
    let tStx ← withMainContext <| Term.TermElabM.run' (Term.exprToSyntax t)
    let mut lastErr : MessageData := m!""
    let mut decided := false
    for lit in [true, false] do
      let saved ← saveState
      try
        -- Proved on a goal of its own, now (a `have … := by …` would postpone the proof, and a
        -- wrong guess would be used before it fails).
        let main ← getMainGoal
        let ty ← main.withContext do mkEq t (toExpr lit)
        let m ← main.withContext do mkFreshExprMVar ty
        setGoals [m.mvarId!]
        evalTactic (← `(tactic| (
          simp only [$(mkIdent c):ident, bne, $extra,*]
          fun_congr
          bv_decide (config := { enums := false }))))
        unless (← getGoals).isEmpty do throwError "not closed"
        let hName ← main.withContext do return (← getLCtx).getUnusedName `hcond
        let (_, main') ← (← main.assert hName ty (← instantiateMVars m)).intro1P
        setGoals [main']
        hyps := hyps.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent hName):ident))
        decided := true
        break
      catch e =>
        lastErr := e.toMessageData
        saved.restore
    if !decided && sym_summary.print.get (← getOptions) then
      logInfo m!"summary_finish: {c} not decided:{indentD lastErr}"
  if sym_summary.print.get (← getOptions) then
    logInfo m!"summary_finish: {apps.size} conditions in the goal, {hyps.size} decided: {apps}"
  evalTactic (← `(tactic| simp only [$hyps,*, Bool.cond_true, Bool.cond_false]))
  evalTactic (← `(tactic| call_fuel))
  evalTactic (← `(tactic| repeat apply Exists.intro))
  evalTactic (← `(tactic| apply And.intro))
  evalTactic (← `(tactic| · first
    | rfl
    | (congr 2
       all_goals (try congr 1)
       all_goals first
         | rfl
         -- The RAM: its definition unfolds only applied to an address.
         | (funext i; simp only [$fieldLemmas,*, $hyps,*, Bool.cond_true, Bool.cond_false]; done)
         | (funext i; simp only [$fieldLemmas,*, $hyps,*, Bool.cond_true, Bool.cond_false]; rfl)
         | (funext i; (try sym_exec [bne, $fieldLemmas,*, $hyps,*]); first | rfl | (fun_congr; bv_decide (config := { enums := false })))
         | (is_regs_eq; congr 1 <;> (try sym_exec [bne]) <;> first | rfl | (fun_congr; bv_decide (config := { enums := false })))
         | ((try sym_exec [bne]) <;> fun_congr <;> bv_decide (config := { enums := false })))))
  evalTactic (← `(tactic| · bv_decide (config := { enums := false })))

/-- `summary_finish`, unfolding `extra` in the path hypotheses first (for summaries whose
conditions unfolded a callee's helper, see `unfoldSym`). -/
macro "summary_finish_all " n:ident " [" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intros
  (try simp only [bne, $extra,*] at *)
  summary_finish $n [$extra,*]))

/-- The previous finish: inline the names, then `call_finish` over the whole state with every
`NAME_…` definition unfolded (the SAT solver picks the fold's branch and compares the values at
once). Lighter than `summary_finish` on summaries whose values nest callee closed forms. -/
elab "summary_finish_whole " n:ident : tactic => do
  let env ← getEnv
  let ns ← getCurrNamespace
  let pre := (ns ++ n.getId).toString ++ "_"
  let names := env.constants.fold (init := #[]) fun acc c _ =>
    let s := c.toString
    if s.startsWith pre then
      let suf := (s.drop pre.length).toString
      if ["pc", "a", "x", "y", "s", "ram", "bad"].contains suf ||
          (suf.startsWith "c" && suf.length > 1 && (suf.drop 1).all Char.isDigit) then acc.push c else acc
    else acc
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← names.mapM fun c => `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident)
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| subst_vars))
  evalTactic (← `(tactic| call_finish [$lemmas,*]))


/-! ## A summary's memory interface -/

/-- Unfold, in `e`, every application of a constant of `Smb.Routine` to the address `i` (a RAM form
`f args i`) until none is left, beta- and zeta-reducing. Other uses of those constants (values such
as `mphCarry ram`, or a RAM form that is only an argument) stay as they are. -/
partial def unfoldReads (i : Expr) (e : Expr) : MetaM Expr := do
  let e' ← Meta.transform e (post := fun t => do
    let fn := t.getAppFn
    let isRead := t.isApp && t.appArg! == i && match fn.constName? with
      | some c => (`Smb.Routine).isPrefixOf c
      | none => false
    if !isRead then
      -- `(fun j => …) i`, left over from a RAM form passed as an argument
      if t.isApp && fn.isLambda then return .visit t.headBeta
      return .continue
    let some u ← delta? t | return .continue
    return .visit (← Meta.zetaReduce u.headBeta))
  let e' ← Meta.zetaReduce (← Core.betaReduce e')
  if e' == e then return e
  unfoldReads i e'

/-- The address terms `X` that `e` compares with `i`, in `i == X` or `X == i`. -/
def comparedWith (i e : Expr) : Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut todo : Array Expr := #[e]
  let mut seen : Std.HashSet Expr := {}
  while !todo.isEmpty do
    let t := todo.back!
    todo := todo.pop
    if seen.contains t then continue
    seen := seen.insert t
    if t.isAppOfArity ``BEq.beq 4 then
      let a := t.getArg! 2
      let b := t.getArg! 3
      if a == i && !b.containsFVar i.fvarId! && !out.contains b then out := out.push b
      else if b == i && !a.containsFVar i.fvarId! && !out.contains a then out := out.push a
    match t with
    | .app f a => todo := todo.push f |>.push a
    | .lam _ d b _ | .forallE _ d b _ => todo := todo.push d |>.push b
    | .letE _ d v b _ => todo := todo.push d |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- `summary_interface NAME`: from the definition `NAME_ram params i`, define
- `NAME_writes params i`: `i` is one of the addresses the RAM form compares it with. This is a may-change
  footprint of the final RAM, not a record of bus writes: a byte written with its old value, or written and
  restored, need not be in it;
- `NAME_at params i`: the byte there, opaque;
and prove `NAME_ram_frame` (`NAME_writes … i = false → NAME_ram … i = ram i`) and `NAME_ram_read`
(`NAME_ram … i = bif NAME_writes … i then NAME_at … i else ram i`) by rewriting: with every `i == X`
false, each path's RAM form reduces to `ram i`. A caller given `NAME_ram_read` and `NAME_writes`
reads an unwritten byte without expanding the summary. -/
elab "summary_interface " n:ident : command => do
  Command.runTermElabM fun _ => do
    let ns ← getCurrNamespace
    let nm (s : String) : Name := ns ++ n.getId.appendAfter s
    let info ← getConstInfo (nm "_ram")
    lambdaTelescope info.value! fun xs body => do
      let i := xs.back!
      let params := xs.pop
      let some ram ← params.findM? (fun p => return (← p.fvarId!.getDecl).userName == `ram)
        | throwError "summary_interface: no parameter named `ram`"
      let unfolded ← unfoldReads i body
      let addrs := comparedWith i unfolded
      -- `NAME_writes`
      let mut wr : Expr := mkConst ``Bool.false
      for x in addrs.reverse do
        wr := mkApp2 (mkConst ``or) (← mkAppM ``BEq.beq #[i, x]) wr
      let addDef (declName : Name) (v : Expr) : MetaM Unit := do
        let v ← mkLambdaFVars xs v
        addDecl (.defnDecl (mkDefinitionValEx declName [] (← inferType v) v (.regular 0) .safe [declName]))
        enableRealizationsForConst declName
      addDef (nm "_writes") wr
      setReducibilityStatus (nm "_writes") .reducible
      addDef (nm "_at") (mkAppN (mkConst (nm "_ram")) xs)
      setReducibilityStatus (nm "_at") .irreducible
      let wrApp := mkAppN (mkConst (nm "_writes")) xs
      let ramApp := mkAppN (mkConst (nm "_ram")) xs
      -- `NAME_ram_frame`: rewrite with `(i == X) = false` for every `X`.
      let frameTy ← mkArrow (← mkEq wrApp (mkConst ``Bool.false)) (← mkEq ramApp (mkApp ram i))
      let frame ← mkFreshExprMVar frameTy
      let (h, g) ← frame.mvarId!.intro1
      let g ← g.replaceTargetDefEq (← mkEq unfolded (mkApp ram i))
      let gs ← Tactic.run g do
        let hs := mkIdent ((← g.getDecl).lctx.get! h).userName
        evalTactic (← `(tactic| simp only [$(mkIdent (nm "_writes")):ident, Bool.or_eq_false_iff, Bool.or_false] at $hs:ident))
        evalTactic (← `(tactic| simp only [$hs:ident, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.cond_false, Bool.cond_self]))
      unless gs.isEmpty do throwError "summary_interface: `NAME_ram_frame` not proved; left:{goalsToMessageData gs}"
      let frameV ← instantiateMVars frame
      let frameName := nm "_ram_frame"
      addDecl (.thmDecl { name := frameName, levelParams := [], type := ← mkForallFVars xs frameTy, value := ← mkLambdaFVars xs frameV })
      -- `NAME_ram_read`
      let atApp := mkAppN (mkConst (nm "_at")) xs
      let readTy ← mkEq ramApp (mkApp4 (mkConst ``cond [1]) (mkConst ``UInt8) wrApp atApp (mkApp ram i))
      let read ← mkFreshExprMVar readTy
      let gs ← Tactic.run read.mvarId! do
        evalTactic (← `(tactic| cases hw : $(← Term.exprToSyntax wrApp):term))
        let args ← xs.mapM fun a => (Term.exprToSyntax a : TermElabM Term)
        evalTactic (← `(tactic| · simpa only [Bool.cond_false, hw] using $(mkIdent frameName) $args* hw))
        evalTactic (← `(tactic| · simp only [Bool.cond_true]; delta $(mkIdent (nm "_at")); rfl))
      unless gs.isEmpty do throwError "summary_interface: `NAME_ram_read` not proved"
      addDecl (.thmDecl { name := nm "_ram_read", levelParams := [], type := ← mkForallFVars xs readTy, value := ← mkLambdaFVars xs (← instantiateMVars read) })
      logInfo m!"summary_interface {n.getId}: {addrs.size} addresses:{indentD (MessageData.joinSep (addrs.toList.map (m!"{·}")) ", ")}"

/-- `summary_regs NAME`: `NAME_s_eq : NAME_s … = sp` and `NAME_bad_eq : NAME_bad … = bad` (or `false` when `bad`
is not an input), each if `rfl` or SAT proves it, the path conditions being opaque atoms: the routine returns with the
stack pointer it got, and did nothing the model flags as unsupported. A caller needs them to return through
the stack, and they save it unfolding the summary's fold. -/
elab "summary_regs " n:ident : command => do
  Command.runTermElabM fun _ => do
    let ns ← getCurrNamespace
    let nm (s : String) : Name := ns ++ n.getId.appendAfter s
    let prove (field : String) (rhs : Array Expr → MetaM Expr) (thm : String) : TermElabM Unit := do
      let info ← getConstInfo (nm field)
      let arity ← forallTelescope info.type fun xs _ => pure xs.size
      forallBoundedTelescope info.type arity fun xs _ => do
        let ty ← mkEq (mkAppN (mkConst (nm field)) xs) (← rhs xs)
        let m ← mkFreshExprMVar ty
        let saved ← saveState
        try
          let gs ← Tactic.run m.mvarId! do
            evalTactic (← `(tactic| delta $(mkIdent (nm field)):ident))
            evalTactic (← `(tactic| first | rfl | bv_decide (config := { enums := false })))
          unless gs.isEmpty do throwError "not closed"
          let thmTy ← mkForallFVars xs ty
          let thmV ← mkLambdaFVars xs (← instantiateMVars m)
          addDecl (.thmDecl { name := nm thm, levelParams := [], type := thmTy, value := thmV })
        catch e =>
          saved.restore
          logInfo m!"{nm thm} not proved: {e.toMessageData}"
    let param (xs : Array Expr) (name : Name) : MetaM (Option Expr) :=
      xs.findM? fun p => return (← p.fvarId!.getDecl).userName == name
    prove "_s" (fun xs => do
      let some sp ← param xs `sp | throwError "no input `sp`"
      return sp) "_s_eq"
    prove "_bad" (fun xs => return (← param xs `bad).getD (mkConst ``Bool.false)) "_bad_eq"

/-- `summary_go NAME ADDR EXIT`: from `NAME_call`, whose end PC is the definition `NAME_pc …`, the theorem
`NAME_EXIT_call`, with the extra hypothesis `NAME_pc … = ADDR` and the literal `ADDR` as the end PC. A caller
following one exit then has no PC to split on, so the summary's many paths stay one. -/
elab "summary_go " n:ident a:num e:ident : command => do
  Command.runTermElabM fun _ => do
    let ns ← getCurrNamespace
    let nm (s : String) : Name := ns ++ n.getId.appendAfter s
    let info ← getConstInfo (nm "_call")
    forallTelescope info.type fun xs ty => do
      let some pcApp := ty.find? (·.isAppOf (nm "_pc")) | throwError "summary_go: no `{nm "_pc"}` in the statement"
      if pcApp.hasLooseBVars then throwError "summary_go: the PC depends on a witness"
      let lit ← Term.elabTerm (← `(($a : UInt16))) (some (mkConst ``UInt16))
      Term.synthesizeSyntheticMVarsNoPostponing
      let lit ← instantiateMVars lit
      let replaced (v : Expr) : Expr := ty.replace fun t => if t == pcApp then some v else none
      let hTy ← mkEq pcApp lit
      let call := mkAppN (mkConst (nm "_call")) xs
      withLocalDeclD `hgo hTy fun h => do
        let motive ← withLocalDeclD `v (mkConst ``UInt16) fun v => mkLambdaFVars #[v] (replaced v)
        let pf ← mkAppM ``Eq.mp #[← mkCongrArg motive h, call]
        let newTy ← mkForallFVars (xs.push h) (replaced lit)
        let val ← mkLambdaFVars (xs.push h) pf
        addDecl (.thmDecl { name := nm s!"_{e.getId}_call", levelParams := [], type := newTy, value := val })
/-- `split_fold PREFIX`: split on the first summary condition (a constant starting with `PREFIX`) tested by a `bif` in
the goal, and rewrite with it. -/
elab "split_fold " p:ident : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let isC (c : Expr) : Bool := match c.getAppFn.constName? with
    | some k => (k.toString.splitOn p.getId.toString).length > 1
    | none => false
  let some e := t.find? (fun e => e.isAppOfArity ``cond 4 && !(e.getArg! 1).hasLooseBVars && isC (e.getArg! 1))
    | throwError "split_fold: no condition"
  let stx ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| cases hc : $stx:term <;> simp only [hc, Bool.cond_true, Bool.cond_false]))

/-- A run from a state at `stop` leaves it unchanged, whatever the fuel. -/
theorem runTo_snd_at_stop {s : Plain} (stop : UInt16) (n : Nat) (h : s.regs.pc = stop) :
    ((CPU.runTo (σ := Plain) stop n).run s).2 = s := by
  cases n with
  | zero => rw [runTo_run_zero]
  | succ n => exact runTo_snd_stop s stop n h

/-- `summary_reach NAME ADDR`: from `NAME_call`, for `stop := ADDR` where the end PC is `ADDR`, the theorem `NAME_reach`:
running to `ADDR` gives exactly the end state, `∃ p' …, ((runTo ADDR (m + K)).run S).2 = END ∧ (p' &&& 4 == 0) = false`. The stop
hypothesis of `NAME_call` must allow `ADDR`, which then no longer appears. -/
elab "summary_reach " n:ident a:num : command => do
  Command.runTermElabM fun _ => do
    let ns ← getCurrNamespace
    let nm (s : String) : Name := ns ++ n.getId.appendAfter s
    let info ← getConstInfo (nm "_call")
    let lit ← Term.elabTerm (← `(($a : UInt16))) (some (mkConst ``UInt16))
    Term.synthesizeSyntheticMVarsNoPostponing
    let lit ← instantiateMVars lit
    let t1 := info.type.bindingBody!.instantiate1 lit
    let hstopM ← mkFreshExprMVar t1.bindingDomain!
    let gs ← Tactic.run hstopM.mvarId! do
      evalTactic (← `(tactic| (intro a h; revert h; bv_decide (config := { enums := false }))))
    unless gs.isEmpty do throwError "summary_reach: the stop hypothesis does not allow it"
    let hstopPf ← instantiateMVars hstopM
    let t2 := t1.bindingBody!.instantiate1 hstopPf
    forallTelescope t2 fun xs body => do
      let call := mkAppN (mkApp2 (mkConst (nm "_call")) lit hstopPf) xs
      let pcId := mkIdent (nm "_pc")
      let steps (g : MVarId) (close : TacticM Unit) : TermElabM (List MVarId) := do
        Tactic.run g do
          let g ← getMainGoal
          let g ← g.assert `h body call
          let (_, g) ← g.intro1P
          setGoals [g]
          evalTactic (← `(tactic| rcases $(mkIdent `h):ident with ⟨j, $(mkIdent `h):ident⟩))
          evalTactic (← `(tactic| simp (disch := simp only [$pcId:ident]) only [runTo_snd_at_stop] at $(mkIdent `h):ident))
          close
      -- First to read the statement off the simplified hypothesis, then to prove it.
      let saved ← saveState
      let tyRef ← IO.mkRef (mkConst ``True)
      let probe ← mkFreshExprMVar (mkConst ``True)
      discard <| steps probe.mvarId! do
        let ty ← withMainContext do
          instantiateMVars (← getLocalDeclFromUserName `h).type
        tyRef.set ty
        evalTactic (← `(tactic| exact True.intro))
      let ty ← tyRef.get
      saved.restore
      let m ← mkFreshExprMVar ty
      let gs ← steps m.mvarId! do
        evalTactic (← `(tactic| exact $(mkIdent `h):ident))
      unless gs.isEmpty do throwError "summary_reach: not closed"
      let thmTy ← mkForallFVars xs ty
      let thmV ← mkLambdaFVars xs (← instantiateMVars m)
      addDecl (.thmDecl { name := nm "_reach", levelParams := [], type := thmTy, value := thmV })

end Smb.Symbolic

