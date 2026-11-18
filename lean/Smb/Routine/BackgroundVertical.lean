import Smb.Routine.PlayerBG

/-!
# Vertical effects of the ordinary background-collision summaries

These final-value contracts preserve Y high, position subpixel and falling gravity.
Y low is unchanged or snapped to its preceding tile row; active gravity is unchanged
or set to $70 by the spring-landing path. The side-check RAM witness is arbitrary.

The projections reuse small callee facts without executing the background code again.
Attaching them to actual execution retains the original call theorem's code, flag,
selected-exit and exceptional-path premises. They are not a bus-write trace.
-/
namespace Smb.Routine.BackgroundVertical

/-- The early prologue changes state/collision bits, but none of these vertical bytes. -/
theorem early_keeps (ram : UInt16 → UInt8) (i : UInt16)
    (hi : i = 0xB5 ∨ i = 0x416 ∨ i = 0xCE ∨ i = 0x70A ∨ i = 0x709) :
    bgPre_ram ram i = ram i := by
  apply bgPre_ram_frame
  simp only [bgPre_writes]
  bv_decide

theorem side_anchors (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (hi : i = 0xB5 ∨ i = 0x416 ∨ i = 0x70A) :
    bgSide_ram w sp ram prg i = ram i := by
  apply bgSide_ram_frame
  simp only [bgSide_writes, stackAt]
  bv_decide

theorem impede_anchors (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (hi : i = 0xB5 ∨ i = 0x416 ∨ i = 0x70A) :
    bgImpede_ram sp ram prg i = ram i := by
  apply bgImpede_ram_frame
  simp only [bgImpede_writes]
  bv_decide

/-- The changed byte is projected once from the smaller landing/impeding summary. -/
theorem chkFoot_y (a sp : UInt8) (ram prg : UInt16 → UInt8) :
    chkFoot_ram a sp ram prg 0xCE = ram 0xCE ∨
    chkFoot_ram a sp ram prg 0xCE = ram 0xCE &&& 0xF0 := by
  simp only [chkFoot_ram]
  bv_decide

theorem chkFoot_gravity (a sp : UInt8) (ram prg : UInt16 → UInt8) :
    chkFoot_ram a sp ram prg 0x709 = ram 0x709 ∨
    chkFoot_ram a sp ram prg 0x709 = 0x70 := by
  simp only [chkFoot_ram]
  bv_decide

-- Instantiate the checked small byte lemma at each concrete chkFoot call in this goal.
-- The traversal does not unfold a summary or modify any shared tactic.
open Lean Elab Tactic Meta in
elab "foot_vertical_facts" : tactic => withMainContext do
  let mut todo := #[(← getMainTarget)]
  let mut seen : Std.HashSet Expr := {}
  let mut g ← getMainGoal
  let mut count := 0
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if seen.contains e then continue
    seen := seen.insert e
    if e.isAppOfArity `Smb.Routine.chkFoot_ram 5 then
      let theoremName ←
        if ← isDefEq e.appArg! (toExpr (0xCE : UInt16)) then
          pure `Smb.Routine.BackgroundVertical.chkFoot_y
        else if ← isDefEq e.appArg! (toExpr (0x709 : UInt16)) then
          pure `Smb.Routine.BackgroundVertical.chkFoot_gravity
        else throwError "expected only the Y-low or active-gravity projection"
      let pf := mkAppN (mkConst theoremName) (e.getAppArgs.extract 0 4)
      let (_, next) ← (← g.assert (← mkFreshUserName `hchkY) (← inferType pf) pf).intro1P
      g := next
      count := count + 1
    else
      match e with
      | .app f a => todo := todo.push f |>.push a
      | .lam _ d b _ | .forallE _ d b _ => todo := todo.push d |>.push b
      | .letE _ d v b _ => todo := todo.push d |>.push v |>.push b
      | .mdata _ b | .proj _ _ b => todo := todo.push b
      | _ => pure ()
  replaceMainGoal [g]
  logInfo m!"foot vertical projection: reused {count} concrete chkFoot byte facts"

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem foot_y (y sp : UInt8) (ram prg : UInt16 → UInt8) :
    footCheck_ram y sp ram prg 0xCE = ram 0xCE ∨
    footCheck_ram y sp ram prg 0xCE = ram 0xCE &&& 0xF0 := by
  have hh := headPart_keeps y sp 4 ram prg (by decide) 0xCE (by decide)
  sym_exec [footCheck_ram]
  foot_vertical_facts
  sym_exec [hh] at *
  bv_decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem foot_gravity (y sp : UInt8) (ram prg : UInt16 → UInt8) :
    footCheck_ram y sp ram prg 0x709 = ram 0x709 ∨
    footCheck_ram y sp ram prg 0x709 = 0x70 := by
  have hh := headPart_keeps y sp 4 ram prg (by decide) 0x709 (by decide)
  sym_exec [footCheck_ram]
  foot_vertical_facts
  sym_exec [hh] at *
  bv_decide

/-- The side witness is unrestricted: each watched address is outside its scratch
footprint and outside the specified horizontal wall-push writes. -/
theorem side_keeps_vertical (w : UInt16 → UInt8) (sp : UInt8) (prg ram : UInt16 → UInt8)
    (i : UInt16) (hi : i = 0xB5 ∨ i = 0x416 ∨ i = 0xCE ∨ i = 0x70A ∨ i = 0x709) :
    sideRam w sp prg ram i = ram i := by
  simp only [sideRam, sideScratch, impedeRam, stackAt]
  bv_decide

theorem bg_foot_y (sp : UInt8) (ram prg : UInt16 → UInt8) :
    bgFootRam sp prg ram 0xCE = ram 0xCE ∨ bgFootRam sp prg ram 0xCE = ram 0xCE &&& 0xF0 := by
  have h := foot_y (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg
  have hr : bgRam ram 0xCE = ram 0xCE := by
    simpa only [bgRam, bgSize_ram] using early_keeps ram 0xCE (by decide)
  simpa only [bgFootRam, hr] using h

theorem bg_foot_gravity (sp : UInt8) (ram prg : UInt16 → UInt8) :
    bgFootRam sp prg ram 0x709 = ram 0x709 ∨ bgFootRam sp prg ram 0x709 = 0x70 := by
  have h := foot_gravity (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg
  have hr : bgRam ram 0x709 = ram 0x709 := by
    simpa only [bgRam, bgSize_ram] using early_keeps ram 0x709 (by decide)
  simpa only [bgFootRam, hr] using h

theorem side_y (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) :
    bgSide_ram w sp ram prg 0xCE = ram 0xCE ∨
    bgSide_ram w sp ram prg 0xCE = ram 0xCE &&& 0xF0 := by
  have hs := fun s r => side_keeps_vertical w s prg r 0xCE (by decide)
  simpa only [bgFootRam, bgY, bgRam, bgSide_ram, hs] using bg_foot_y sp ram prg

theorem impede_y (sp : UInt8) (ram prg : UInt16 → UInt8) :
    bgImpede_ram sp ram prg 0xCE = ram 0xCE ∨
    bgImpede_ram sp ram prg 0xCE = ram 0xCE &&& 0xF0 := by
  simpa only [bgFootRam, bgY, bgRam, bgImpede_ram] using bg_foot_y sp ram prg

theorem side_gravity (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) :
    bgSide_ram w sp ram prg 0x709 = ram 0x709 ∨ bgSide_ram w sp ram prg 0x709 = 0x70 := by
  have hs := fun s r => side_keeps_vertical w s prg r 0x709 (by decide)
  simpa only [bgFootRam, bgY, bgRam, bgSide_ram, hs] using bg_foot_gravity sp ram prg

theorem impede_gravity (sp : UInt8) (ram prg : UInt16 → UInt8) :
    bgImpede_ram sp ram prg 0x709 = ram 0x709 ∨ bgImpede_ram sp ram prg 0x709 = 0x70 := by
  simpa only [bgFootRam, bgY, bgRam, bgImpede_ram] using bg_foot_gravity sp ram prg

/-- Background collision cannot add downward displacement; alignment removes at most 15 pixels. -/
theorem side_y_bound (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) :
    let out := bgSide_ram w sp ram prg
    let before : UInt32 := (ram 0xB5).toUInt32 <<< 8 ||| (ram 0xCE).toUInt32
    let after : UInt32 := (out 0xB5).toUInt32 <<< 8 ||| (out 0xCE).toUInt32
    after ≤ before ∧ before - after ≤ 15 := by
  have hh := side_anchors w sp ram prg 0xB5 (by decide)
  have hy := side_y w sp ram prg
  dsimp only
  bv_decide

theorem impede_y_bound (sp : UInt8) (ram prg : UInt16 → UInt8) :
    let out := bgImpede_ram sp ram prg
    let before : UInt32 := (ram 0xB5).toUInt32 <<< 8 ||| (ram 0xCE).toUInt32
    let after : UInt32 := (out 0xB5).toUInt32 <<< 8 ||| (out 0xCE).toUInt32
    after ≤ before ∧ before - after ≤ 15 := by
  have hh := impede_anchors sp ram prg 0xB5 (by decide)
  have hy := impede_y sp ram prg
  dsimp only
  bv_decide

end Smb.Routine.BackgroundVertical
