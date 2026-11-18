import Smb.Routine.FloorClip
import Smb.Routine.JumpSwimSub
import Smb.Routine.JumpStart
import Smb.Vertical

/-!
# A small invariant for the $90 falling-gravity regime

`safe` relates subpixel residue, velocity and active gravity. It permits an arbitrary
retained subpixel after a lift reset and excludes a six-pixel downward gravity step.
The JumpSwimSummary adapter connects the arithmetic to an existing ROM routine result.

This is conditional on the specified gravity/state transitions, not an invariant of
all legal gameplay. Slower jump classes use a separate `lowSafe` range; swimming,
climbing, mode $0B and unusual event order need their own arguments. A reset's effective
$90 gravity is not a claim that the reset writes the raw VerticalForce byte. Likewise
`bounce_safe` covers movement followed by an overwrite, not an arbitrary isolated write.

The floor-window conclusion does not establish that collision dispatch selects a
landable tile, that lifts/springs cannot reposition through solids, or that every concrete
frame is represented by the old `Vertical.succs` transition relation.
-/
namespace Smb.Routine.VerticalPhase
open Smb Smb.Routine

def phase (q v : UInt16) : Prop := (q &&& 0xF) = (if v &&& 0x10 = 0 then (0 : UInt16) else 8)

def safe (q v : UInt16) (active : UInt8) : Prop :=
  v &&& 7 = 0 ∧
  (v ≤ 0x047F ∨ (0x0500 ≤ v ∧ v ≤ 0x050F) ∨ 0xF400 ≤ v) ∧
  (active = 0x28 ∨ active = 0x70 ∨ active = 0x90) ∧
  (v &&& 8 ≠ 0 → phase q v) ∧
  (active = 0x28 → 0x8000 ≤ v → phase q v)

/-- An unrestricted lift reset preserves the arithmetic invariant. Neither its
pixel height nor whether the preceding movement entered a tile row is needed. -/
theorem reset_safe (q : UInt16) :
    safe q 0 0x90 := by
  simp only [safe, phase] at *
  bv_decide

/-- Spring animation may move whole pixels arbitrarily; those moves leave q alone. -/
theorem spring_safe (q : UInt16)
    (speed : UInt16) (hs : speed = 0xF400 ∨ speed = 0xF900) :
    safe q speed 0x70 := by
  simp only [safe, phase] at *
  bv_decide

theorem jump_safe : safe 0 0xFB00 0x28 := by
  unfold safe phase
  decide

/-- Actual gravity choices outside swimming and GameEngineSubroutine $0B. -/
def choice (v : UInt16) (active g : UInt8) : Prop :=
  (v < 0x8000 ∧ g = 0x90) ∨ (0x8000 ≤ v ∧ (g = active ∨ g = 0x90))

theorem gravity_safe (q v : UInt16) (active g : UInt8)
    (h : safe q v active) (hg : choice v active g) :
    safe (q + v) (Smb.Vertical.gravity g v) g := by
  simp only [safe, phase, choice, Smb.Vertical.gravity] at *
  bv_decide

/-- Stronger than required: any listed speed overwrite after movement, irrespective
of sign. High speed byte replacement preserves the low five velocity bits. -/
theorem bounce_safe (q v : UInt16) (active g speed : UInt8)
    (h : safe q v active) (hg : choice v active g)
    (hs : speed = 0xFC ∨ speed = 0xFD ∨ speed = 1 ∨ speed = 0 ∨ speed = 0xFE) :
    safe (q + v) ((speed.toUInt16 <<< 8) ||| (Smb.Vertical.gravity g v &&& 0xFF)) g := by
  simp only [safe, phase, choice, Smb.Vertical.gravity] at *
  bv_decide

/-- No 6-pixel movement: full subpixel byte q, widened to avoid sum overflow. -/
theorem no_six_pixel_step (q v : UInt16) (active : UInt8)
    (h : safe q v active) (hq : q ≤ 0xFF) (hv : v < 0x8000) :
    q.toUInt32 + v.toUInt32 < 0x600 := by
  simp only [safe, phase] at *
  bv_decide

/-- Independently of all high-coordinate wrapping, ordinary downward movement
cannot enter a metatile row at offset 5 or later. -/
theorem no_floor_skip (pos : UInt32) (v : UInt16) (active : UInt8)
    (h : safe ((pos &&& 0xFF).toUInt16) v active) (hv : v < 0x8000)
    (hr : Smb.Routine.entersRow pos v = true) :
    Smb.Routine.posY (Smb.Routine.nextPos pos v) &&& 0xF < 5 := by
  simp only [safe, phase, Smb.Routine.entersRow, Smb.Routine.posY,
    Smb.Routine.nextPos, Smb.Routine.sext16, bne] at *
  bv_decide


/-- The residue range itself supplies ImposeGravity's signed-speed premise. -/
theorem safe_speed_bound (q v : UInt16) (active : UInt8) (h : safe q v active) :
    (v >>> 8).toUInt8 + 0x40 < 0x80 := by
  simp only [safe, phase] at h
  bv_decide

/-- Reuse the actual ROM movement summary; no instruction re-execution.
    Raw active gravity is sampled before JumpSwimSub's gravity selection. -/
theorem jump_summary_safe (ram : UInt16 → UInt8) (t : Plain)
    (hs : JumpSwimSummary ram t)
    (hmode : ram 0x0E ≠ 0x0B) (hfall : ram 0x70A = 0x90)
    (h : safe (ram 0x416).toUInt16 (yvel16 ram 0) (ram 0x709)) :
    safe (t.ram 0x416).toUInt16 (yvel16 t.ram 0) (t.ram 0x709) := by
  obtain ⟨hpc, hbad, hg, hv, hpos, hx⟩ := hs
  have hchoice : choice (yvel16 ram 0) (ram 0x709) (jssForce ram) := by
    sym_exec [choice, jssForce, yvel16, ySpeedIdx, yForceIdx]
    bv_decide
  have hnext := gravity_safe (ram 0x416).toUInt16 (yvel16 ram 0) (ram 0x709)
    (jssForce ram) h hchoice
  have hq : (t.ram 0x416).toUInt16 &&& 0xF =
      ((ram 0x416).toUInt16 + yvel16 ram 0) &&& 0xF := by
    sym_exec [ypos24, yvel16, sext16, dummyIdx, yForceIdx, ySpeedIdx, yPosIdx, yHighIdx] at hpos ⊢
    bv_decide
  rw [hg, hv]
  change safe (t.ram 0x416).toUInt16
    (Smb.Vertical.gravity (jssForce ram) (yvel16 ram 0)) (jssForce ram)
  simp only [safe, phase] at hnext ⊢
  rw [hq]
  exact hnext

/-- Smaller land-gravity regimes need no divisibility/phase invariant. -/
def lowSafe (v : UInt16) : Prop := v ≤ 0x047F ∨ 0xF400 ≤ v

theorem low_gravity_safe (v : UInt16) (g : UInt8) (h : lowSafe v) (hg : g ≤ 0x80) :
    lowSafe (gravityVel 0 g 0 4 v) := by
  simp only [lowSafe, gravityVel] at *
  bv_decide

/-- Mode0B's forced28 is inside the bound, so no mode exclusion is needed. -/
theorem jssForce_le_80 (ram : UInt16 → UInt8)
    (ha : ram 0x709 ≤ 0x80) (hf : ram 0x70A ≤ 0x80) : jssForce ram ≤ 0x80 := by
  simp only [jssForce]
  bv_decide

/-- Actual output velocity and active-gravity byte; fall-byte framing is separate. -/
theorem jump_summary_low (ram : UInt16 → UInt8) (t : Plain)
    (hs : JumpSwimSummary ram t) (hv : lowSafe (yvel16 ram 0))
    (ha : ram 0x709 ≤ 0x80) (hf : ram 0x70A ≤ 0x80) :
    lowSafe (yvel16 t.ram 0) ∧ t.ram 0x709 ≤ 0x80 := by
  obtain ⟨hpc, hbad, hg, hvel, hpos, hx⟩ := hs
  have hbound := jssForce_le_80 ram ha hf
  constructor
  · rw [hvel]
    exact low_gravity_safe _ _ hv hbound
  · rw [hg]
    exact hbound

theorem low_speed_bound (v : UInt16) (h : lowSafe v) :
    (v >>> 8).toUInt8 + 0x40 < 0x80 := by
  simp only [lowSafe] at h
  bv_decide

/-- No restriction on the subpixel residue or high coordinate bytes. -/
theorem low_floor_window (pos : UInt32) (v : UInt16)
    (h : lowSafe v) (hdown : v < 0x8000) (hrow : entersRow pos v = true) :
    posY (nextPos pos v) &&& 0xF < 5 := by
  have hv : v < 0x0500 := by
    simp only [lowSafe] at h
    bv_decide
  exact floor_window pos v hv hrow

/-- The actual Y byte after this downward movement is in the landing window.
    Current position movement uses old velocity; its own conclusion needs no
    gravity bounds. Bounds are needed to propagate lowSafe to the next move. -/
theorem jump_summary_low_window (ram : UInt16 → UInt8) (t : Plain)
    (hs : JumpSwimSummary ram t) (hv : lowSafe (yvel16 ram 0))
    (hdown : yvel16 ram 0 < 0x8000)
    (hrow : entersRow (ypos24 ram 0) (yvel16 ram 0) = true) :
    t.ram 0xCE &&& 0xF < 5 := by
  obtain ⟨hpc, hbad, hg, hvel, hpos, hx⟩ := hs
  have hw := low_floor_window (ypos24 ram 0) (yvel16 ram 0) hv hdown hrow
  change posY ((ypos24 ram 0 + sext16 (yvel16 ram 0)) &&& 0xFFFFFF) &&& 0xF < 5 at hw
  rw [← hpos] at hw
  sym_exec [posY, ypos24, dummyIdx, yPosIdx, yHighIdx] at hw
  bv_decide

/-- A fresh normal jump of class0/1/2 initializes the low regime regardless of
    previous vertical state. jumpPart_call supplies exactly this jumpRam. -/
theorem jumpRam_low_initial (ram : UInt16 → UInt8)
    (hj : startsJump ram = true) (hs : ram 0x704 = 0) (hx : ram 0x700 < 0x19) :
    let r := jumpRam ram
    r 0x416 = 0 ∧ lowSafe (yvel16 r 0) ∧ r 0x709 ≤ 0x80 ∧ r 0x70A ≤ 0x80 := by
  sym_exec [jumpRam, hj, hs, jumpClass, jumpMForce, fallMForce, initMForce,
    jumpYSpeed, tbl7, lowSafe, yvel16, ySpeedIdx, yForceIdx]
  bv_decide

/-- A fresh class3/4 jump initializes the high-regime jump_safe premises.
    No residue or velocity premise about the previous state is needed. -/
theorem jumpRam_high_initial (ram : UInt16 → UInt8)
    (hj : startsJump ram = true) (hs : ram 0x704 = 0) (hx : 0x19 ≤ ram 0x700) :
    let r := jumpRam ram
    r 0x416 = 0 ∧ yvel16 r 0 = 0xFB00 ∧ r 0x709 = 0x28 ∧ r 0x70A = 0x90 := by
  sym_exec [jumpRam, hj, hs, jumpClass, jumpMForce, fallMForce, initMForce,
    jumpYSpeed, tbl7, yvel16, ySpeedIdx, yForceIdx]
  bv_decide

end Smb.Routine.VerticalPhase
