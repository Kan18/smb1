import Smb.Movement.Model
import Smb.Routine.Launch

/-!
# The movement model against the ROM's summaries

`Smb.Movement.preFall` and `fallS` are what `PlayerMovementSubs` does, on the cells the model has: each theorem here reads one cell of the generated summary `msK_ram` and finds the model's value. The conditions are what the model leaves out: normal control (`$0E` = 8), not swimming, not changing size, no jumpspring, not in water, no wall touched last frame, the summaries' speed range, and the two input cells `PlayerCtrlRoutine` sets from `$6FC`.
-/
namespace Smb.Routine.ModelBridge
open Smb.Routine.PlayerFramePosition Smb.Routine.HorizontalLimit Smb.Routine.HorizontalLimitNes Smb.Routine.Launch

/-- The cells the model describes. -/
def cellsOf (ram : UInt16 → UInt8) : Smb.Movement.S :=
  { v := ram 0x57, f := ram 0x705, abs := ram 0x700, face := ram 0x33, move := ram 0x45, st := ram 0x1D,
    t783 := ram 0x783, r703 := ram 0x703, y := ram 0xCE, ysub := ram 0x416, vy := ram 0x9F, vf := ram 0x433,
    g := ram 0x709, gfall := ram 0x70A, y0 := ram 0x708, rise := ram 0x706, prevA := ram 0x0D &&& 0x80 }

/-- The pad as the model reads it. -/
def inOfRam (ram : UInt16 → UInt8) : Smb.Movement.In :=
  ⟨ram 0x6FC &&& 1 != 0, ram 0x6FC &&& 2 != 0, ram 0x6FC &&& 0x40 != 0, ram 0x6FC &&& 0x80 != 0,
   ram 0x6FC &&& 0x38 != 0, ram 0x6FC &&& 4 != 0, ram 0x783 != 0⟩

/-- What `PlayerCtrlRoutine` does with `$6FC` before `PlayerMovementSubs`. -/
def InputCells (ram : UInt16 → UInt8) : Prop :=
  ram 0x0A = ram 0x6FC &&& 0xC0 ∧
  ram 0x0C = (bif ram 0x6FC &&& 4 != 0 && ram 0x1D == 0 then 0 else ram 0x6FC &&& 3)

/-! ## Flattening

The model is written with `if` and `match` on structures, and `bv_decide` wants bytes and `bif`. -/

theorem ite_bif {α : Type} (c : Prop) [Decidable c] (a b : α) : (if c then a else b) = bif decide c then a else b := by
  by_cases h : c <;> simp [h]

theorem tbl5_jc (x a b c d e : UInt8) :
    Smb.Movement.tbl5 a b c d e (Smb.Movement.jumpClass x) =
      bif decide (x < 9) then a else bif decide (x < 0x10) then b else bif decide (x < 0x19) then c else bif decide (x < 0x1C) then d else e := by
  by_cases h1 : x < 9 <;> by_cases h2 : x < 0x10 <;> by_cases h3 : x < 0x19 <;> by_cases h4 : x < 0x1C <;>
    simp [Smb.Movement.jumpClass, Smb.Movement.tbl5, h1, h2, h3, h4]

theorem tbl3_sc (r : Bool) (a b c : UInt8) :
    Smb.Movement.tbl3 a b c (bif r then 0 else 1) = bif r then a else b := by
  cases r <;> rfl

theorem tbl3_fc (r q : Bool) (a b c : UInt8) :
    Smb.Movement.tbl3 a b c (bif r then 0 else bif q then 2 else 1) = bif r then a else bif q then c else b := by
  cases r <;> cases q <;> rfl

macro "model_tac" : tactic => `(tactic| (
  simp only [cellsOf, inOfRam, InputCells, Smb.Movement.moved, Smb.Movement.fallS, Smb.Movement.jumpStart, Smb.Movement.speedClass,
    Smb.Movement.frictionClass, Smb.Movement.running, Smb.Movement.timerSet, Smb.Movement.routine, Smb.Movement.skid,
    Smb.Movement.friction, Smb.Movement.rightV, Smb.Movement.leftV, Smb.Movement.absOf,
    tbl5_jc, tbl3_sc, tbl3_fc,
    apply_ite Smb.Movement.S.v, apply_ite Smb.Movement.S.f, apply_ite Smb.Movement.S.abs, apply_ite Smb.Movement.S.face,
    apply_ite Smb.Movement.S.move, apply_ite Smb.Movement.S.st, apply_ite Smb.Movement.S.t783, apply_ite Smb.Movement.S.r703,
    apply_ite Smb.Movement.S.y, apply_ite Smb.Movement.S.ysub, apply_ite Smb.Movement.S.vy, apply_ite Smb.Movement.S.vf,
    apply_ite Smb.Movement.S.g, apply_ite Smb.Movement.S.gfall, apply_ite Smb.Movement.S.y0, apply_ite Smb.Movement.S.rise,
    apply_ite Smb.Movement.S.prevA, ite_bif, decide_eq_true_eq, Bool.decide_eq_true] at *
  try simp only [tbl3_sc, tbl3_fc] at *
  (sym_exec [gravityVel, startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam,
    gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass,
    xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx,
    pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx,
    ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
   fun_congr
   bv_decide (config := { enums := false }))))

/-- `PlayerMovementSubs`, by the model. -/
abbrev modelMove (ram : UInt16 → UInt8) : Smb.Movement.S := Smb.Movement.fallS (Smb.Movement.moved (inOfRam ram) (cellsOf ram))

set_option maxHeartbeats 8000000 in
theorem ms0_v (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x57 = (modelMove ram).v := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_f (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x705 = (modelMove ram).f := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_abs (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x700 = (modelMove ram).abs := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_face (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x33 = (modelMove ram).face := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_move (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x45 = (modelMove ram).move := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_st (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x1D = (modelMove ram).st := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_t783 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x783 = (modelMove ram).t783 := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_r703 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x703 = (modelMove ram).r703 := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_y (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0xCE = (modelMove ram).y := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_ysub (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x416 = (modelMove ram).ysub := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_vy (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x9F = (modelMove ram).vy := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_vf (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x433 = (modelMove ram).vf := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_g (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x709 = (modelMove ram).g := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_gfall (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x70A = (modelMove ram).gfall := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_y0 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x708 = (modelMove ram).y0 := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms0_rise (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms0_ram sp ram 0x706 = (modelMove ram).rise := by
  simp only [modelMove, ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_v (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x57 = (modelMove ram).v := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_f (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x705 = (modelMove ram).f := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_abs (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x700 = (modelMove ram).abs := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_face (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x33 = (modelMove ram).face := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_move (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x45 = (modelMove ram).move := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_st (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x1D = (modelMove ram).st := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_t783 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x783 = (modelMove ram).t783 := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_r703 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x703 = (modelMove ram).r703 := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_y (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0xCE = (modelMove ram).y := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_ysub (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x416 = (modelMove ram).ysub := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_vy (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x9F = (modelMove ram).vy := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_vf (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x433 = (modelMove ram).vf := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_g (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x709 = (modelMove ram).g := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_gfall (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x70A = (modelMove ram).gfall := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_y0 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x708 = (modelMove ram).y0 := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms1_rise (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms1_ram sp ram 0x706 = (modelMove ram).rise := by
  simp only [modelMove, ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_v (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x57 = (modelMove ram).v := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_f (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x705 = (modelMove ram).f := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_abs (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x700 = (modelMove ram).abs := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_face (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x33 = (modelMove ram).face := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_move (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x45 = (modelMove ram).move := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_st (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x1D = (modelMove ram).st := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_t783 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x783 = (modelMove ram).t783 := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_r703 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x703 = (modelMove ram).r703 := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_y (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0xCE = (modelMove ram).y := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_ysub (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x416 = (modelMove ram).ysub := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_vy (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x9F = (modelMove ram).vy := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_vf (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x433 = (modelMove ram).vf := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_g (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x709 = (modelMove ram).g := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_gfall (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x70A = (modelMove ram).gfall := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_y0 (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x708 = (modelMove ram).y0 := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

set_option maxHeartbeats 8000000 in
theorem ms2_rise (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (he : ram 0x0E = 8) (ha : ram 0x74E ≠ 0) (hc : ram 0x490 = 0xFF) (hi : InputCells ram) :
    ms2_ram sp ram 0x706 = (modelMove ram).rise := by
  simp only [modelMove, ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  model_tac

end Smb.Routine.ModelBridge
