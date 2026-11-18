import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# `ImposeGravity` (`$BFD7`)

The vertical movement routine shared by Mario (`MovePlayerVertically`: `X = 0`, `$00` =
`VerticalForce`, maximum speed 4, `A = 0`), enemies, platforms, fireballs, hammers and coins.

```
ImposeGravity:            ; A: nonzero = also apply the upward part
  pha
  YMF_Dummy,x += Y_MoveForce,x            ; fraction of the position
  $07 := (Y_Speed,x < 0) ? $FF : $00
  Y_Position,x += Y_Speed,x + carry;  Y_HighPos,x += $07 + carry
  Y_MoveForce,x += $00;  Y_Speed,x += carry      ; gravity
  cmp $02 / bmi:  if "speed ≥ max" and force ≥ $80: speed := max, force := 0
  pla / beq: done if A was 0
  $07 := -max
  Y_MoveForce,x -= $01;  Y_Speed,x -= borrow      ; upward amount
  cmp $07 / bpl:  if "speed < -max" and force < $80: speed := -max, force := $FF
```

Read as fixed point: the position is a 16.8 number (high : position : dummy) and the velocity
an 8.8 number (speed : force). `gravityVel` below is the *intended* velocity update, with true
signed comparisons. The routine's comparisons only test the sign bit of `speed - max`.

**What the proof attempt found.** Without bounds, `bv_decide` refutes the velocity claim: when
`speed - max` (or `speed + max` in the upward part) overflows, the sign test disagrees with the
signed comparison. E.g. speed `$80` (−128, rising fast) with maximum 4 is treated as "at least
the maximum" and clamped to +4 (`ImposeGravityOverflow.lean`). With the speed in [−64, 63] and
the maximum below 64 the summary holds. Every call in the TAS replay satisfies these bounds,
but whether any input sequence can violate them is a separate, open question: the summary
says nothing about such calls.

The proof also settles whether the maximum speed is a hard limit (`gravityVel_withinMax`,
`gravityVel_mario_speed5` below): it is when gravity is at most `$80`, but Mario's falling
gravity can be `$90`, which allows speed 5 for one frame. (The TAS itself does this: an
instrumented replay finds 40 such calls, the first on model frame 336 with velocity `$0470`
→ `$0500`. So it is a gap in the naive "speed ≤ 4" rule, not a new trick.)
-/
-- The linter walks the large symbolic-execution proofs for nothing.
set_option linter.unusedVariables false

namespace Smb.Routine

/-- `$BFD7`–`$C046`, including the final RTS. -/
def imposeGravityCode : List UInt8 :=
  smbPrg% 0xBFD7 112

def imposeGravityRun (s : Plain) : Plain := ((CPU.runTo (σ := Plain) 0xC046 60).run s).2

def dummyIdx (x : UInt8) : UInt16 := (0x416 + x.toUInt16) &&& 0x7FF
def yForceIdx (x : UInt8) : UInt16 := (0x433 + x.toUInt16) &&& 0x7FF
def ySpeedIdx (x : UInt8) : UInt16 := (0x9F + x).toUInt16 &&& 0x7FF
def yPosIdx (x : UInt8) : UInt16 := (0xCE + x).toUInt16 &&& 0x7FF
def yHighIdx (x : UInt8) : UInt16 := (0xB5 + x).toUInt16 &&& 0x7FF

/-- Vertical position, 16.8 fixed point. -/
def ypos24 (ram : UInt16 → UInt8) (x : UInt8) : UInt32 :=
  ((ram (yHighIdx x)).toUInt32 <<< 16) ||| ((ram (yPosIdx x)).toUInt32 <<< 8) ||| (ram (dummyIdx x)).toUInt32

/-- Vertical velocity, 8.8 fixed point. -/
def yvel16 (ram : UInt16 → UInt8) (x : UInt8) : UInt16 :=
  ((ram (ySpeedIdx x)).toUInt16 <<< 8) ||| (ram (yForceIdx x)).toUInt16

def sext16 (v : UInt16) : UInt32 := bif 0x8000 ≤ v then v.toUInt32 ||| 0xFFFF0000 else v.toUInt32

/-- The intended velocity update: add gravity `down`, clamp at `max`; if `aIn ≠ 0`, subtract
`up` and clamp at `-max`. Comparisons are true signed comparisons of the speed byte. -/
def gravityVel (aIn down up mx : UInt8) (v : UInt16) : UInt16 :=
  let v1 := v + down.toUInt16
  let v1 := bif mx.toBitVec.sle (v1 >>> 8).toUInt8.toBitVec && (0x80 ≤ v1.toUInt8 : Bool)
    then mx.toUInt16 <<< 8 else v1
  bif aIn == 0 then v1 else
  let v2 := v1 - up.toUInt16
  let neg := 0 - mx
  bif (v2 >>> 8).toUInt8.toBitVec.slt neg.toBitVec && (v2.toUInt8 < 0x80 : Bool)
    then (neg.toUInt16 <<< 8) ||| 0xFF else v2

/-- Cycles from entry to the RTS. The base path (`A = 0`, speed not negative, no clamp
check) takes 86 cycles; a negative speed adds one (the `dey`); each clamp check adds 8, and
an actual clamp 13 more; the upward part adds 41 plus its own check. The tests are the same
as in `gravityVel`. -/
def gravityCycles (aIn down up mx : UInt8) (v : UInt16) : UInt64 :=
  let v1 := v + down.toUInt16
  let check1 : UInt64 := bif mx.toBitVec.sle (v1 >>> 8).toUInt8.toBitVec then
    (bif (0x80 ≤ v1.toUInt8 : Bool) then 21 else 8) else 0
  let base : UInt64 := 86 + (bif 0x8000 ≤ v then 1 else 0) + check1
  bif aIn == 0 then base else
  let v1 := gravityVel 0 down up mx v
  let v2 := v1 - up.toUInt16
  let neg := 0 - mx
  let check2 : UInt64 := bif (v2 >>> 8).toUInt8.toBitVec.slt neg.toBitVec then
    (bif (v2.toUInt8 < 0x80 : Bool) then 21 else 8) else 0
  base + 41 + check2

/-- The `A` returned: 0 after `A = 0`; otherwise the last byte loaded, which is the new
speed when the upward part's clamp check is skipped and the new fraction when it runs. -/
def gravityA (aIn down up mx : UInt8) (v : UInt16) : UInt8 :=
  bif aIn == 0 then 0 else
  let v2 := gravityVel 0 down up mx v - up.toUInt16
  bif (v2 >>> 8).toUInt8.toBitVec.slt (0 - mx).toBitVec then (gravityVel aIn down up mx v).toUInt8
  else (v2 >>> 8).toUInt8

/-- Flags are not summarized; the direct callers set them again before testing them
(tail calls such as `jmp ImposeGravity` were only spot-checked). -/
def GravitySummary (aIn x sp : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64) (s : Plain) : Prop :=
  s.bad = false ∧ s.regs.pc = 0xC046 ∧ s.regs.x = x ∧ s.regs.s = sp ∧
  s.regs.a = gravityA aIn (ram 0) (ram 1) (ram 2) (yvel16 ram x) ∧
  s.regs.y = (bif aIn == 0 then (bif 0x80 ≤ ram (ySpeedIdx x) then 0xFF else 0) else 0 - ram 2) ∧
  s.cyc = cyc + gravityCycles aIn (ram 0) (ram 1) (ram 2) (yvel16 ram x) ∧
  ypos24 s.ram x = (ypos24 ram x + sext16 (yvel16 ram x)) &&& 0xFFFFFF ∧
  yvel16 s.ram x = gravityVel aIn (ram 0) (ram 1) (ram 2) (yvel16 ram x) ∧
  (∀ i : UInt16, i ≠ 7 → i ≠ dummyIdx x → i ≠ yForceIdx x → i ≠ ySpeedIdx x → i ≠ yPosIdx x →
    i ≠ yHighIdx x → i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF → s.ram i = ram i)

set_option maxHeartbeats 20000000 in
theorem imposeGravity
    (aIn x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3FD7 imposeGravityCode) (hp : p &&& 4 ≠ 0) (hx : x < 0x32)
    (hspd : ram (ySpeedIdx x) + 0x40 < 0x80) (hmax : ram 2 < 0x40) :
    GravitySummary aIn x sp ram cyc (imposeGravityRun ⟨⟨0xBFD7, aIn, x, y, sp, p⟩, ram, prg, cyc, false⟩) := by
  simp only [CodeAt, imposeGravityCode, UInt16.reduceAdd] at hcode
  simp only [ySpeedIdx] at hspd
  generalize hrun : imposeGravityRun ⟨⟨0xBFD7, aIn, x, y, sp, p⟩, ram, prg, cyc, false⟩ = f
  unfold imposeGravityRun at hrun
  have hI : (p &&& 4 == 0) = false := beq_false_of_ne hp
  sym_run hrun [hcode, hI]
  all_goals
    intros
    clear hcode hI
    simp only [GravitySummary, gravityA, gravityCycles, ypos24, yvel16, sext16, gravityVel, dummyIdx,
      yForceIdx, ySpeedIdx, yPosIdx, yHighIdx, bne] at *
    -- One `bv_decide` for all register/position/cycle claims, one for the RAM frame.
    simp only [← and_assoc]
    refine ⟨?_, fun i h0 h1 h2 h3 h4 h5 h6 => ?_⟩ <;> bv_decide

/-! ### Is the maximum speed a bound?

The clamp only fires when the fraction is at least `$80`, so a carry from the fraction can
push the speed above the maximum for one call. Whether that happens depends on the gravity. -/

/-- At or below the maximum: below it, or at it with fraction below `$80` (after a call with
`A = 0`, a state at the maximum with a larger fraction would already have been clamped). -/
def withinMax (mx : UInt8) (v : UInt16) : Bool :=
  (v >>> 8).toUInt8.toBitVec.slt mx.toBitVec || ((v >>> 8).toUInt8 == mx && (v.toUInt8 < 0x80 : Bool))

/-- With gravity at most `$80`, the maximum is a true bound for objects moved with `A = 0`. -/
theorem gravityVel_withinMax (down mx : UInt8) (v : UInt16) (hd : down ≤ 0x80) (hm : mx < 0x40)
    (hlow : (v >>> 8).toUInt8 + 0x40 < 0x80) (h : withinMax mx v = true) :
    withinMax mx (gravityVel 0 down 0 mx v) = true := by
  simp only [withinMax, gravityVel] at *
  bv_decide

/-- Mario falls with gravity `VerticalForce` taken from `FallMForceData`, which contains `$90`,
and maximum speed 4. From speed 4 with fraction `$7F`, one call gives speed 5. (The next call
clamps back to 4.) -/
theorem gravityVel_mario_speed5 : gravityVel 0 0x90 0 4 0x047F = 0x050F := by decide

end Smb.Routine
