import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# `ImposeFriction` (`$B5CC`): Mario's horizontal acceleration and friction

Entered with `A` = the left/right buttons. With a direction held (and not blocked by
`Player_CollisionBits`), right accelerates (`+`) and left decelerates (`−`); with none held,
the speed decays toward 0. The step is the 8.8 `FrictionAdder` (`High:Low`, set by
`PlayerPhysicsSub`; doubled when turning), and the result is clamped at `MaximumRightSpeed`
/ `MaximumLeftSpeed` by a sign-bit test, like the gravity clamp. `Player_XSpeedAbsolute` gets
the speed's magnitude.

```
     inp := A & CollisionBits
     inp ≠ 0:  right bit → add, else → sub
     inp = 0:  speed = 0 → |speed| := 0;  speed > 0 → sub;  speed < 0 → add
add: force += Low; speed += High + carry; if speed − MaxRight has bit 7 clear: speed := MaxRight
sub: force −= Low; speed −= High + borrow; if speed − MaxLeft has bit 7 set:   speed := MaxLeft
```

This file gives the routine as a call theorem (closed form at its RTS, `$B623`).
-/
namespace Smb.Routine

/-- `$B5CC`–`$B623`, including the final RTS. -/
def imposeFrictionCode : List UInt8 :=
  smbPrg% 0xB5CC 88

/-- 0: no change; 1: add (accelerate right / brake leftward motion); 2: subtract. -/
def frictionDir (lr coll spd : UInt8) : UInt8 :=
  bif lr &&& coll != 0 then (bif lr &&& coll &&& 1 != 0 then 1 else 2)
  else bif spd == 0 then 0 else bif spd < 0x80 then 2 else 1

/-- The speed after the step, before clamping. -/
def frictionRaw (dir spd force lo hi : UInt8) : UInt8 :=
  bif dir == 1 then spd + hi + (bif force.toUInt16 + lo.toUInt16 > 0xFF then 1 else 0)
  else spd - hi - (bif force < lo then 1 else 0)

def frictionClamped (dir spd force lo hi maxR maxL : UInt8) : Bool :=
  let r := frictionRaw dir spd force lo hi
  bif dir == 1 then (r - maxR) &&& 0x80 == 0 else (r - maxL) &&& 0x80 != 0

def frictionSpeed (dir spd force lo hi maxR maxL : UInt8) : UInt8 :=
  bif dir == 0 then spd else
  bif frictionClamped dir spd force lo hi maxR maxL then (bif dir == 1 then maxR else maxL)
  else frictionRaw dir spd force lo hi

def frictionForce (dir force lo : UInt8) : UInt8 :=
  bif dir == 0 then force else bif dir == 1 then force + lo else force - lo

/-- `Player_XSpeedAbsolute` (and `A`): the magnitude of the new speed, except that a clamp at
the right maximum stores `MaxRight` as is. -/
def frictionAbs (dir spd force lo hi maxR maxL : UInt8) : UInt8 :=
  let v := frictionSpeed dir spd force lo hi maxR maxL
  bif dir == 1 && frictionClamped dir spd force lo hi maxR maxL then maxR
  else bif v &&& 0x80 != 0 then 0 - v else v

/-- Cycles to the RTS. Two taken branches cross into page `$B6` (+1 each). -/
def frictionCycles (lr coll spd force lo hi maxR maxL : UInt8) : UInt64 :=
  let dir := frictionDir lr coll spd
  let joy := lr &&& coll != 0
  let r := frictionRaw dir spd force lo hi
  let xs (v : UInt8) : UInt64 := bif v &&& 0x80 == 0 then 5 else 10
  bif dir == 0 then 19 else
  bif dir == 1 then
    (bif joy then 13 else 18) + 28 +
      (bif frictionClamped dir spd force lo hi maxR maxL then 12 else 4 + xs r) + 4
  else
    (bif joy then 14 else 16) + 28 +
      (bif frictionClamped dir spd force lo hi maxR maxL then 9 + xs maxL else 3 + xs r) + 4

/-- RAM on return. (Written so that bytes the path leaves alone read `ram i`: `bv_decide` has
no congruence for `ram`, so `ram i` and `ram 0x57` are unrelated atoms to it even when
`i = 0x57`.) -/
def frictionRam (lr : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let dir := frictionDir lr (ram 0x490) (ram 0x57)
  bif i == 0x705 && dir != 0 then frictionForce dir (ram 0x705) (ram 0x702)
  else bif i == 0x57 && dir != 0 then
    frictionSpeed dir (ram 0x57) (ram 0x705) (ram 0x702) (ram 0x701) (ram 0x456) (ram 0x450)
  else bif i == 0x700 then
    frictionAbs dir (ram 0x57) (ram 0x705) (ram 0x702) (ram 0x701) (ram 0x456) (ram 0x450)
  else ram i

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem imposeFriction_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB5CC ≤ a && a ≤ 0xB623) = true → a ≠ stop)
    (m : Nat) (lr x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x35CC imposeFrictionCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB5CC, lr, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB623,
        frictionAbs (frictionDir lr (ram 0x490) (ram 0x57)) (ram 0x57) (ram 0x705) (ram 0x702) (ram 0x701)
          (ram 0x456) (ram 0x450), x, y, sp, p'⟩,
        frictionRam lr ram, prg,
        cyc + frictionCycles lr (ram 0x490) (ram 0x57) (ram 0x705) (ram 0x702) (ram 0x701) (ram 0x456) (ram 0x450),
        bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, imposeFrictionCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB5CC, lr, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 46627
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [frictionRam, frictionAbs, frictionSpeed, frictionForce, frictionClamped, frictionRaw,
      frictionDir, frictionCycles]

end Smb.Routine
