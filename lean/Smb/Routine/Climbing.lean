import Smb.Data.ProofRom
import Smb.Routine.ImposeGravity

/-!
# `ClimbingSub` (`$B3CF`): Mario on a vine, one frame

```
YMF_Dummy += Y_MoveForce;  (Y_HighPos : Y_Position) += sign_extend(Y_Speed) + carry
if left/right held and ClimbSideTimer = 0: step sideways by ClimbAdder (timer := $18),
   PlayerFacingDir := buttons ^ 3
```

`Y_MoveForce`/`Y_Speed` were set by `PlayerPhysicsSub` (`Climb_Y_*Data`): `$20`/`−1` climbing
up, `$FF`/`1` climbing down, 0 still. Unlike gravity, the force goes straight into the
sub-pixel and the speed byte into the pixel (the code adds `A`, still holding the speed from
its sign test, not just the sign adder): climbing down moves 1 px plus the carry of `$FF`,
i.e. usually 2 px per frame. Climbing down also adds `$FF` to the sub-pixel each frame, the one land move that
gives the sub-pixel odd values, which is what makes the 1-2 vine floor clip possible
(`analysis/vertical_reach.py`, `FloorReach.lean`).
-/
namespace Smb.Routine

/-- `$B3C7`–`$B423`: `ClimbAdderLow/High` and `ClimbingSub`. -/
def climbingCode : List UInt8 :=
  smbPrg% 0xB3C7 93

/-- The 16.8 vertical position after one climbing frame: the force goes into the sub-pixel,
and the speed byte (still in `A` from the sign test) into the pixel, sign-extended. -/
def climbPos (ram : UInt16 → UInt8) : UInt32 :=
  let spd : UInt32 := bif 0x80 ≤ ram 0x9F then (ram 0x9F).toUInt32 ||| 0xFFFF00 else (ram 0x9F).toUInt32
  (ypos24 ram 0 + (ram 0x433).toUInt32 + (spd <<< 8)) &&& 0xFFFFFF

def ClimbSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  (t.regs.pc = 0xB41F ∨ t.regs.pc = 0xB423) ∧ t.bad = false ∧ ypos24 t.ram 0 = climbPos ram

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem climbing_reach (stop : UInt16) (hstop : ∀ a : UInt16, (0xB3CF ≤ a && a ≤ 0xB423) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x33C7 climbingCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 50)).run ⟨⟨0xB3CF, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ ClimbSummary ram t := by
  simp only [CodeAt, climbingCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 50)).run ⟨⟨0xB3CF, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until [46111, 46115]
  all_goals
    intros
    subst hrun
    reach_finish [ClimbSummary, climbPos, ypos24, dummyIdx, yPosIdx, yHighIdx]

end Smb.Routine
