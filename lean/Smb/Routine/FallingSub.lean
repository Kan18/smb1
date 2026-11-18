import Smb.Data.ProofRom
import Smb.Routine.JumpSwimSub

/-!
# `FallingSub` (`$B36D`): Mario falling (walked off a ledge, or after a landing failed)

```
FallingSub:  VerticalForce := VerticalForceDown; jmp LRAir   (then as in JumpSwimSub)
```

So a fall always uses the falling gravity of the *last jump's* class (`VerticalForceDown` is
only written by a jump start and by the pipe entrance), the position moves by the velocity
from before this frame's gravity, and the horizontal speed changes only with left/right held.
-/
namespace Smb.Routine

/-- `$B36D`–`$B375`: `FallingSub` (just before `JumpSwimSub`). -/
def fallingSubCode : List UInt8 := smbPrg% 0xB36D 9

def FallingSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xC046 ∧ t.bad = false ∧
  t.ram 0x709 = (bif ram 0x0E == 0x0B then 0x28 else ram 0x70A) ∧
  yvel16 t.ram 0 = gravityVel 0 (bif ram 0x0E == 0x0B then 0x28 else ram 0x70A) 0 4 (yvel16 ram 0) ∧
  ypos24 t.ram 0 = (ypos24 ram 0 + sext16 (yvel16 ram 0)) &&& 0xFFFFFF ∧
  t.ram 0x57 = (bif ram 0x0C == 0 then ram 0x57 else
    frictionSpeed (frictionDir (ram 0x0C) (ram 0x490) (ram 0x57)) (ram 0x57) (ram 0x705) (ram 0x702)
      (ram 0x701) (ram 0x456) (ram 0x450))

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem fallingSub_reach (stop : UInt16) (hstop : ∀ a : UInt16, (0xB36D ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode0 : CodeAt prg 0x336D fallingSubCode)
    (hcode : CodeAt prg 0x3376 jumpSwimCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0xB36D, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ FallingSummary ram t := by
  simp only [CodeAt, fallingSubCode, UInt16.reduceAdd] at hcode0
  simp only [CodeAt, jumpSwimCode, UInt16.reduceAdd] at hcode
  -- The callees' RTS bytes, which this routine executes after each call.
  have hfrts : prg 0x3623 = 0x60 := by
    have h := hfcode; simp only [CodeAt, imposeFrictionCode, UInt16.reduceAdd] at h; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hhrts : prg 0x3F4C = 0x60 := by
    have h := hhcode; simp only [CodeAt, movePlayerHorizontallyCode, moveObjectHorizontallyCode,
      List.cons_append, List.nil_append, UInt16.reduceAdd] at h
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0xB36D, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode0, hcode, hfrts, hhrts, hI, frictionRam, mphRam, mpvRam] until 49222
    calls [imposeFriction_call, movePlayerHorizontally_call, movePlayerVertically_call]
  all_goals
    intros
    clear hcode0 hcode hfrts hhrts
    subst hrun
    reach_finish [FallingSummary, gravityRam, mpvRam, mphRam, frictionRam, gravityVel, gravityY,
      gravityA, ypos24, yvel16, sext16, dummyIdx, yForceIdx, ySpeedIdx, yPosIdx, yHighIdx, mphPos, mphLo,
      mphHi, mphCarry, pos24, sext, pageIdx, posIdx, forceIdx, speedIdx, frictionSpeed, frictionForce,
      frictionAbs, frictionClamped, frictionRaw, frictionDir]

end Smb.Routine
