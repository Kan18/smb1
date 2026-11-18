import Smb.Data.ProofRom
import Smb.Routine.AnimSpeed
import Smb.Routine.ImposeFriction
import Smb.Routine.MovePlayerHorizontally

/-!
# `OnGroundStateSub` (`$B35A`): Mario on the ground, one frame

```
OnGroundStateSub:  jsr GetPlayerAnimSpeed            (animation; RunningSpeed; the skid stop)
                   if left/right held: PlayerFacingDir := left/right buttons
                   jsr ImposeFriction                (always, unlike in the air)
                   jsr MovePlayerHorizontally; Player_X_Scroll := A
```

Through the call theorems of its three callees: the skid stop happens *before* friction, so
after a stop the speed is `ImposeFriction` applied to 0 (with no direction held: 0).
-/
namespace Smb.Routine

/-- `$B35A`–`$B36C`. -/
def onGroundCode : List UInt8 :=
  smbPrg% 0xB35A 19

/-- The new horizontal speed: the skid stop, then friction. -/
def groundSpeed (ram : UInt16 → UInt8) : UInt8 :=
  let r := animRam ram
  frictionSpeed (frictionDir (ram 0x0C) (r 0x490) (r 0x57)) (r 0x57) (r 0x705) (r 0x702) (r 0x701)
    (r 0x456) (r 0x450)

def OnGroundSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xB36C ∧ t.bad = false ∧ t.ram 0x57 = groundSpeed ram ∧
  t.ram 0x33 = (bif ram 0x0C == 0 then ram 0x33 else ram 0x0C)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem onGround_reach (stop : UInt16) (hstop : ∀ a : UInt16, (0xB35A ≤ a && a ≤ 0xBF4C) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x335A onGroundCode) (hacode : CodeAt prg 0x358C animSpeedCode)
    (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode) (hI : (p &&& 4 == 0) = false)
    (hjs : ram 0x70E = 0) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xB35A, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ OnGroundSummary ram t := by
  simp only [CodeAt, onGroundCode, UInt16.reduceAdd] at hcode
  have hrts : prg 0x35CB = 0x60 ∧ prg 0x3623 = 0x60 ∧ prg 0x3F4C = 0x60 := by
    refine ⟨?_, ?_, ?_⟩
    · have h := hacode; simp only [CodeAt, animSpeedCode, UInt16.reduceAdd] at h; simp [h]
    · have h := hfcode; simp only [CodeAt, imposeFrictionCode, UInt16.reduceAdd] at h; simp [h]
    · have h := hhcode; simp only [CodeAt, movePlayerHorizontallyCode, moveObjectHorizontallyCode,
        List.cons_append, List.nil_append, UInt16.reduceAdd] at h; simp [h]
  obtain ⟨hr1, hr2, hr3⟩ := hrts
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xB35A, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hr1, hr2, hr3, hI, animRam, frictionRam, mphRam] until 45932
    calls [animSpeed_call, imposeFriction_call, movePlayerHorizontally_call]
  all_goals
    intros
    clear hcode hr1 hr2 hr3
    subst hrun
    reach_finish_all [OnGroundSummary, groundSpeed, animRam, skidStops, frictionRam, mphRam, mphPos, mphLo,
      mphHi, mphCarry, pos24, sext, pageIdx, posIdx, forceIdx, speedIdx, frictionSpeed, frictionForce,
      frictionAbs, frictionClamped, frictionRaw, frictionDir]

end Smb.Routine
