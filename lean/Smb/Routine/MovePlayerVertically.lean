import Smb.Data.ProofRom
import Smb.Routine.ImposeGravityCall

/-!
# `MovePlayerVertically` (`$BF4D`), through a call summary

```
MovePlayerVertically:  ldx #0; if TimerControl = 0 and JumpspringAnimCtrl ≠ 0: return
                       $00 := VerticalForce; A := 4; jmp ImposeGravitySprObj
ImposeGravitySprObj:   $02 := A; A := 0; jmp ImposeGravity
```

The first use of `sym_run … calls`: at `$BFD7` the call summary `imposeGravity_call` replaces
the twelve paths of `ImposeGravity` by one closed-form state. Mario's whole vertical move per
frame is gravity `VerticalForce`, maximum speed 4, and no upward part.
-/
namespace Smb.Routine

/-- `$BF4D`–`$BFB3`: `MovePlayerVertically` through `ImposeGravitySprObj`. -/
def movePlayerVerticallyCode : List UInt8 :=
  smbPrg% 0xBF4D 103

/-- RAM when `ImposeGravity` starts: gravity in `$00`, maximum 4 in `$02`. -/
def mpvRam (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == 2 then 4 else bif i == 0 then ram 0x709 else ram i

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem movePlayerVertically_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xBF4D ≤ a && a ≤ 0xC046) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hI : (p &&& 4 == 0) = false) (hjs : ram 0x747 ≠ 0 ∨ ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xBF4D, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xC046, gravityA 0 (ram 0x709) (ram 1) 4 (yvel16 ram 0), 0,
        gravityY 0 4 (ram 0x9F), sp, p'⟩, gravityRam 0 0 sp (mpvRam ram), prg,
        cyc + (bif ram 0x747 != 0 then 29 else 34) + gravityCycles 0 (ram 0x709) (ram 1) 4 (yvel16 ram 0),
        bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, movePlayerVerticallyCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xBF4D, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI, ySpeedIdx] until 49222 calls [imposeGravity_call]
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [gravityRam, mpvRam, gravityY, gravityA, gravityCycles, gravityVel, ypos24, yvel16, sext16, dummyIdx, yForceIdx, ySpeedIdx, yPosIdx, yHighIdx]

end Smb.Routine
