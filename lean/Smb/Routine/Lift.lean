import Smb.Data.ProofRom
import Smb.Routine.Firebar

/-!
# Standing on a vertical lift (`PositionPlayerOnVPlat`, `$DC21`)

```
PositionPlayerOnVPlat:  leave if GameEngineSubroutine = $0B or the lift is not on screen
                        Player_Y_Position/HighPos := lift's Y − $20 (16-bit)
                        Player_Y_Speed := 0; Player_Y_MoveForce := 0
```

The sub-pixel is left alone. Mario's pixel follows the lift's, which is not tied to the
metatile rows, so he stands at any row offset with the sub-pixel he had: the any-offset
walk-off and jump starts of `Smb.Vertical` (speed and force 0 when he steps off).
-/
namespace Smb.Routine

/-- `$DC21`–`$DC3F`. -/
def liftCode : List UInt8 :=
  smbPrg% 0xDC21 31

/-- The lift (enemy slot `x`) carries Mario this frame. -/
def liftOn (x : UInt8) (ram : UInt16 → UInt8) : Bool := ram 0x0E != 0x0B && ram (zpx 0xB6 x) == 1

def LiftSummary (x : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xDC40 ∧ t.bad = false ∧
  t.ram 0xCE = (bif liftOn x ram then ram (zpx 0xCF x) - 0x20 else ram 0xCE) ∧
  t.ram 0xB5 = (bif liftOn x ram then (bif ram (zpx 0xCF x) < 0x20 then 0 else 1) else ram 0xB5) ∧
  t.ram 0x9F = (bif liftOn x ram then 0 else ram 0x9F) ∧
  t.ram 0x433 = (bif liftOn x ram then 0 else ram 0x433) ∧
  t.ram 0x416 = ram 0x416

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem lift_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDC21 ≤ a && a ≤ 0xDC40) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x5C21 liftCode) (hI : (p &&& 4 == 0) = false) (hx : x < 6) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xDC21, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ LiftSummary x ram t := by
  simp only [CodeAt, liftCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xDC21, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI, hx] until 56384
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [LiftSummary, liftOn, zpx]

end Smb.Routine
