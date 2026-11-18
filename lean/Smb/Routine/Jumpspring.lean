import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# What a jumpspring does to Mario (`JumpspringHandler`, `$B8BD`–`$B901`)

```
            leave if TimerControl ≠ 0 or JumpspringAnimCtrl = 0
            Y := JumpspringAnimCtrl − 1
            Y & 2 = 0 → Player_Y_Position += 2      else −= 2
PosJSpr:    the spring's own position from Jumpspring_Y_PosData
            Y ≥ 1 and A newly pressed → JumpspringForce := $F4
BounceJS:   Y = 3 → Player_Y_Speed := JumpspringForce; JumpspringAnimCtrl := 0
```

Landing on the spring (`LandPlyr`: speed and force 0, position aligned to the row) sets the
force `$F9`, the gravity `$70` and the animation control 1; the timer advances the control
every 4 frames. Here, per frame: the position moves by exactly ±2 pixels (without carrying
into `Player_Y_HighPos`), the speed byte becomes the spring force on the bounce frame, and
the force and sub-pixel are untouched. So the bounce leaves from an even row offset with the
landing's sub-pixel. `Smb.Vertical` allows every row offset for a spring launch.
-/
namespace Smb.Routine

/-- `$B8B6`–`$B901`: `Jumpspring_Y_PosData`, then `JumpspringHandler` up to `DrawJSpr`. -/
def jumpspringCode : List UInt8 :=
  smbPrg% 0xB8B6 76

/-- The spring is animating this frame. -/
def springActive (ram : UInt16 → UInt8) : Bool := ram 0x747 == 0 && ram 0x70E != 0

/-- `JumpspringForce` after this frame's A check. -/
def springForce (ram : UInt16 → UInt8) : UInt8 :=
  bif springActive ram && ram 0x70E - 1 != 0 && ram 0x0A &&& 0x80 != 0 && ram 0x0A &&& 0x80 &&& ram 0x0D == 0
  then 0xF4 else ram 0x6DB

def SpringSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xB902 ∧ t.bad = false ∧
  t.ram 0xCE = (bif !springActive ram then ram 0xCE
    else bif (ram 0x70E - 1) &&& 2 == 0 then ram 0xCE + 2 else ram 0xCE - 2) ∧
  t.ram 0x9F = (bif springActive ram && ram 0x70E == 4 then springForce ram else ram 0x9F) ∧
  t.ram 0x433 = ram 0x433 ∧ t.ram 0x416 = ram 0x416 ∧ t.ram 0xB5 = ram 0xB5

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem jumpspring_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xB8BD ≤ a && a ≤ 0xB902) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x38B6 jumpspringCode) (hI : (p &&& 4 == 0) = false) (hx : x < 6) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB8BD, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ SpringSummary ram t := by
  simp only [CodeAt, jumpspringCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB8BD, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI, hx] until 47362
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [SpringSummary, springActive, springForce]

end Smb.Routine
