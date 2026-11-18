import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# `GetPlayerAnimSpeed` (`$B58F`): animation speed, running flag, and the skid stop

Despite its name this routine also changes Mario's motion. On the ground (and swimming):

```
y := |speed| ≥ $1C ? 0 : |speed| ≥ $0E ? 1 : 2;  PlayerAnimTimerSet := [2, 4, 7][y]
if |speed| ≥ $1C:                       RunningSpeed := |speed| (nonzero)
else if buttons & $7F ≠ 0:
  if buttons & 3 = MovingDir:          RunningSpeed := 0
  else if |speed| < $0B:              MovingDir := FacingDir; X_Speed := 0; X_MoveForce := 0
```

The skid stop compares `buttons & 3` with the moving direction whenever *any* button other
than A is pressed. So besides pressing the opposite direction (the intended skid) and L+R,
holding only Up, Down, Select or B (no direction; Start pauses the game) while moving slower than `$0B`
also stops Mario dead in one frame (`animSpeed_stop`).
-/
namespace Smb.Routine

/-- `$B58C`–`$B5CB`: `PlayerAnimTmrData` and `GetPlayerAnimSpeed` with its RTS. -/
def animSpeedCode : List UInt8 :=
  smbPrg% 0xB58C 64

/-- Does the routine stop Mario (the skid stop)? -/
def skidStops (ram : UInt16 → UInt8) : Bool :=
  ram 0x700 < 0x1C && ram 0x6FC &&& 0x7F != 0 && ram 0x6FC &&& 0x03 != ram 0x45 && ram 0x700 < 0x0B

def AnimSpeedSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xB5CB ∧ t.bad = false ∧
  t.ram 0x70C = (bif 0x1C ≤ ram 0x700 then 2 else bif 0x0E ≤ ram 0x700 then 4 else 7) ∧
  t.ram 0x703 = (bif 0x1C ≤ ram 0x700 then ram 0x700
    else bif ram 0x6FC &&& 0x7F != 0 && ram 0x6FC &&& 0x03 == ram 0x45 then 0 else ram 0x703) ∧
  t.ram 0x57 = (bif skidStops ram then 0 else ram 0x57) ∧
  t.ram 0x705 = (bif skidStops ram then 0 else ram 0x705) ∧
  t.ram 0x45 = (bif skidStops ram then ram 0x33 else ram 0x45)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem animSpeed_reach (stop : UInt16) (hstop : ∀ a : UInt16, (0xB58F ≤ a && a ≤ 0xB5CB) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x358C animSpeedCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB58F, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ AnimSpeedSummary ram t := by
  simp only [CodeAt, animSpeedCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB58F, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until 46539
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [AnimSpeedSummary, skidStops]

/-- Holding only Down (say) while walking slowly stops Mario in one frame. -/
theorem animSpeed_stop (ram : UInt16 → UInt8) (hb : ram 0x6FC = 0x04) (hd : ram 0x45 ≠ 0)
    (hs : ram 0x700 < 0x0B) : skidStops ram = true := by
  simp only [skidStops, hb, bne]; revert hd hs; generalize ram 0x45 = d; generalize ram 0x700 = v; bv_decide

end Smb.Routine

namespace Smb.Routine

/-- Cycles of `GetPlayerAnimSpeed` to its RTS. -/
def animCycles (ram : UInt16 → UInt8) : UInt64 :=
  let v := ram 0x700
  let b := ram 0x6FC
  bif 0x1C ≤ v then 26 else
  (bif 0x0E ≤ v then 17 else 18) +
    (bif b &&& 0x7F == 0 then 17
     else bif b &&& 0x03 == ram 0x45 then 32
     else bif 0x0B ≤ v then 33 else 47)

/-- RAM on return (bytes a path leaves alone read `ram i`). -/
def animRam (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  let v := ram 0x700
  let b := ram 0x6FC
  let setRun := 0x1C ≤ v || (b &&& 0x7F != 0 && b &&& 0x03 == ram 0x45)
  bif i == 0x70C then (bif 0x1C ≤ v then 2 else bif 0x0E ≤ v then 4 else 7)
  else bif i == 0x703 && setRun then (bif 0x1C ≤ v then v else 0)
  else bif (i == 0x57 || i == 0x705) && skidStops ram then 0
  else bif i == 0x45 && skidStops ram then ram 0x33
  else ram i

set_option maxHeartbeats 40000000 in
theorem animSpeed_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB58F ≤ a && a ≤ 0xB5CB) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x358C animSpeedCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB58F, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB5CB, animRam ram 0x70C, x,
        (bif 0x1C ≤ ram 0x700 then 0 else bif 0x0E ≤ ram 0x700 then 1 else 2), sp, p'⟩,
        animRam ram, prg, cyc + animCycles ram, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, animSpeedCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB58F, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 46539
  all_goals
    intros
    clear hcode
    subst hrun
    call_finish [animRam, animCycles, skidStops]

end Smb.Routine
