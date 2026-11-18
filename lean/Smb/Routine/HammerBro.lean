import Smb.Data.ProofRom
import Smb.Routine.Firebar
import Smb.Certificates

/-!
# A Hammer Bro inherits its jump countdown (`InitHammerBro`, `$C328`)

```
InitHammerBro:  HammerThrowingTimer,x := 0; Enemy_X_Speed,x := 0;
                EnemyIntervalTimer,x := HBroWalkingTimerData[SecondaryHardMode]
SetBBox:        Enemy_BoundBoxCtrl,x := $0B; Enemy_MovingDir,x := 2
InitVStf:       Enemy_Y_Speed,x := 0; Enemy_Y_MoveForce,x := 0
```

`HammerBroJumpTimer,x` (`$3C,x`) is not set (`hammerBro_inherits`). The jump logic reads it
first (`ChkJH`: jump now if 0, else count down), and only Hammer Bros write it, so a Hammer Bro
starts with the countdown left by the previous Hammer Bro in its slot (the area init clears
RAM, so the first ones start at 0). The TAS does this in 8-3 (`tas_hammerBro_inherits`,
certified: the timer values at spawn): the second wave of Hammer Bros spawns with leftover
timers 161, 125, 54 and 119 instead of 0. What follows is from a replay trace, not certified:
three of them leave the screen before their timers run out (the countdown does not run every
frame: 161 is down to 81 after 111 frames), and the one starting at 54 makes its first jump
55 frames after spawning (`ChkJH` tests for 0 before counting down).
-/
namespace Smb.Routine

/-- `$C326`–`$C33C`: `HBroWalkingTimerData` and `InitHammerBro`. -/
def initHammerBroCode : List UInt8 :=
  smbPrg% 0xC326 23

/-- `$C35C`–`$C36A`: `SetBBox` and `InitVStf`. -/
def setBBoxCode : List UInt8 :=
  smbPrg% 0xC35C 15

def HammerSummary (x : UInt8) (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xC36A ∧ t.bad = false ∧ t.ram (zpx 0x3C x) = ram (zpx 0x3C x)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem hammerBro_inherits (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xC328 ≤ a && a ≤ 0xC33C || 0xC35C ≤ a && a ≤ 0xC36A) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x4326 initHammerBroCode) (hbcode : CodeAt prg 0x435C setBBoxCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x10) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xC328, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ HammerSummary x ram t := by
  simp only [CodeAt, initHammerBroCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, setBBoxCode, UInt16.reduceAdd] at hbcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xC328, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hbcode, hI] until 50026
  all_goals
    intros
    clear hcode hbcode
    subst hrun
    reach_finish [HammerSummary, zpx]

/-- In 8-3 the TAS spawns Hammer Bros into slots 0, 1, 1, 2 whose jump timers still hold
161, 125, 54, 119 from the previous Hammer Bros there (`Smb.Certificates.hammerCert`). -/
theorem tas_hammerBro_inherits : Smb.Certificates.hammerCert = true := by native_decide

end Smb.Routine
