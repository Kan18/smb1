import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Walking off: the start of `PlayerBGCollision` (`$DC64`)

```
PlayerBGCollision:  leave if DisableCollisionDet, or GameEngineSubroutine = $0B or < 4
                    Player_State := 1 if swimming, else 2 (falling) if it was 0 or 3
ChkOnScr:           leave unless Player_Y_HighPos = 1; Player_CollisionBits := $FF
                    leave if Player_Y_Position ≥ $CF
ChkCollSize:        block-buffer offset from crouching, size, swimming
```

Every frame on the ground, Mario is first put in the falling state; only the foot check
afterwards (`LandPlyr`, `landPlyr_reach`) puts him back. None of Mario's vertical state is
touched, so with the ground frame (`groundFrame_reach`: no jump leaves speed, force,
sub-pixel and position as they were) and the last landing (speed and force 0), walking off
starts a fall at speed 0, force 0, and the row offset and sub-pixel Mario stood at: the
walk-off move of `Smb.Vertical`.
-/
namespace Smb.Routine

/-- `$DC64`–`$DCAA`. -/
def bgPrologueCode : List UInt8 :=
  smbPrg% 0xDC64 71

/-- `Player_State` after the prologue. -/
def bgState (ram : UInt16 → UInt8) : UInt8 :=
  bif ram 0x716 != 0 || ram 0x0E == 0x0B || ram 0x0E < 4 then ram 0x1D
  else bif ram 0x704 != 0 then 1
  else bif ram 0x1D == 0 || ram 0x1D == 3 then 2 else ram 0x1D

def WalkOffSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  (t.regs.pc = 0xDC97 ∨ t.regs.pc = 0xDCAB) ∧ t.bad = false ∧ t.ram 0x1D = bgState ram ∧
  t.ram 0x9F = ram 0x9F ∧ t.ram 0x433 = ram 0x433 ∧ t.ram 0x416 = ram 0x416 ∧
  t.ram 0xCE = ram 0xCE ∧ t.ram 0xB5 = ram 0xB5

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem bgPrologue_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDC64 ≤ a && a ≤ 0xDCAB) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x5C64 bgPrologueCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDC64, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ WalkOffSummary ram t := by
  simp only [CodeAt, bgPrologueCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDC64, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI] until [56471, 56491]
  all_goals
    intros
    clear hcode
    subst hrun
    reach_finish [WalkOffSummary, bgState]

/-- On the ground, with collision detection running and not swimming, the prologue switches
Mario to falling and leaves his vertical state alone. -/
theorem walkOff (ram : UInt16 → UInt8) (hd : ram 0x716 = 0) (he : 4 ≤ ram 0x0E) (he' : ram 0x0E ≠ 0x0B)
    (hs : ram 0x704 = 0) (hg : ram 0x1D = 0) : bgState ram = 2 := by
  simp only [bgState, hd, hs, hg]
  have : (ram 0x0E == 0x0B) = false := by simpa using he'
  have : (ram 0x0E < 4 : Bool) = false := by simpa using he
  simp [*]

end Smb.Routine
