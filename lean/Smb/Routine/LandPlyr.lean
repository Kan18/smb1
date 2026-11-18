import Smb.Data.ProofRom
import Smb.Routine.Landing

/-!
# `LandPlyr` (`$DD44`): what landing does to Mario's vertical state

```
LandPlyr:  ChkForLandJumpSpring (on a jumpspring metatile $67/$68: VerticalForce := $70, …)
           Player_Y_Position &= $F0          (snap to the metatile row)
           HandlePipeEntry                   (Down held over a warp pipe: start the pipe entry)
           Player_Y_Speed := 0; Player_Y_MoveForce := 0; StompChainCounter := 0
InitSteP:  Player_State := 0
```

The sub-pixel `Player_YMF_Dummy` is *not* reset: it carries into the next fall or jumpspring
bounce (a jump resets it). This is the landing move of the abstract vertical model
(`Smb.Vertical`). Stated for Down not held (no pipe entry).
-/
namespace Smb.Routine

/-- `$DD44`–`$DD5D`. -/
def landPlyrCode : List UInt8 :=
  smbPrg% 0xDD44 26

/-- `$DEC4`–`$DEEF`: `ChkForLandJumpSpring`, `ChkJumpspringMetatiles`, the start of
`HandlePipeEntry`. -/
def landCalleesCode : List UInt8 :=
  smbPrg% 0xDEC4 42

def LandSummary (ram : UInt16 → UInt8) (tile : UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0xDD5E ∧ t.bad = false ∧
  t.ram 0xCE = ram 0xCE &&& 0xF0 ∧ t.ram 0x9F = 0 ∧ t.ram 0x433 = 0 ∧ t.ram 0x1D = 0 ∧
  t.ram 0x416 = ram 0x416 ∧ t.ram 0xB5 = ram 0xB5 ∧
  t.ram 0x709 = (bif tile == 0x67 || tile == 0x68 then 0x70 else ram 0x709)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem landPlyr_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDD44 ≤ a && a ≤ 0xDD5E || 0xDEC4 ≤ a && a ≤ 0xDEEF || a == 0xDF4A) = true →
      a ≠ stop)
    (m : Nat) (tile x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x5D44 landPlyrCode) (hccode : CodeAt prg 0x5EC4 landCalleesCode)
    (hrts : prg 0x5F4A = 0x60) (hI : (p &&& 4 == 0) = false) (hdown : ram 0x0B &&& 4 = 0)
    (hsp : 0x10 ≤ sp) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDD44, tile, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ LandSummary ram tile t := by
  simp only [CodeAt, landPlyrCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, landCalleesCode, UInt16.reduceAdd] at hccode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDD44, tile, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hccode, hrts, hI] until 56670
  all_goals
    intros
    clear hcode hccode hrts
    subst hrun
    reach_finish [LandSummary]

end Smb.Routine
