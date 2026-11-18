import Smb.Data.ProofRom
import Smb.Routine.Climb

/-!
# Landing: `ChkFootMTile` (`$DD1D`)

Part of `PlayerBGCollision`, reached when a foot probe found a non-empty metatile (in `A`;
`$04` = `Player_Y_Position & $0F`, the sub-tile offset). Which way it goes:

```
ChkFootMTile:  climbable (metatile ≥ ClimbMTileUpperExt[metatile >> 6]) → DoPlayerSideCheck
               rising (Player_Y_Speed < 0)                              → DoPlayerSideCheck
               axe ($C5)                                                → HandleAxeMetatile
               hidden coin / 1-up block ($5F, $60)                     → DoPlayerSideCheck
               jumpspring animating                                     → InitSteP
               $04 < 5                                                  → LandPlyr
               otherwise                                                → ImpedePlayerMove (pushed sideways)
```

So Mario lands only if his feet are in rows 0–4 of the metatile: this is the five-pixel window
that the speed-5 floor clip crosses in one frame. Note that the test is `Player_Y_Position`'s
low nybble, so the window is the same for every metatile row.
-/
namespace Smb.Routine

/-- `$DD1D`–`$DD43`. -/
def chkFootCode : List UInt8 :=
  smbPrg% 0xDD1D 39

/-- `$DF96`–`$DFB8`: `ClimbMTileUpperExt`, `CheckForClimbMTiles`, `CheckForCoinMTiles`,
`GetMTileAttrib`. -/
def climbTilesCode : List UInt8 :=
  smbPrg% 0xDF96 35

/-- `$DEBD`–`$DEC3`: `ChkInvisibleMTiles`. -/
def invisibleTilesCode : List UInt8 :=
  smbPrg% 0xDEBD 7

/-- Where `ChkFootMTile` goes, for foot metatile `t`. -/
def footExit (t : UInt8) (ram : UInt16 → UInt8) : UInt16 :=
  bif climbable t || 0x80 ≤ ram 0x9F then 0xDD5E
  else bif t == 0xC5 then 0xDE0E
  else bif t == 0x5F || t == 0x60 then 0xDD5E
  else bif ram 0x70E != 0 then 0xDD5A
  else bif ram 4 < 5 then 0xDD44
  else 0xDF4B

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
theorem chkFootMTile_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDD1D ≤ a && a ≤ 0xDFB8) = true → a ≠ stop)
    (m : Nat) (t x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hccode : CodeAt prg 0x5F96 climbTilesCode)
    (hicode : CodeAt prg 0x5EBD invisibleTilesCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j s, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDD1D, t, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run s).2 ∧ s.regs.pc = footExit t ram ∧ s.bad = false := by
  simp only [CodeAt, chkFootCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at hccode
  simp only [CodeAt, invisibleTilesCode, UInt16.reduceAdd] at hicode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDD1D, t, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hccode, hicode, hI] until [56670, 56846, 56666, 56644, 57163]
  all_goals
    intros
    clear hcode hicode
    subst hrun
    reach_finish [footExit, climbable, climbExt]

end Smb.Routine
