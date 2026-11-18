import Smb.Data.ProofRom
import Smb.Routine.BlockBuffer

/-!
# Head bump (`PlayerBGCollision`'s head check, `$DCBA`)

```
HeadChk:  unless too high: probe above the head (BlockBufferColli_Head)
          coin → AwardTouchedCoin;  not rising, or sub-tile offset < 4 → DoFootCheck
          solid metatile (or water area, or a block still bouncing) → NYSpd: Player_Y_Speed := 1
          otherwise PlayerHeadCollision (bump or break the block: excluded here)
```

Of Mario's vertical state only the speed byte can change, to 1; the force, sub-pixel and
position are kept. This is the `NYSpd` head-bump move of the abstract vertical model
(`BumpBlock` and `BrickShatter` set speed 0 and `$FE` and are not covered here).
-/
namespace Smb.Routine

/-- `$DCBA`–`$DCF5`. -/
def headChkCode : List UInt8 :=
  smbPrg% 0xDCBA 60

/-- `$DF8B`–`$DFB8`: `SolidMTileUpperExt`, `CheckForSolidMTiles`, `ClimbMTileUpperExt`,
`CheckForClimbMTiles`, `CheckForCoinMTiles`, `GetMTileAttrib`. -/
def tileClassCode : List UInt8 :=
  smbPrg% 0xDF8B 46

def HeadSummary (ram : UInt16 → UInt8) (t : Plain) : Prop :=
  (t.regs.pc = 0xDCF6 ∨ t.regs.pc = 0xDD1A) ∧ t.bad = false ∧
  (t.ram 0x9F = ram 0x9F ∨ t.ram 0x9F = 1) ∧
  t.ram 0x433 = ram 0x433 ∧ t.ram 0x416 = ram 0x416 ∧ t.ram 0xCE = ram 0xCE ∧ t.ram 0xB5 = ram 0xB5

set_option linter.unusedVariables false

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
theorem headChk_reach (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDCBA ≤ a && a ≤ 0xDD1A || 0xDF8B ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x5CBA headChkCode) (htcode : CodeAt prg 0x5F8B tileClassCode)
    (hbcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hy : y < 0x1C) (hsp : 0x10 ≤ sp)
    (hnobump : ram 0x74E = 0 ∨ ram 0x784 ≠ 0) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xDCBA, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ HeadSummary ram t := by
  -- The head entry `$E3E9`: `lda #0`, then `.db $2C` (`BIT $01A9`, skipping the side entry's
  -- `lda #1`), `ldx #0`; and the RTS.
  have hrts : prg 0x6431 = 0x60 ∧ prg 0x63E9 = 0xA9 ∧ prg 0x63EA = 0x00 ∧ prg 0x63EB = 0x2C ∧
      prg 0x63EE = 0xA2 ∧ prg 0x63EF = 0x00 ∧ prg 0x63EC = 0xA9 ∧ prg 0x63ED = 0x01 := by
    have h := hbcode; simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at h; simp [h]
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩ := hrts
  simp only [CodeAt, headChkCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at htcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xDCBA, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, htcode, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hI, bbRam] until [56566, 56602]
    calls [blockBufferCollision_call]
  all_goals
    intros
    clear hcode htcode hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
    subst hrun
    reach_finish_all [HeadSummary, bbRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd,
      bbYAdd, bbXPos, bbYPos, bbPage]

end Smb.Routine
