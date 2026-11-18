import Smb.Data.ProofRom
import Smb.Summary
import Smb.Routine.FootCheck

/-!
# The foot check as one call theorem (`GBBAdr` `$DCAB` through the head and foot checks)

Composes `headPart_call`, `bbFeet_call` and `chkFoot_call` through
`DoPlayerSideCheck` (`$DD5E`) or `ImpedePlayerMove`'s RTS (`$DF8A`).
The hypotheses exclude a head coin, a head block hit, a foot coin, the axe,
and pipe entry. The symbolic summary fields `footCheck_*`
keep each path's raw values; the named predicates below (`footTile`, `lands`, `impeded`, …) say what the
paths mean.
-/
namespace Smb.Routine

set_option linter.unusedVariables false

/-- `$DCF6`–`$DD19`: `DoFootCheck`. -/
def doFootCheckCode : List UInt8 :=
  smbPrg% 0xDCF6 36

/-- The metatiles under the left and right foot. -/
def footTileL (prg ram : UInt16 → UInt8) (y : UInt8) : UInt8 := bbTile prg ram 0 (bbOffset prg y + 1)
def footTileR (prg ram : UInt16 → UInt8) (y : UInt8) : UInt8 := bbTile prg ram 0 (bbOffset prg y + 2)
/-- The one `ChkFootMTile` examines: the left foot's, or if that is empty the right foot's. -/
def footTile (prg ram : UInt16 → UInt8) (y : UInt8) : UInt8 :=
  bif footTileL prg ram y == 0 then footTileR prg ram y else footTileL prg ram y
/-- The foot probes run (Mario above `$CF`; the prologue already returns otherwise) and find something. -/
def footProbed (prg ram : UInt16 → UInt8) (y : UInt8) : Bool := ram 0xCE < 0xCF && footTile prg ram y != 0

/-- A foot touches a coin (→ `AwardTouchedCoin`). -/
def footCoin (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  ram 0xCE < 0xCF && (coinTile (footTileL prg ram y) || footTileL prg ram y == 0 && coinTile (footTileR prg ram y))

/-- Standing ground under the feet: `footGround` with the speed after the head check. -/
def footSolid (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  let t := footTile prg ram y
  footProbed prg ram y && !climbable t && headSpeed prg ram y < 0x80 && t != 0xC5 && t != 0x5F && t != 0x60 &&
    ram 0x70E == 0

/-- The axe under the feet, not rising (→ `HandleAxeMetatile`). -/
def footAxeAt (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  footProbed prg ram y && headSpeed prg ram y < 0x80 && footTile prg ram y == 0xC5

/-- Mario lands: feet in rows 0–4 of a solid metatile. -/
def lands (prg ram : UInt16 → UInt8) (y : UInt8) : Bool := footSolid prg ram y && ram 0xCE &&& 0x0F < 5
/-- Mario's feet are deeper in the metatile: `ImpedePlayerMove` instead of landing. -/
def impeded (prg ram : UInt16 → UInt8) (y : UInt8) : Bool := footSolid prg ram y && 5 ≤ ram 0xCE &&& 0x0F

/-- Landing with Down held on the warp-pipe top (→ the pipe entry in `HandlePipeEntry`). -/
def pipeEntryAt (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  lands prg ram y && ram 0x0B &&& 4 != 0 && footTileR prg ram y == 0x11 && footTileL prg ram y == 0x10

/-- Where the foot check ends: `ImpedePlayerMove`'s RTS, or `DoPlayerSideCheck`. -/
def footPc (prg ram : UInt16 → UInt8) (y : UInt8) : UInt16 := bif impeded prg ram y then 0xDF8A else 0xDD5E

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem footCheck_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDCAB ≤ a && a ≤ 0xDD5E || a == 0xBCED || a == 0xDE0E || 0xDEBD ≤ a && a ≤ 0xDEFA ||
      0xDF4A ≤ a && a ≤ 0xDFB8 || 0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hgcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode : CodeAt prg 0x5CBA headChkCode)
    (hfcode : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode : CodeAt prg 0x63AD adderCode)
    (hbcode : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode : CodeAt prg 0x5EC4 landCalleesCode) (hpcode : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
    (hI : (p &&& 4 == 0) = false) (hy : y < 3)
    (hhc : headCoin prg ram y = false) (hhh : headHit prg ram y = false)
    (hfc : footCoin prg ram y = false) (hfa : footAxeAt prg ram y = false)
    (hpe : pipeEntryAt prg ram y = false) :
    ((CPU.runTo (σ := Plain) stop (m + 400)).run ⟨⟨0xDCAB, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  have htab : prg ((0xE3AD + y.toUInt16) &&& 0x7FFF) < 0x10 := by
    have h := hacode; simp only [CodeAt, adderCode, UInt16.reduceAdd] at h
    have : y = 0 ∨ y = 1 ∨ y = 2 := by bv_decide
    rcases this with rfl | rfl | rfl <;> simp [h]
  have htbl : prg 0x5F8B = 0x10 ∧ prg 0x5F8C = 0x61 ∧ prg 0x5F8D = 0x88 ∧ prg 0x5F8E = 0xC4 := by
    have h := htcode; simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at h; simp [h]
  have hrtsb : prg 0x6431 = 0x60 := by
    have h := hbcode; simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at h; simp [h]
  have hf2 := hfcode
  simp only [CodeAt, doFootCheckCode, UInt16.reduceAdd] at hf2
  have ht2 := htcode
  simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at ht2
  replace hf2 := fun (_ : Unit) => hf2
  replace ht2 := fun (_ : Unit) => ht2
  have hsp := headPart_sp y sp p ram prg hI htbl hhh
  -- The exclusions as bitvector facts, so that pruning can use them.
  simp only [headCoin, headHit, footCoin, footAxeAt, pipeEntryAt, lands, footSolid, footProbed, footTile,
    footTileL, footTileR, headSpeed, headBumps, headBlocked, headProbed, headTile, coinTile, solidTile,
    climbable, bbOffset, bne] at hhc hhh hfc hfa hpe
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 400)).run ⟨⟨0xDCAB, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary footCheck hrun [hf2 (), ht2 (), hrtsb, hI, headPart_eb,
      headPart_keeps, headPart_tile, headPart_nobad, hsp, hhc, hhh, hfc, hfa, hpe,
      bbFlags, bbYAdd, bbRam, bbNybble, bbXPos, bbYPos, bbPage,
      bbTile_wr, bbRow_wr, bbLo_wr, bbXSum_wr, bbColumn_wr, bbTile_wrs, bbRow_wrs, bbLo_wrs, bbXSum_wrs,
      bbColumn_wrs] until [56670, 57226, 56846, 57082, 56602, 48365]
    calls [headPart_call, bbFeet_call, chkFoot_call]
    exact finish (exact_finish footCheck)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface footCheck
summary_regs footCheck

end Smb.Routine
