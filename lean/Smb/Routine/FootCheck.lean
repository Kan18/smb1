import Smb.Data.ProofRom
import Smb.Summary
import Smb.Routine.HeadBump
import Smb.Routine.Landing
import Smb.Routine.LandPlyr
import Smb.Routine.Impede

namespace Smb.Routine
set_option linter.unusedVariables false

/-- The flags after a head or foot probe: `N`, `Z` from the metatile (`lda $03`), `C`, `V` from
the row's `sbc #$20`, the rest kept. -/
def bbFlags (prg ram : UInt16 → UInt8) (y p : UInt8) : UInt8 :=
  let t := bbTile prg ram 0 y
  let v := (bbYPos ram 0 + bbYAdd prg y) &&& 0xF0
  (p &&& 0x3C) ||| (bif 0x20 ≤ v then 1 else 0) ||| (bif v == 0x80 || v == 0x90 then 0x40 else 0) |||
    (bif t == 0 then 2 else 0) ||| (t &&& 0x80)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem bbHead_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hy : y < 0x1C) :
    ∃ j, ((CPU.runTo (σ := Plain) stop (m + 70)).run ⟨⟨0xE3E9, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xE431, bbTile prg ram 0 y, 0, y, sp, bbFlags prg ram y p⟩,
        bbRam 0 0 y sp prg ram, prg,
        cyc + 151 + (bif (bbLo prg ram 0 y).toUInt16 + (bbRow prg ram 0 y).toUInt16 > 0xFF then 1 else 0),
        bad⟩).2 ∧
      (bbFlags prg ram y p &&& 4 == 0) = false := by
  simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, getBlockBufferAddrCode, UInt16.reduceAdd] at hgcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 70)).run ⟨⟨0xE3E9, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hgcode, hI] until 58417
  all_goals
    intros
    clear hcode
    subst hrun
    simp only [bbFlags]
    (try simp only [bne] at *)
    call_fuel
    apply And.intro
    · congr 2
      all_goals (try congr 1)
      all_goals first
        | rfl
        | (is_regs_eq; congr 1)
        | ((try sym_exec [bne, bbRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos, bbYPos, bbPage]) <;> fun_congr <;> bv_decide (config := { enums := false }))
        | (funext i; (try sym_exec [bne, bbRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos, bbYPos, bbPage]); fun_congr; bv_decide (config := { enums := false }))
      all_goals first
        | rfl
        | ((try sym_exec [bne, bbRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos, bbYPos, bbPage]) <;> fun_congr <;> bv_decide (config := { enums := false }))
    · bv_decide

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem bbFeet_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x63B0 blockBufferCode) (hgcode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (hy : y < 0x1B) :
    ∃ j, ((CPU.runTo (σ := Plain) stop (m + 70)).run ⟨⟨0xE3E8, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xE431, bbTile prg ram 0 (y + 1), 0, y + 1, sp, bbFlags prg ram (y + 1) p⟩,
        bbRam 0 0 (y + 1) sp prg ram, prg,
        cyc + 153 + (bif (bbLo prg ram 0 (y + 1)).toUInt16 + (bbRow prg ram 0 (y + 1)).toUInt16 > 0xFF then 1 else 0),
        bad⟩).2 ∧
      (bbFlags prg ram (y + 1) p &&& 4 == 0) = false := by
  simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, getBlockBufferAddrCode, UInt16.reduceAdd] at hgcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 70)).run ⟨⟨0xE3E8, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hgcode, hI] until 58417
  all_goals
    intros
    clear hcode
    subst hrun
    simp only [bbFlags]
    (try simp only [bne] at *)
    call_fuel
    apply And.intro
    · congr 2
      all_goals (try congr 1)
      all_goals first
        | rfl
        | (is_regs_eq; congr 1)
        | ((try sym_exec [bne, bbRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos, bbYPos, bbPage]) <;> fun_congr <;> bv_decide (config := { enums := false }))
        | (funext i; (try sym_exec [bne, bbRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos, bbYPos, bbPage]); fun_congr; bv_decide (config := { enums := false }))
      all_goals first
        | rfl
        | ((try sym_exec [bne, bbRam, bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbNybble, bbXAdd, bbYAdd, bbXPos, bbYPos, bbPage]) <;> fun_congr <;> bv_decide (config := { enums := false }))
    · bv_decide

/-- `call_finish`, but with the hypotheses unfolded too (`defs` at `*`), and with the RAM compared
pointwise last, so that a failure reports the pointwise counterexample. -/
macro "fc_finish" " [" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (try simp only [bne, $defs,*] at *)
  call_fuel
  repeat apply Exists.intro
  apply And.intro
  · congr 2
    all_goals (try congr 1)
    all_goals first
      | rfl
      | (is_regs_eq; congr 1 <;> (try sym_exec [bne, $defs,*]) <;> fun_congr <;> bv_decide (config := { enums := false }))
      | ((try sym_exec [bne, $defs,*]) <;> fun_congr <;> bv_decide (config := { enums := false }))
      | (funext i; (try sym_exec [bne, $defs,*]); fun_congr; bv_decide (config := { enums := false }))
  · bv_decide (config := { enums := false })))

/-! ROM reads indexed by a register: the address is never in RAM. -/
theorem add_inRom (c : UInt16) (b : UInt8) (h : (0x2000 ≤ c && c ≤ 0xFF00) = true) :
    decide (c + b.toUInt16 < 0x2000) = false := by
  simp only [Bool.and_eq_true] at h; simp only [decide_eq_false_iff_not]; bv_decide
theorem add_readRom (c : UInt16) (b : UInt8) (h : (0x8000 ≤ c && c ≤ 0xFF00) = true) :
    decide (0x8000 ≤ c + b.toUInt16) = true := by
  simp only [Bool.and_eq_true] at h; simp only [decide_eq_true_eq]; bv_decide
theorem page_inRom (c y : UInt16) (h : (0x2000 ≤ c) = true) : decide ((c ||| (y &&& 255)) < 0x2000) = false := by
  simp only [decide_eq_true_eq] at h; simp only [decide_eq_false_iff_not]; bv_decide
theorem page_readRom (c y : UInt16) (h : (0x8000 ≤ c) = true) : decide (0x8000 ≤ (c ||| (y &&& 255))) = true := by
  simp only [decide_eq_true_eq] at h; simp only [decide_eq_true_eq]; bv_decide

/-- Zero-page cells other than the probe's position bytes. -/
abbrev zpOther (a : UInt16) : Bool := a < 0x100 && a != 0x86 && a != 0xCE && a != 0x6D

section strip
variable (prg r : UInt16 → UInt8) (a : UInt16) (s b y : UInt8)
local macro "strip" : tactic => `(tactic| (
  (try simp only [zpOther, bne] at *)
  simp only [bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbXAdd, bbYAdd, bbXPos, bbYPos, bbPage]
  fun_congr; bv_decide))
theorem bbTile_wr (h : zpOther a = true) : bbTile prg (fun i => bif i == a then b else r i) 0 y = bbTile prg r 0 y := by strip
theorem bbRow_wr (h : zpOther a = true) : bbRow prg (fun i => bif i == a then b else r i) 0 y = bbRow prg r 0 y := by strip
theorem bbLo_wr (h : zpOther a = true) : bbLo prg (fun i => bif i == a then b else r i) 0 y = bbLo prg r 0 y := by strip
theorem bbXSum_wr (h : zpOther a = true) : bbXSum prg (fun i => bif i == a then b else r i) 0 y = bbXSum prg r 0 y := by strip
theorem bbColumn_wr (h : zpOther a = true) : bbColumn prg (fun i => bif i == a then b else r i) 0 y = bbColumn prg r 0 y := by strip
theorem bbTile_wrs : bbTile prg (fun i => bif i == (256 ||| s.toUInt16) &&& 2047 then b else r i) 0 y = bbTile prg r 0 y := by strip
theorem bbRow_wrs : bbRow prg (fun i => bif i == (256 ||| s.toUInt16) &&& 2047 then b else r i) 0 y = bbRow prg r 0 y := by strip
theorem bbLo_wrs : bbLo prg (fun i => bif i == (256 ||| s.toUInt16) &&& 2047 then b else r i) 0 y = bbLo prg r 0 y := by strip
theorem bbXSum_wrs : bbXSum prg (fun i => bif i == (256 ||| s.toUInt16) &&& 2047 then b else r i) 0 y = bbXSum prg r 0 y := by strip
theorem bbColumn_wrs : bbColumn prg (fun i => bif i == (256 ||| s.toUInt16) &&& 2047 then b else r i) 0 y = bbColumn prg r 0 y := by strip
end strip

/-- `$E3AD`–`$E3AF`: `BlockBufferAdderData`. -/
def adderCode : List UInt8 := smbPrg% 0xE3AD 3
/-- `$DC62`–`$DC64`: `PlayerBGUpperExtent` and the next byte (read for a crouching small Mario). -/
def upperExtCode : List UInt8 := smbPrg% 0xDC62 3
/-- `$DCAB`–`$DCB9`: `GBBAdr`. -/
def gbbAdrCode : List UInt8 :=
  smbPrg% 0xDCAB 15

/-- `$EB`: the block-buffer adder offset for the collision box (`BlockBufferAdderData[Y]`). -/
def bbOffset (prg : UInt16 → UInt8) (y : UInt8) : UInt8 := prg ((0xE3AD + y.toUInt16) &&& 0x7FFF)

/-- `CheckForCoinMTiles`. -/
def coinTile (t : UInt8) : Bool := t == 0xC2 || t == 0xC3

/-- `CheckForSolidMTiles`: at least `SolidMTileUpperExt` of the metatile's palette group. -/
def solidTile (t : UInt8) : Bool :=
  let ext : UInt8 := bif t >>> 6 == 0 then 0x10 else bif t >>> 6 == 1 then 0x61 else
    bif t >>> 6 == 2 then 0x88 else 0xC4
  ext ≤ t

/-- The metatile above Mario's head. -/
def headTile (prg ram : UInt16 → UInt8) (y : UInt8) : UInt8 := bbTile prg ram 0 (bbOffset prg y)

/-- Low enough on the screen for the head probe: `Player_Y_Position ≥ PlayerBGUpperExtent[size + crouch]`. -/
def headProbed (prg ram : UInt16 → UInt8) : Bool :=
  prg ((0xDC62 + (ram 0x754 + bif ram 0x714 == 0 then 0 else 1).toUInt16) &&& 0x7FFF) ≤ ram 0xCE

/-- The head touches a coin (→ `AwardTouchedCoin`). -/
def headCoin (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  headProbed prg ram && coinTile (headTile prg ram y)

/-- Rising into a non-empty metatile with the head (the probe's row offset at least 4). -/
def headBlocked (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  let t := headTile prg ram y
  headProbed prg ram && t != 0 && !coinTile t && 0x80 ≤ ram 0x9F && 4 ≤ ram 0xCE &&& 0x0F

/-- The block is hit (`PlayerHeadCollision`: bump or break it): not solid, not a water level,
no block bouncing. -/
def headHit (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  headBlocked prg ram y && !solidTile (headTile prg ram y) && ram 0x74E != 0 && ram 0x784 == 0

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_summarize headPart (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDCAB ≤ a && a ≤ 0xDCF6 || a == 0xDD1A || a == 0xBCED || 0xDF8B ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hgcode : CodeAt prg 0x5CAB gbbAdrCode) (hcode : CodeAt prg 0x5CBA headChkCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode)
    (hbcode : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (htab : bbOffset prg y < 0x10) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 120)).run ⟨⟨0xDCAB, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ True := by
  simp only [bbOffset] at htab
  simp only [CodeAt, gbbAdrCode, UInt16.reduceAdd] at hgcode
  simp only [CodeAt, headChkCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at htcode
  have hb2 := hbcode
  simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at hb2
  replace hgcode := fun (_ : Unit) => hgcode
  replace hcode := fun (_ : Unit) => hcode
  replace htcode := fun (_ : Unit) => htcode
  replace hb2 := fun (_ : Unit) => hb2
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 120)).run ⟨⟨0xDCAB, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary headPart hrun [hgcode (), hcode (), htcode (), hb2 (), hI, add_inRom, add_readRom, page_inRom, page_readRom, bbFlags, bbYAdd, bbRam, bbNybble, bbXPos, bbYPos, bbPage,
      bbTile_wr, bbRow_wr, bbLo_wr, bbXSum_wr, bbColumn_wr, bbTile_wrs, bbRow_wrs, bbLo_wrs, bbXSum_wrs,
      bbColumn_wrs] until [56566, 56602, 48365]
    calls [bbHead_call]

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
theorem headPart_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDCAB ≤ a && a ≤ 0xDCF6 || a == 0xDD1A || a == 0xBCED || 0xDF8B ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hgcode : CodeAt prg 0x5CAB gbbAdrCode) (hcode : CodeAt prg 0x5CBA headChkCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode)
    (hbcode : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hI : (p &&& 4 == 0) = false) (htab : bbOffset prg y < 0x10) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 120)).run ⟨⟨0xDCAB, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨bif headCoin prg ram y then 0xDD1A else bif headHit prg ram y then 0xBCED
          else 0xDCF6, headPart_a y ram prg,
        headPart_x y ram prg, headPart_y y ram prg,
        headPart_s y sp ram prg, p'⟩, headPart_ram y sp ram prg, prg,
        headPart_cyc y ram prg cyc, headPart_bad bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [bbOffset] at htab
  have htbl : prg 0x5F8B = 0x10 ∧ prg 0x5F8C = 0x61 ∧ prg 0x5F8D = 0x88 ∧ prg 0x5F8E = 0xC4 := by
    have h := htcode; simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at h; simp [h]
  simp only [CodeAt, gbbAdrCode, UInt16.reduceAdd] at hgcode
  simp only [CodeAt, headChkCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, tileClassCode, UInt16.reduceAdd] at htcode
  have hb2 := hbcode
  simp only [CodeAt, blockBufferCode, UInt16.reduceAdd] at hb2
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 120)).run ⟨⟨0xDCAB, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hgcode, hcode, htcode, hb2, hI, add_inRom, add_readRom, page_inRom, page_readRom, bbFlags, bbYAdd, bbRam, bbNybble, bbXPos, bbYPos, bbPage,
      bbTile_wr, bbRow_wr, bbLo_wr, bbXSum_wr, bbColumn_wr, bbTile_wrs, bbRow_wrs, bbLo_wrs, bbXSum_wrs,
      bbColumn_wrs] until [56566, 56602, 48365]
    calls [bbHead_call]
  all_goals
    intros
    clear hgcode hcode htcode hb2 hbcode hbacode
    subst_vars
    fc_finish [headCoin, headHit, headBlocked, headProbed, headTile, coinTile, solidTile, bbOffset,
      headPart_a, headPart_x, headPart_y, headPart_s, headPart_ram, headPart_cyc, headPart_bad, bbFlags, bbYPos, bbYAdd,
      headPart_c0, headPart_c1, headPart_c2, headPart_c3, headPart_c4, headPart_c5, headPart_c6, headPart_c7, headPart_c8, headPart_c9, headPart_c10, headPart_c11, headPart_c12, headPart_c13, headPart_c14, headPart_c15, headPart_c16, headPart_c17, headPart_c18, headPart_c19, headPart_c20]

/-- The head bump (`NYSpd`): rising into a solid metatile, or a water level, or a block still
bouncing. -/
def headBumps (prg ram : UInt16 → UInt8) (y : UInt8) : Bool :=
  headBlocked prg ram y && (solidTile (headTile prg ram y) || ram 0x74E == 0 || ram 0x784 != 0)

/-- `Player_Y_Speed` after the head check. -/
def headSpeed (prg ram : UInt16 → UInt8) (y : UInt8) : UInt8 := bif headBumps prg ram y then 1 else ram 0x9F

/-- Cells the head check leaves alone: all but `$02`–`$07`, `Player_Y_Speed`, `$EB`, the sound
queues `$FE`/`$FF` and the stack page. -/
def headKeeps (i : UInt16) : Bool :=
  i < 2 || (8 ≤ i && i < 0x100 && i != 0x9F && i != 0xEB && i != 0xFE && i != 0xFF) || 0x200 ≤ i

section headPart
variable (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
  (hI : (p &&& 4 == 0) = false)
include hI

theorem headPart_keeps (i : UInt16) (h : headKeeps i = true) :
   
    headPart_ram y sp ram prg i = ram i := by
  simp only [headKeeps, bne] at h
  sym_exec [headPart_ram, bbFlags, bbRam, bbYPos, bbYAdd, bbNybble, bbXPos, bbPage, bbTile_wr, bbRow_wr, bbLo_wr, bbXSum_wr, bbColumn_wr, bbTile_wrs, bbRow_wrs, bbLo_wrs, bbXSum_wrs, bbColumn_wrs, bne]
  all_goals bv_decide (config := { enums := false })

omit hI in
theorem headPart_eb : headPart_ram y sp ram prg 0xEB = prg ((0xE3AD + y.toUInt16) &&& 0x7FFF) := by
  sym_exec [headPart_ram, bbFlags, bbRam, bbYPos, bbYAdd, bbNybble, bbXPos, bbPage, bbTile_wr, bbRow_wr, bbLo_wr, bbXSum_wr, bbColumn_wr, bbTile_wrs, bbRow_wrs, bbLo_wrs, bbXSum_wrs, bbColumn_wrs, bne]
  all_goals bv_decide (config := { enums := false })

theorem headPart_tile (k : UInt8) : bbTile prg (headPart_ram y sp ram prg) 0 k = bbTile prg ram 0 k := by
  simp only [bbTile, bbAddr, bbRow, bbLo, bbColumn, bbXSum, bbXAdd, bbYAdd, bbXPos, bbYPos, bbPage]
  simp (disch := (simp only [headKeeps, bne]; bv_decide)) only [headPart_keeps y sp p ram prg hI]
  all_goals (fun_congr; bv_decide)

theorem headPart_sp (htbl : prg 0x5F8B = 0x10 ∧ prg 0x5F8C = 0x61 ∧ prg 0x5F8D = 0x88 ∧ prg 0x5F8E = 0xC4)
    (hhit : headHit prg ram y = false) : headPart_s y sp ram prg = sp := by
  obtain ⟨h1, h2, h3, h4⟩ := htbl
  revert hhit
  sym_exec [headPart_s, headPart_c0, headPart_c1, headPart_c2, headPart_c3, headPart_c4, headPart_c5, headPart_c6, headPart_c7, headPart_c8, headPart_c9, headPart_c10, headPart_c11, headPart_c12, headPart_c13, headPart_c14, headPart_c15, headPart_c16, headPart_c17, headPart_c18, headPart_c19, headPart_c20, headHit, headBlocked, headTile, headProbed, coinTile, solidTile, bbOffset, bbFlags, bbRam, bbYPos, bbYAdd, bbNybble, bbXPos, bbPage, bbTile_wr, bbRow_wr, bbLo_wr, bbXSum_wr, bbColumn_wr, bbTile_wrs, bbRow_wrs, bbLo_wrs, bbXSum_wrs, bbColumn_wrs, bne]
  fun_congr
  all_goals bv_decide (config := { enums := false })

omit hI in
theorem headPart_nobad : headPart_bad bad = bad := by
  simp only [headPart_bad]
end headPart


/-! ## `ChkFootMTile` (`$DD1D`) to the end -/

/-- `$DEEE`–`$DEF9`: `HandlePipeEntry`'s metatile tests. -/
def pipeTestCode : List UInt8 :=
  smbPrg% 0xDEEE 12

/-- `ChkFootMTile` on foot metatile `t` reaches the axe test with the axe (→ `HandleAxeMetatile`). -/
def footAxe (t : UInt8) (ram : UInt16 → UInt8) : Bool := !climbable t && ram 0x9F < 0x80 && t == 0xC5

/-- `t` is ground to stand on: not climbable, not the axe, not a hidden block, Mario not rising,
and no jumpspring animating. Then the row offset `$04` decides: `< 5` lands, otherwise impeded. -/
def footGround (t : UInt8) (ram : UInt16 → UInt8) : Bool :=
  !climbable t && ram 0x9F < 0x80 && t != 0xC5 && t != 0x5F && t != 0x60 && ram 0x70E == 0

/-- Down held over the warp-pipe top (`$00` = right foot `$11`, `$01` = left foot `$10`): the pipe
entry of `HandlePipeEntry`. -/
def pipeDown (ram : UInt16 → UInt8) : Bool := ram 0x0B &&& 4 != 0 && ram 0 == 0x11 && ram 1 == 0x10

set_option maxHeartbeats 40000000 in
sym_summarize chkFoot (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDD1D ≤ a && a ≤ 0xDD5E || a == 0xDE0E || 0xDEBD ≤ a && a ≤ 0xDEFA ||
      0xDF4A ≤ a && a ≤ 0xDF8A || 0xDF96 ≤ a && a ≤ 0xDFB8) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode : CodeAt prg 0x5EC4 landCalleesCode) (hpcode : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
    (hI : (p &&& 4 == 0) = false) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xDD1D, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ True := by
  simp only [CodeAt, chkFootCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, landPlyrCode, UInt16.reduceAdd] at hlcode
  simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at hccode
  simp only [CodeAt, invisibleTilesCode, UInt16.reduceAdd] at hicode
  simp only [CodeAt, landCalleesCode, UInt16.reduceAdd] at hjcode
  simp only [CodeAt, pipeTestCode, UInt16.reduceAdd] at hpcode
  simp only [CodeAt, impedeCode, UInt16.reduceAdd] at himcode
  -- (As `∀` facts, which `sym_summary`'s side `bv_decide` calls leave out.)
  replace hcode := fun (_ : Unit) => hcode
  replace hlcode := fun (_ : Unit) => hlcode
  replace hccode := fun (_ : Unit) => hccode
  replace hicode := fun (_ : Unit) => hicode
  replace hjcode := fun (_ : Unit) => hjcode
  replace hpcode := fun (_ : Unit) => hpcode
  replace himcode := fun (_ : Unit) => himcode
  replace hrts := fun (_ : Unit) => hrts
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xDD1D, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary chkFoot hrun [hcode (), hlcode (), hccode (), hicode (), hjcode (), hpcode (), hrts (), himcode (), hI]
    until [56670, 57226, 56846, 57082]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem chkFoot_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xDD1D ≤ a && a ≤ 0xDD5E || a == 0xDE0E || 0xDEBD ≤ a && a ≤ 0xDEFA ||
      0xDF4A ≤ a && a ≤ 0xDF8A || 0xDF96 ≤ a && a ≤ 0xDFB8) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode : CodeAt prg 0x5EC4 landCalleesCode) (hpcode : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
    (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xDD1D, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨bif footAxe a ram then 0xDE0E
          else bif footGround a ram && ram 4 < 5 && pipeDown ram then 0xDEFA
          else bif footGround a ram && 5 ≤ ram 4 then 0xDF8A else 0xDD5E, chkFoot_a a ram prg,
        chkFoot_x a ram prg, chkFoot_y a ram prg,
        chkFoot_s a sp ram prg, p'⟩, chkFoot_ram a sp ram prg, prg,
        chkFoot_cyc a ram prg cyc, chkFoot_bad a bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  have htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6 := by
    have h := hccode; simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at h; simp [h]
  simp only [CodeAt, chkFootCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, landPlyrCode, UInt16.reduceAdd] at hlcode
  simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at hccode
  simp only [CodeAt, invisibleTilesCode, UInt16.reduceAdd] at hicode
  simp only [CodeAt, landCalleesCode, UInt16.reduceAdd] at hjcode
  simp only [CodeAt, pipeTestCode, UInt16.reduceAdd] at hpcode
  simp only [CodeAt, impedeCode, UInt16.reduceAdd] at himcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 80)).run ⟨⟨0xDD1D, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hlcode, hccode, hicode, hjcode, hpcode, hrts, himcode, hI] until [56670, 57226, 56846, 57082]
  all_goals
    intros
    clear hcode hlcode hccode hicode hjcode hpcode hrts himcode
    subst_vars
    fc_finish [footAxe, footGround, pipeDown, climbable, climbExt, chkFoot_a, chkFoot_x, chkFoot_y, chkFoot_s,
      chkFoot_ram, chkFoot_cyc, chkFoot_bad, chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, chkFoot_c5, chkFoot_c6, chkFoot_c7, chkFoot_c8, chkFoot_c9, chkFoot_c10, chkFoot_c11, chkFoot_c12, chkFoot_c13, chkFoot_c14, chkFoot_c15, chkFoot_c16, chkFoot_c17, chkFoot_c18, chkFoot_c19, chkFoot_c20, chkFoot_c21, chkFoot_c22, chkFoot_c23, chkFoot_c24]

end Smb.Routine
