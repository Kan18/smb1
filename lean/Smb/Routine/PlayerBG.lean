import Smb.Data.ProofRom
import Smb.Summary
import Smb.Routine.FootCheckCall
import Smb.Routine.SideCheck

/-!
# `PlayerBGCollision` (`$DC64`), one call theorem per way out

The prologue in two segments: the early exits (`bgPre`, to `ExPBGCol`'s RTS `$DC97` or on to `ChkCollSize` `$DC98`) and the
offset for Mario's size (`bgSize`). Then `footCheck_call`, and on one of its exits `sideCheck_call`. Each exit is a
theorem with a hypothesis saying the path takes it (`summary_go`: `hgo`, `hfoot`), so a summary's many paths stay one:
`bgPre_exit_call` (leaves early), `bgImpede_call` (`ImpedePlayerMove`'s RTS `$DF8A`), `bgSide_call` (`$DD9B`/`$DE02`).
The exclusions (coins, the axe, pipes, climbing, `heb`) are stated on the RAM where the code reads them.
-/
namespace Smb.Routine
set_option linter.unusedVariables false

/-- `$DC64`–`$DC97`: `PlayerBGCollision`, the early exits. -/
def bgPreCode : List UInt8 := smbPrg% 0xDC64 52
/-- `$DC98`–`$DCAA`: `ChkCollSize`, the offset for Mario's size. -/
def bgSizeCode : List UInt8 := smbPrg% 0xDC98 19

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
sym_theorem bgPre_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xDC64 ≤ a && a ≤ 0xDC98) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x5C64 bgPreCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDC64, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, bgPreCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xDC64, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary bgPre hrun [hcode, hI] until [56471, 56472] exact finish (clear hcode; exact_finish bgPre)
summary_interface bgPre
summary_regs bgPre

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
sym_theorem bgSize_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xDC98 ≤ a && a ≤ 0xDCAB) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x5C98 bgSizeCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xDC98, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, bgSizeCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xDC98, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary bgSize hrun [hcode, hI] until 56491 exact finish (clear hcode; exact_finish bgSize)
summary_regs bgSize
summary_interface bgSize
theorem bgSize_y_lt (ram : UInt16 → UInt8) : bgSize_y ram < 3 := by
  delta bgSize_y
  bv_decide

summary_go bgPre 0xDC98 go
summary_go bgPre 0xDC97 exit
summary_go footCheck 0xDD5E side
summary_go footCheck 0xDF8A impede

/-- The RAM and `Y` at `GBBAdr`, on the path through the prologue. -/
noncomputable def bgRam (ram : UInt16 → UInt8) : UInt16 → UInt8 := bgSize_ram (bgPre_ram ram)
noncomputable def bgY (ram : UInt16 → UInt8) : UInt8 := bgSize_y (bgPre_ram ram)
/-- The RAM after the foot check. -/
noncomputable def bgFootRam (sp : UInt8) (prg ram : UInt16 → UInt8) : UInt16 → UInt8 := footCheck_ram (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem bgSide_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x9BDD ≤ a && a ≤ 0x9BF5 || a == 0xBCED || 0xDC64 ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hprecode : CodeAt prg 0x5C64 bgPreCode) (hszcode : CodeAt prg 0x5C98 bgSizeCode)
    (hgcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode : CodeAt prg 0x5CBA headChkCode)
    (hfcode : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode : CodeAt prg 0x63AD adderCode)
    (hbcode : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode : CodeAt prg 0x5EC4 landCalleesCode) (hpcode : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
    (h1code : CodeAt prg 0x5D5E sideCheckCode) (h2code : CodeAt prg 0x5DFF stopPlayerMoveCode)
    (h3code : CodeAt prg 0x5EBD chkInvisibleCode) (h4code : CodeAt prg 0x5EDD chkJumpspringCode)
    (hI : (p &&& 4 == 0) = false)
    (hgo : bgPre_pc ram = 0xDC98)
    (hhc : headCoin prg (bgRam ram) (bgY ram) = false) (hhh : headHit prg (bgRam ram) (bgY ram) = false)
    (hfc : footCoin prg (bgRam ram) (bgY ram) = false) (hfa : footAxeAt prg (bgRam ram) (bgY ram) = false)
    (hpe : pipeEntryAt prg (bgRam ram) (bgY ram) = false)
    (hfoot : footCheck_pc (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg = 0xDD5E)
    (heb : bgFootRam sp prg ram 0xEB < 0x16) (hcoin : noSideCoin prg (bgFootRam sp prg ram) = true)
    (hclimb : noSideClimb prg (bgFootRam sp prg ram) = true)
    (hpipe : noSidePipeEntry prg (bgFootRam sp prg ram) = true) :
    ((CPU.runTo (σ := Plain) stop (m + 1200)).run ⟨⟨0xDC64, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  have hsPre : ∀ a : UInt16, (0xDC64 ≤ a && a ≤ 0xDC98) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsSize : ∀ a : UInt16, (0xDC98 ≤ a && a ≤ 0xDCAB) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsFoot : ∀ a : UInt16, (0xDCAB ≤ a && a ≤ 0xDD5E || a == 0xBCED || a == 0xDE0E || 0xDEBD ≤ a && a ≤ 0xDEFA ||
      0xDF4A ≤ a && a ≤ 0xDFB8 || 0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsSide : ∀ a : UInt16, (0xDD5E ≤ a && a ≤ 0xDDCD || 0xDDFF ≤ a && a ≤ 0xDE02 || 0xDEBD ≤ a && a ≤ 0xDEC3 ||
      0xDEDD ≤ a && a ≤ 0xDEE7 || 0xDF4B ≤ a && a ≤ 0xDFB8 || 0xE3B0 ≤ a && a ≤ 0xE431 ||
      0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hy := bgSize_y_lt (bgPre_ram ram)
  simp only [bgRam, bgY, bgFootRam] at hhc hhh hfc hfa hpe hfoot heb hcoin hclimb hpipe
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 1200)).run ⟨⟨0xDC64, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary bgSide hrun [hI, bgSize_pc] until [56731, 56834]
    calls [bgPre_go_call, bgSize_call, footCheck_side_call, sideCheck_call]
    exact finish (exact_finish bgSide)
summary_interface bgSide
summary_regs bgSide

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem bgImpede_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x9BDD ≤ a && a ≤ 0x9BF5 || a == 0xBCED || 0xDC64 ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hprecode : CodeAt prg 0x5C64 bgPreCode) (hszcode : CodeAt prg 0x5C98 bgSizeCode)
    (hgcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode : CodeAt prg 0x5CBA headChkCode)
    (hfcode : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode : CodeAt prg 0x63AD adderCode)
    (hbcode : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode : CodeAt prg 0x5EC4 landCalleesCode) (hpcode : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
    (hI : (p &&& 4 == 0) = false)
    (hgo : bgPre_pc ram = 0xDC98)
    (hhc : headCoin prg (bgRam ram) (bgY ram) = false) (hhh : headHit prg (bgRam ram) (bgY ram) = false)
    (hfc : footCoin prg (bgRam ram) (bgY ram) = false) (hfa : footAxeAt prg (bgRam ram) (bgY ram) = false)
    (hpe : pipeEntryAt prg (bgRam ram) (bgY ram) = false)
    (hfoot : footCheck_pc (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg = 0xDF8A) :
    ((CPU.runTo (σ := Plain) stop (m + 1200)).run ⟨⟨0xDC64, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  have hsPre : ∀ a : UInt16, (0xDC64 ≤ a && a ≤ 0xDC98) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsSize : ∀ a : UInt16, (0xDC98 ≤ a && a ≤ 0xDCAB) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsFoot : ∀ a : UInt16, (0xDCAB ≤ a && a ≤ 0xDD5E || a == 0xBCED || a == 0xDE0E || 0xDEBD ≤ a && a ≤ 0xDEFA ||
      0xDF4A ≤ a && a ≤ 0xDFB8 || 0xE3B0 ≤ a && a ≤ 0xE431 || 0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsSide : ∀ a : UInt16, (0xDD5E ≤ a && a ≤ 0xDDCD || 0xDDFF ≤ a && a ≤ 0xDE02 || 0xDEBD ≤ a && a ≤ 0xDEC3 ||
      0xDEDD ≤ a && a ≤ 0xDEE7 || 0xDF4B ≤ a && a ≤ 0xDFB8 || 0xE3B0 ≤ a && a ≤ 0xE431 ||
      0x9BDD ≤ a && a ≤ 0x9BF5) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hy := bgSize_y_lt (bgPre_ram ram)
  simp only [bgRam, bgY, bgFootRam] at hhc hhh hfc hfa hpe hfoot
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 1200)).run ⟨⟨0xDC64, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary bgImpede hrun [hI, bgSize_pc] until 57226
    calls [bgPre_go_call, bgSize_call, footCheck_impede_call]
    exact finish (exact_finish bgImpede)
summary_interface bgImpede
summary_regs bgImpede

/-! ## The stack on the ordinary exits -/

/-- The only unreturned nested call in the small foot summary is the pipe-entry stop. -/
theorem chkFoot_stack_exit (a sp : UInt8) (ram prg : UInt16 → UInt8) :
    chkFoot_s a sp ram prg =
      (bif chkFoot_pc a ram prg == 0xDEFA then sp + 254 else sp) := by
  simp only [chkFoot_s, chkFoot_pc]
  bv_decide

/-- Either ordinary exit restores the input S; no numerical stack bound is needed. -/
theorem chkFoot_stack_normal (a sp : UInt8) (ram prg : UInt16 → UInt8)
    (h : chkFoot_pc a ram prg = 0xDD5E ∨ chkFoot_pc a ram prg = 0xDF8A) :
    chkFoot_s a sp ram prg = sp := by
  rw [chkFoot_stack_exit]
  rcases h with h | h <;> rw [h] <;> rfl

/-- Readable stack effect under the actual four climbability thresholds. -/
theorem chkFoot_stack_class (a sp : UInt8) (ram prg : UInt16 → UInt8)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6) :
    chkFoot_s a sp ram prg =
      (bif footGround a ram && ram 4 < 5 && pipeDown ram then sp + 254 else sp) := by
  rcases htbl with ⟨h0,h1,h2,h3⟩
  simp only [chkFoot_s, chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, chkFoot_c5, chkFoot_c6, chkFoot_c7, chkFoot_c8, chkFoot_c9, chkFoot_c10, chkFoot_c11, chkFoot_c12, chkFoot_c13, chkFoot_c14, chkFoot_c15, chkFoot_c16, chkFoot_c17, footGround, pipeDown, climbable, climbExt, bne]
  fun_congr
  bv_decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- Relate the final PC and S fields, keeping headPart RAM and all execution opaque. -/
theorem footCheck_stack_normal (y sp : UInt8) (ram prg : UInt16 → UInt8)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hpc : footCheck_pc y sp ram prg = 0xDD5E ∨ footCheck_pc y sp ram prg = 0xDF8A) :
    footCheck_s y sp ram prg = sp := by
  have hs := fun a s r => chkFoot_stack_class a s r prg htbl
  simp only [footCheck_s, hs]
  simp only [footCheck_pc, footCheck_c0, footCheck_c1, footCheck_c2, footCheck_c3, footCheck_c4, footCheck_c5, footCheck_c6, footCheck_c7, footCheck_c8, footCheck_c9, footCheck_c10, footCheck_c11, footCheck_c12, footAxe, footGround, pipeDown, bne] at hpc ⊢
  bv_decide

/-- This discharges the frame's hfs premise using only an existing code hypothesis
and its selected foot-check exit. No new reachability or stack bound is required. -/
theorem background_stack_normal (sp : UInt8) (ram prg : UInt16 → UInt8)
    (hcode : CodeAt prg 0x5F96 climbTilesCode)
    (hpc : footCheck_pc (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg = 0xDD5E ∨
      footCheck_pc (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg = 0xDF8A) :
    bgSide_s sp ram prg = sp ∧ bgImpede_s sp ram prg = sp := by
  have htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6 := by
    simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at hcode
    exact ⟨hcode.1, hcode.2.1, hcode.2.2.1, hcode.2.2.2.1⟩
  have h := footCheck_stack_normal (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg htbl hpc
  constructor
  · simpa only [bgSide_s, bgY, bgRam, bgSize_s_eq, bgPre_s_eq] using h
  · simpa only [bgImpede_s, bgY, bgRam, bgSize_s_eq, bgPre_s_eq] using h

end Smb.Routine
