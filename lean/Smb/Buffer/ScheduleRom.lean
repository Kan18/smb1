import Smb.Data.ProofRom
import Smb.Buffer.Schedule
import Smb.Routine.Common

/-!
# The ROM behind `Schedule`'s automata

* **The parser.** `AreaParserTaskHandler`'s code and its `AreaParserTasks` table are the ROM's, and the table sends
  exactly the task indices `taskRenders` names to `RenderAreaGraphics` (`parser_table_renders`).
* **A floatey slot's routine.** Run from `FloateyNumbersRoutine`'s entry for slot `x`, the four cases of
  `slotCall`: a zero control byte returns with nothing changed; a zero timer clears the control byte and returns;
  any other timer is decremented, and it reaches `LoadNumTiles`, which calls `AddToScore`, exactly when the timer
  read was `$2B` (`floatey_idle`, `floatey_expire`, `floatey_tick`, `floatey_award`).
* **Block replacement.** `BlockObjMT_Updater` writes nothing but `ObjectOffset` when buffer 1 already has a record
  (`$0301` nonzero), so a block object's delayed metatile can only open a window (`blockUpdater_busy`).
* **The game timer.** `ResGTCtrl`, the only path to the timer's print, sets `GameTimerCtrlTimer` to `$18` first
  (`resGTCtrl_in_rom`).
-/
namespace Smb.Buffer.Schedule
open Smb Smb.Routine

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

/-! ## The parser -/

/-- `AreaParserTaskHandler` (`$92B0`) and `AreaParserTasks` (`$92C8`): the dispatch through `JumpEngine` and its
8-entry table. -/
def parserCode : List UInt8 :=
  smbPrg% 0x92B0 43

theorem parserCode_in_rom : CodeAt rom 0x12b0 parserCode := codeAt_of_matches _ _ _ (by native_decide)

/-- Task `i`'s routine is `RenderAreaGraphics` (`$88AE`) exactly when `taskRenders i`; the others are
`IncrementColumnPos` (`$92DB`) and `AreaParserCore` (`$93FC`), which don't touch the buffers' control. -/
theorem parser_table_renders : (List.range 8).all (fun i =>
    let lo := rom (0x92CB + 2 * UInt16.ofNat i)
    let hi := rom (0x92CC + 2 * UInt16.ofNat i)
    ((lo == 0xAE && hi == 0x88) == taskRenders (UInt8.ofNat i)) &&
      ((lo == 0xAE && hi == 0x88) || (lo == 0xDB && hi == 0x92) || (lo == 0xFC && hi == 0x93))) = true := by
  native_decide

/-! ## A floatey-number slot -/

/-- `FloateyNumbersRoutine` from its entry (`$84C3`) through `jsr AddToScore`. -/
def floateyCode : List UInt8 :=
  smbPrg% 0x84C3 61

theorem floateyCode_in_rom : CodeAt rom 0x04c3 floateyCode := codeAt_of_matches _ _ _ (by native_decide)

/-- Its control byte and timer for slot `x`. -/
abbrev ctl (x : UInt8) : UInt16 := 0x110 + x.toUInt16
abbrev tmr (x : UInt8) : UInt16 := 0x12C + x.toUInt16

/-- The slot's cells never alias each other or the lives counter (`$075A`) and sound queue (`$FE`). -/
theorem alias_facts (x : UInt8) (hx : x ≤ 5) :
    (0x12C + x.toUInt16 == 0x110 + x.toUInt16) = false ∧ (0x110 + x.toUInt16 == 0x12C + x.toUInt16) = false ∧
    ((0x75A : UInt16) == 0x12C + x.toUInt16) = false ∧ ((0x75A : UInt16) == 0x110 + x.toUInt16) = false ∧
    ((0xFE : UInt16) == 0x12C + x.toUInt16) = false := by
  revert hx; bv_decide

set_option maxHeartbeats 4000000 in
/-- A zero control byte: back at `EndExitOne`'s `rts` (`$8486`), nothing written. -/
theorem floatey_idle (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x04c3 floateyCode) (hI : p &&& 4 ≠ 0) (hx : x ≤ 5) (hc : ram (ctl x) = 0) :
    let t := ((CPU.runTo (σ := Plain) 0x8486 20).run ⟨⟨0x84C3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.bad = false ∧ t.regs.pc = 0x8486 ∧ t.ram = ram := by
  dsimp only
  simp only [CodeAt, floateyCode, UInt16.reduceAdd] at hcode
  generalize hr : ((CPU.runTo (σ := Plain) 0x8486 20).run ⟨⟨0x84C3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  have ha : (0x110 + x.toUInt16) &&& 0x7ff = 0x110 + x.toUInt16 := by revert hx; bv_decide
  simp only [ctl] at hc
  sym_run hr [hcode, hi, ha, hc]
  all_goals
    intros
    clear hcode hi
    simp_all
    try bv_decide

set_option maxHeartbeats 8000000 in
/-- A zero timer: the control byte is cleared, and the routine returns at `$84DA`. -/
theorem floatey_expire (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x04c3 floateyCode) (hI : p &&& 4 ≠ 0) (hx : x ≤ 5) (hc : ram (ctl x) ≠ 0)
    (ht : ram (tmr x) = 0) :
    let t := ((CPU.runTo (σ := Plain) 0x84DA 20).run ⟨⟨0x84C3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.bad = false ∧ t.regs.pc = 0x84DA ∧ t.ram (ctl x) = 0 ∧ ∀ i : UInt16, i ≠ ctl x → t.ram i = ram i := by
  dsimp only
  simp only [CodeAt, floateyCode, UInt16.reduceAdd] at hcode
  generalize hr : ((CPU.runTo (σ := Plain) 0x84DA 20).run ⟨⟨0x84C3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  have ha : (0x110 + x.toUInt16) &&& 0x7ff = 0x110 + x.toUInt16 := by revert hx; bv_decide
  have hb : (0x12C + x.toUInt16) &&& 0x7ff = 0x12C + x.toUInt16 := by revert hx; bv_decide
  have hn := alias_facts x hx
  have hc' : (ram (0x110 + x.toUInt16) == 0) = false := by simpa [ctl] using hc
  simp only [tmr] at ht
  sym_run hr [hcode, hi, ha, hb, hc', ht, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2]
  all_goals
    intros
    clear hcode hi
    simp_all
    try bv_decide

set_option maxHeartbeats 8000000 in
/-- Any other timer not at `$2B`: decremented, and on to `ChkTallEnemy` (`$8500`) without awarding; only the
timer and the control byte (clamped to `$0B`) change. -/
theorem floatey_tick (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x04c3 floateyCode) (hI : p &&& 4 ≠ 0) (hx : x ≤ 5) (hc : ram (ctl x) ≠ 0)
    (ht : ram (tmr x) ≠ 0) (ht2 : ram (tmr x) ≠ 0x2B) :
    let t := ((CPU.runTo (σ := Plain) 0x8500 20).run ⟨⟨0x84C3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.bad = false ∧ t.regs.pc = 0x8500 ∧ t.ram (tmr x) = ram (tmr x) - 1 ∧
      ∀ i : UInt16, i ≠ ctl x → i ≠ tmr x → t.ram i = ram i := by
  dsimp only
  simp only [CodeAt, floateyCode, UInt16.reduceAdd] at hcode
  generalize hr : ((CPU.runTo (σ := Plain) 0x8500 20).run ⟨⟨0x84C3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  have ha : (0x110 + x.toUInt16) &&& 0x7ff = 0x110 + x.toUInt16 := by revert hx; bv_decide
  have hb : (0x12C + x.toUInt16) &&& 0x7ff = 0x12C + x.toUInt16 := by revert hx; bv_decide
  have hn := alias_facts x hx
  have hc' : (ram (0x110 + x.toUInt16) == 0) = false := by simpa [ctl] using hc
  have ht' : (ram (0x12C + x.toUInt16) == 0) = false := by simpa [tmr] using ht
  have ht2' : (ram (0x12C + x.toUInt16) == 0x2B) = false := by simpa [tmr] using ht2
  sym_run hr [hcode, hi, ha, hb, hc', ht', ht2', hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2]
  all_goals
    intros
    clear hcode hi
    simp_all
    try bv_decide

set_option maxHeartbeats 8000000 in
/-- A timer at `$2B`: decremented to `$2A`, and on to `LoadNumTiles` (`$84ED`), whose straight-line code ends in
`jsr AddToScore`. -/
theorem floatey_award (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x04c3 floateyCode) (hI : p &&& 4 ≠ 0) (hx : x ≤ 5) (hc : ram (ctl x) ≠ 0)
    (ht : ram (tmr x) = 0x2B) :
    let t := ((CPU.runTo (σ := Plain) 0x84ED 24).run ⟨⟨0x84C3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.bad = false ∧ t.regs.pc = 0x84ED ∧ t.ram (tmr x) = 0x2A := by
  dsimp only
  simp only [CodeAt, floateyCode, UInt16.reduceAdd] at hcode
  generalize hr : ((CPU.runTo (σ := Plain) 0x84ED 24).run ⟨⟨0x84C3, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  have ha : (0x110 + x.toUInt16) &&& 0x7ff = 0x110 + x.toUInt16 := by revert hx; bv_decide
  have hb : (0x12C + x.toUInt16) &&& 0x7ff = 0x12C + x.toUInt16 := by revert hx; bv_decide
  have hn := alias_facts x hx
  have hc' : (ram (0x110 + x.toUInt16) == 0) = false := by simpa [ctl] using hc
  simp only [tmr] at ht
  sym_run hr [hcode, hi, ha, hb, hc', ht, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2]
  all_goals
    intros
    clear hcode hi
    simp_all
    try bv_decide

/-! ## Block replacement and the game timer -/

/-- `BlockObjMT_Updater` (`$BED4`). -/
def blockUpdaterCode : List UInt8 :=
  smbPrg% 0xBED4 46

theorem blockUpdaterCode_in_rom : CodeAt rom 0x3ed4 blockUpdaterCode := codeAt_of_matches _ _ _ (by native_decide)

set_option maxHeartbeats 4000000 in
/-- With a record already in buffer 1, the updater reaches its `rts` (`$BF01`) having written only `ObjectOffset`. -/
theorem blockUpdater_busy (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x3ed4 blockUpdaterCode) (hI : p &&& 4 ≠ 0) (hb : ram 0x301 ≠ 0) :
    let t := ((CPU.runTo (σ := Plain) 0xBF01 24).run ⟨⟨0xBED4, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.bad = false ∧ t.regs.pc = 0xBF01 ∧ ∀ i : UInt16, i ≠ 8 → t.ram i = ram i := by
  dsimp only
  simp only [CodeAt, blockUpdaterCode, UInt16.reduceAdd] at hcode
  generalize hr : ((CPU.runTo (σ := Plain) 0xBF01 24).run ⟨⟨0xBED4, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  have hb' : (ram 0x301 == 0) = false := by simpa using hb
  sym_run hr [hcode, hi, hb']
  all_goals
    intros
    clear hcode hi
    simp_all
    try bv_decide

/-- `ResGTCtrl` (`$B786`): `GameTimerCtrlTimer` := `$18`, then the digit math and the print. -/
def resGTCtrlCode : List UInt8 :=
  smbPrg% 0xB786 20

theorem resGTCtrl_in_rom : CodeAt rom 0x3786 resGTCtrlCode := codeAt_of_matches _ _ _ (by native_decide)

end Smb.Buffer.Schedule
