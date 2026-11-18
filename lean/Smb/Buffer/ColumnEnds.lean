import Smb.Data.ProofRom
import Smb.Summary
import Smb.Buffer.Addr
import Smb.Buffer.StatusRecord
import Smb.Buffer.RenderAttribute
import Smb.Routine.Common

/-!
# The column record's ends

`RenderAreaGraphics` (`$88AE`) opens the column record before its 13 rows (`Renderer.RowCompose`, from `$88D0`)
and closes it after them (from `$8943`):

* the header, with `v = $0340`: `CurrentNTAddr` high at `$0341 + v`, low at `$0342 + v`, `$9A` (26 tiles, by
  columns) at `$0343 + v`; it saves `v` in `$00` for the rows, and starts `$04` and `X` at 0;
* the tail, with `q = $00` after the rows (`v + 26`): a terminator at `$0341 + (q + 3)`, `$0340 := q + 3`, the
  next column's `CurrentNTAddr`, and `$0773 := 6`.
-/
namespace Smb.Buffer
open Smb Smb.Routine

def columnHeadCode : List UInt8 := smbPrg% 0x88AE 34
def columnTailCode : List UInt8 := smbPrg% 0x8943 39

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem columnHeadCode_in_rom : CodeAt rom 0x08ae columnHeadCode := codeAt_of_matches _ _ _ (by native_decide)
theorem columnTailCode_in_rom : CodeAt rom 0x0943 columnTailCode := codeAt_of_matches _ _ _ (by native_decide)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem columnHead_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x88AE ≤ a && a ≤ 0x88CF) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x08ae columnHeadCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 50)).run ⟨⟨0x88AE, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, columnHeadCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 50)).run ⟨⟨0x88AE, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary chead hrun [hcode, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x88D0]
    exact finish (clear hcode; exact_finish chead)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface chead
summary_regs chead

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem columnTail_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8943 ≤ a && a ≤ 0x8969 || 0x89BD ≤ a && a ≤ 0x89C2) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0943 columnTailCode) (hsvc : CodeAt prg 0x09bd setVramCtrlCode)
    (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 50)).run ⟨⟨0x8943, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, columnTailCode, setVramCtrlCode, UInt16.reduceAdd] at hcode hsvc
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 50)).run ⟨⟨0x8943, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ctail hrun [hcode, hsvc, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x89C2]
    exact finish (clear hcode hsvc; exact_finish ctail)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface ctail
summary_regs ctail

set_option maxHeartbeats 8000000 in
/-- The header: away from the scratch bytes `$00`, `$04`, `$05`, the column record opens with `CurrentNTAddr`
high and low and `$9A`, from `$0341 + v`. -/
theorem chead_ram_record (ram : UInt16 → UInt8) (hv : ram 0x340 ≤ 252) (i : UInt16) (h0 : i ≠ 0) (h4 : i ≠ 4)
    (h5 : i ≠ 5) : chead_ram ram i = record2 ram (ram 0x340) [ram 0x720, ram 0x721, 0x9A] 0 i := by
  simp only [chead_ram, record2, put, UInt16.reduceAdd]
  generalize ram 0x340 = v at *
  generalize ram 0x720 = hi at *
  generalize ram 0x721 = lo at *
  bv_decide

theorem chead_saves_offset (ram : UInt16 → UInt8) : chead_ram ram 0 = ram 0x340 := by
  simp only [chead_ram]
  bv_decide

/-- The tail: with `q = $00` after the rows, the terminator goes to `$0341 + (q + 3)` and the offset becomes
`q + 3`. -/
theorem ctail_terminator (ram : UInt16 → UInt8) :
    ctail_ram ram ((0x341 + (ram 0 + 3).toUInt16) &&& 0x7FF) = 0 ∧ ctail_ram ram 0x340 = ram 0 + 3 := by
  simp only [ctail_ram, ctail_c0]
  generalize ram 0 = q
  constructor <;> bv_decide

end Smb.Buffer
