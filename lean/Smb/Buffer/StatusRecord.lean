import Smb.Data.ProofRom
import Smb.Summary
import Smb.Buffer.Addr
import Smb.Routine.Common

/-!
# The status-number record (`OutputNumbers`, `$8F11`)

`OutputNumbers` prints one number from the status bar into VRAM buffer 1, appended at the current offset
`o = $0300`. With selector `n = (A + 1) &&& $0F`, below 6, it writes the record

* `$0301 + o`: PPU address high, `$20` (`$22` for selector 0, the title's top score)
* `$0302 + o`, `$0303 + o`: PPU address low and digit count, from the table at `$8EF4`
* `$0304 + (o + i)`, for each digit `i`: the digit `$07D7 + d0 + i`, with the 8-bit index wrapping
* `$0304 + (o + len)`: a terminator

and sets `$0300` to `o + len + 3`. It also leaves `o` in `$02`, 0 in `$03`, and pushes and pops the selector.
Selectors 6 and up return at once. Nothing bounds `o`: these are the stores an overflowing offset makes too.
-/
namespace Smb.Buffer
open Smb Smb.Routine

def outputNumbersCode : List UInt8 :=
  smbPrg% 0x8F11 78

/-- `StatusBarData`: address low byte and digit count per selector. -/
def statusData : List UInt8 := smbPrg% 0x8EF4 12

/-- `StatusBarOffset`: one past each number's last digit in `DisplayDigits` (`$07D7`). -/
def statusOffset : List UInt8 := smbPrg% 0x8F00 6

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem outputNumbersCode_in_rom : CodeAt rom 0x0f11 outputNumbersCode := codeAt_of_matches _ _ _ (by native_decide)
theorem statusData_in_rom : CodeAt rom 0x0ef4 statusData := codeAt_of_matches _ _ _ (by native_decide)
theorem statusOffset_in_rom : CodeAt rom 0x0f00 statusOffset := codeAt_of_matches _ _ _ (by native_decide)

/-- A store, as the machine makes it. -/
def wr (r : UInt16 → UInt8) (a : UInt16) (b : UInt8) : UInt16 → UInt8 :=
  fun i => bif Plain.inRam a && i == a &&& 0x7FF then b else r i

set_option linter.unusedVariables false

/-! ## Machine-level summaries, one per selector

Each starts just after `and #$0F`, with `A` the selector, and runs to the `rts` at `$8F5E`. -/

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem status0_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8F16 ≤ a && a ≤ 0x8F5E) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hdata : CodeAt prg 0x0ef4 statusData)
    (hoff : CodeAt prg 0x0f00 statusOffset) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 0, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, outputNumbersCode, statusData, statusOffset, UInt16.reduceAdd] at hcode hdata hoff
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 0, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary st0 hrun [hcode, hdata, hoff, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x8F5E]
    exact finish (clear hcode hdata hoff; exact_finish st0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface st0
summary_regs st0

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem status1_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8F16 ≤ a && a ≤ 0x8F5E) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hdata : CodeAt prg 0x0ef4 statusData)
    (hoff : CodeAt prg 0x0f00 statusOffset) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 1, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, outputNumbersCode, statusData, statusOffset, UInt16.reduceAdd] at hcode hdata hoff
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 1, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary st1 hrun [hcode, hdata, hoff, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x8F5E]
    exact finish (clear hcode hdata hoff; exact_finish st1)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface st1
summary_regs st1

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem status2_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8F16 ≤ a && a ≤ 0x8F5E) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hdata : CodeAt prg 0x0ef4 statusData)
    (hoff : CodeAt prg 0x0f00 statusOffset) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 2, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, outputNumbersCode, statusData, statusOffset, UInt16.reduceAdd] at hcode hdata hoff
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 2, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary st2 hrun [hcode, hdata, hoff, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x8F5E]
    exact finish (clear hcode hdata hoff; exact_finish st2)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface st2
summary_regs st2

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem status3_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8F16 ≤ a && a ≤ 0x8F5E) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hdata : CodeAt prg 0x0ef4 statusData)
    (hoff : CodeAt prg 0x0f00 statusOffset) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 3, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, outputNumbersCode, statusData, statusOffset, UInt16.reduceAdd] at hcode hdata hoff
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 3, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary st3 hrun [hcode, hdata, hoff, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x8F5E]
    exact finish (clear hcode hdata hoff; exact_finish st3)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface st3
summary_regs st3

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem status4_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8F16 ≤ a && a ≤ 0x8F5E) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hdata : CodeAt prg 0x0ef4 statusData)
    (hoff : CodeAt prg 0x0f00 statusOffset) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 4, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, outputNumbersCode, statusData, statusOffset, UInt16.reduceAdd] at hcode hdata hoff
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 4, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary st4 hrun [hcode, hdata, hoff, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x8F5E]
    exact finish (clear hcode hdata hoff; exact_finish st4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface st4
summary_regs st4

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem status5_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8F16 ≤ a && a ≤ 0x8F5E) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hdata : CodeAt prg 0x0ef4 statusData)
    (hoff : CodeAt prg 0x0f00 statusOffset) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 5, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, outputNumbersCode, statusData, statusOffset, UInt16.reduceAdd] at hcode hdata hoff
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8F16, 5, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary st5 hrun [hcode, hdata, hoff, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x8F5E]
    exact finish (clear hcode hdata hoff; exact_finish st5)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface st5
summary_regs st5

/-! ## The record, stated cleanly -/

/-- RAM with `b` stored at `a`. -/
def put (r : UInt16 → UInt8) (a : UInt16) (b : UInt8) : UInt16 → UInt8 := fun i => bif i == a then b else r i

/-- RAM with a record's `fields` laid out from buffer 1's logical index `o`, at `$0301 + o`. -/
def record (r : UInt16 → UInt8) (o : UInt8) : List UInt8 → UInt16 → (UInt16 → UInt8)
  | [], _ => r
  | b :: bs, k => record (put r (0x301 + o.toUInt16 + k) b) o bs (k + 1)

/-- Selector 0, the top score on the title screen: address `$22F0`, 6 digits from `$07D7`, and a terminator. -/
def st0Fields (ram : UInt16 → UInt8) : List UInt8 := [0x22, 0xf0, 0x06, ram 0x7D7, ram 0x7D8, ram 0x7D9, ram 0x7DA, ram 0x7DB, ram 0x7DC, 0x00]

set_option maxHeartbeats 4000000 in
/-- Away from the stack byte and the scratch bytes `$02`/`$03`, selector 0 lays down its record at the offset
and nothing else, for any offset that leaves room for it. -/
theorem st0_ram_record (sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 246) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (h2 : i ≠ 2) (h3 : i ≠ 3) (h300 : i ≠ 0x300) :
    st0_ram sp ram i = record ram (ram 0x300) (st0Fields ram) 0 i := by
  simp only [st0_ram, record, st0Fields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 0x7D7 = d0 at *
  generalize ram 0x7D8 = d1 at *
  generalize ram 0x7D9 = d2 at *
  generalize ram 0x7DA = d3 at *
  generalize ram 0x7DB = d4 at *
  generalize ram 0x7DC = d5 at *
  bv_decide

theorem st0_ram_offset (sp : UInt8) (ram : UInt16 → UInt8) : st0_ram sp ram 0x300 = ram 0x300 + 9 := by
  simp only [st0_ram]
  bv_decide

/-- Selector 1, the score: address `$2062`, 6 digits from `$07DD`, and a terminator. -/
def st1Fields (ram : UInt16 → UInt8) : List UInt8 := [0x20, 0x62, 0x06, ram 0x7DD, ram 0x7DE, ram 0x7DF, ram 0x7E0, ram 0x7E1, ram 0x7E2, 0x00]

set_option maxHeartbeats 4000000 in
/-- Away from the stack byte and the scratch bytes `$02`/`$03`, selector 1 lays down its record at the offset
and nothing else, for any offset that leaves room for it. -/
theorem st1_ram_record (sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 246) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (h2 : i ≠ 2) (h3 : i ≠ 3) (h300 : i ≠ 0x300) :
    st1_ram sp ram i = record ram (ram 0x300) (st1Fields ram) 0 i := by
  simp only [st1_ram, record, st1Fields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 0x7DD = d0 at *
  generalize ram 0x7DE = d1 at *
  generalize ram 0x7DF = d2 at *
  generalize ram 0x7E0 = d3 at *
  generalize ram 0x7E1 = d4 at *
  generalize ram 0x7E2 = d5 at *
  bv_decide

theorem st1_ram_offset (sp : UInt8) (ram : UInt16 → UInt8) : st1_ram sp ram 0x300 = ram 0x300 + 9 := by
  simp only [st1_ram]
  bv_decide

/-- Selector 2, the score: address `$2062`, 6 digits from `$07E3`, and a terminator. -/
def st2Fields (ram : UInt16 → UInt8) : List UInt8 := [0x20, 0x62, 0x06, ram 0x7E3, ram 0x7E4, ram 0x7E5, ram 0x7E6, ram 0x7E7, ram 0x7E8, 0x00]

set_option maxHeartbeats 4000000 in
/-- Away from the stack byte and the scratch bytes `$02`/`$03`, selector 2 lays down its record at the offset
and nothing else, for any offset that leaves room for it. -/
theorem st2_ram_record (sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 246) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (h2 : i ≠ 2) (h3 : i ≠ 3) (h300 : i ≠ 0x300) :
    st2_ram sp ram i = record ram (ram 0x300) (st2Fields ram) 0 i := by
  simp only [st2_ram, record, st2Fields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 0x7E3 = d0 at *
  generalize ram 0x7E4 = d1 at *
  generalize ram 0x7E5 = d2 at *
  generalize ram 0x7E6 = d3 at *
  generalize ram 0x7E7 = d4 at *
  generalize ram 0x7E8 = d5 at *
  bv_decide

theorem st2_ram_offset (sp : UInt8) (ram : UInt16 → UInt8) : st2_ram sp ram 0x300 = ram 0x300 + 9 := by
  simp only [st2_ram]
  bv_decide

/-- Selector 3, the coin count: address `$206D`, 2 digits from `$07ED`, and a terminator. -/
def st3Fields (ram : UInt16 → UInt8) : List UInt8 := [0x20, 0x6d, 0x02, ram 0x7ED, ram 0x7EE, 0x00]

set_option maxHeartbeats 4000000 in
/-- Away from the stack byte and the scratch bytes `$02`/`$03`, selector 3 lays down its record at the offset
and nothing else, for any offset that leaves room for it. -/
theorem st3_ram_record (sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 250) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (h2 : i ≠ 2) (h3 : i ≠ 3) (h300 : i ≠ 0x300) :
    st3_ram sp ram i = record ram (ram 0x300) (st3Fields ram) 0 i := by
  simp only [st3_ram, record, st3Fields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 0x7ED = d0 at *
  generalize ram 0x7EE = d1 at *
  bv_decide

theorem st3_ram_offset (sp : UInt8) (ram : UInt16 → UInt8) : st3_ram sp ram 0x300 = ram 0x300 + 5 := by
  simp only [st3_ram]
  bv_decide

/-- Selector 4, the coin count: address `$206D`, 2 digits from `$07F3`, and a terminator. -/
def st4Fields (ram : UInt16 → UInt8) : List UInt8 := [0x20, 0x6d, 0x02, ram 0x7F3, ram 0x7F4, 0x00]

set_option maxHeartbeats 4000000 in
/-- Away from the stack byte and the scratch bytes `$02`/`$03`, selector 4 lays down its record at the offset
and nothing else, for any offset that leaves room for it. -/
theorem st4_ram_record (sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 250) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (h2 : i ≠ 2) (h3 : i ≠ 3) (h300 : i ≠ 0x300) :
    st4_ram sp ram i = record ram (ram 0x300) (st4Fields ram) 0 i := by
  simp only [st4_ram, record, st4Fields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 0x7F3 = d0 at *
  generalize ram 0x7F4 = d1 at *
  bv_decide

theorem st4_ram_offset (sp : UInt8) (ram : UInt16 → UInt8) : st4_ram sp ram 0x300 = ram 0x300 + 5 := by
  simp only [st4_ram]
  bv_decide

/-- Selector 5, the game timer: address `$207A`, 3 digits from `$07F8`, and a terminator. -/
def st5Fields (ram : UInt16 → UInt8) : List UInt8 := [0x20, 0x7a, 0x03, ram 0x7F8, ram 0x7F9, ram 0x7FA, 0x00]

set_option maxHeartbeats 4000000 in
/-- Away from the stack byte and the scratch bytes `$02`/`$03`, selector 5 lays down its record at the offset
and nothing else, for any offset that leaves room for it. -/
theorem st5_ram_record (sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 249) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (h2 : i ≠ 2) (h3 : i ≠ 3) (h300 : i ≠ 0x300) :
    st5_ram sp ram i = record ram (ram 0x300) (st5Fields ram) 0 i := by
  simp only [st5_ram, record, st5Fields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 0x7F8 = d0 at *
  generalize ram 0x7F9 = d1 at *
  generalize ram 0x7FA = d2 at *
  bv_decide

theorem st5_ram_offset (sp : UInt8) (ram : UInt16 → UInt8) : st5_ram sp ram 0x300 = ram 0x300 + 6 := by
  simp only [st5_ram]
  bv_decide

end Smb.Buffer
