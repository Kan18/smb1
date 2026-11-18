import Smb.Data.ProofRom
import Smb.Summary
import Smb.Buffer.Addr
import Smb.Buffer.StatusRecord
import Smb.Routine.Common

/-!
# Relocation: the attribute renderer (`RenderAttributeTables`, `$896A`)

The parser's last task of a column set writes the attribute record into VRAM buffer 2 from `$0341 + v`, with
`v = $0340` read as is: seven 4-byte entries at `$0341 + (v + 4r)` (8-bit index), each an attribute-table address
(`$23` or `$27`, then a low byte), length 1, and `AttributeBuffer[r]`, which it then clears; a terminator at
`$0341 + (v + 28)`; and `$0340 := v + 28`. It ends in `SetVRAMCtrl`, setting `$0773` to 6. Nothing bounds `v`.
-/
namespace Smb.Buffer
open Smb Smb.Routine

def renderAttributeCode : List UInt8 :=
  smbPrg% 0x896A 83

/-- `SetVRAMCtrl`: `lda #6`, `sta $0773`, `rts`. -/
def setVramCtrlCode : List UInt8 := smbPrg% 0x89BD 6

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem renderAttributeCode_in_rom : CodeAt rom 0x096a renderAttributeCode :=
  codeAt_of_matches _ _ _ (by native_decide)
theorem setVramCtrlCode_in_rom : CodeAt rom 0x09bd setVramCtrlCode := codeAt_of_matches _ _ _ (by native_decide)

set_option linter.unusedVariables false

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 40000 in
sym_theorem renderAttribute_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x896A ≤ a && a ≤ 0x89C2) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x096a renderAttributeCode) (hsvc : CodeAt prg 0x09bd setVramCtrlCode)
    (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0x896A, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, renderAttributeCode, setVramCtrlCode, UInt16.reduceAdd] at hcode hsvc
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0x896A, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ratt hrun [hcode, hsvc, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero, rom_idx_not_ram]
      until [0x89C2]
    exact finish (clear hcode hsvc; exact_finish ratt)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 80000000 in
summary_interface ratt
summary_regs ratt

/-! ## The record, stated cleanly -/

/-- RAM with a record's `fields` laid out from buffer 2's logical index `v`, at `$0341 + v`. -/
def record2 (r : UInt16 → UInt8) (v : UInt8) : List UInt8 → UInt16 → (UInt16 → UInt8)
  | [], _ => r
  | b :: bs, k => record2 (put r (0x341 + v.toUInt16 + k) b) v bs (k + 1)

/-- The attribute table's address high byte: `$23` or `$27`, the page of the column four columns back. -/
def attrHi (lo hi : UInt8) : UInt8 := ((bif (lo &&& 0x1F) < 4 then hi ^^^ 4 else hi) &&& 4) ||| 0x23

/-- The low byte before the first row: `$C0` plus the column's attribute column. -/
def attrBase (lo : UInt8) : UInt8 :=
  let t := ((lo &&& 0x1F) - 4) &&& 0x1F
  (t >>> (2 : UInt8)) + (0xC0 : UInt8) + ((t >>> (1 : UInt8)) &&& (1 : UInt8))

/-- Seven entries, one per attribute row: address high, low (moving down a row, 8 bytes, each time), length 1,
and `AttributeBuffer[r]`; then a terminator. -/
def rattFields (ram : UInt16 → UInt8) : List UInt8 :=
  let hi := attrHi (ram 0x721) (ram 0x720)
  let b := attrBase (ram 0x721)
  [hi, b + 8, 1, ram 0x3F9, hi, b + 16, 1, ram 0x3FA, hi, b + 24, 1, ram 0x3FB, hi, b + 32, 1, ram 0x3FC,
   hi, b + 40, 1, ram 0x3FD, hi, b + 48, 1, ram 0x3FE, hi, b + 56, 1, ram 0x3FF, 0]

set_option maxHeartbeats 40000000 in
/-- For an offset that keeps the record clear of `AttributeBuffer`, the attribute renderer lays down its record at
`$0341 + v`, and away from its scratch bytes, the offset, the address control (set to 6) and `AttributeBuffer`
(which it clears), nothing else. -/
theorem ratt_ram_record (p : UInt8) (ram : UInt16 → UInt8) (hv : ram 0x340 ≤ 0x9B) (i : UInt16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h340 : i ≠ 0x340) (h773 : i ≠ 0x773) (hab : i < 0x3F9 ∨ 0x3FF < i) :
    ratt_ram p ram i = record2 ram (ram 0x340) (rattFields ram) 0 i := by
  simp only [ratt_ram, ratt_c0, record2, rattFields, attrHi, attrBase, put, UInt16.reduceAdd]
  generalize ram 0x340 = v at *
  generalize ram 0x720 = hi at *
  generalize ram 0x721 = lo at *
  bv_decide

theorem ratt_ram_offset (p : UInt8) (ram : UInt16 → UInt8) : ratt_ram p ram 0x340 = ram 0x340 + 28 := by
  simp only [ratt_ram, ratt_c0]
  bv_decide

end Smb.Buffer
