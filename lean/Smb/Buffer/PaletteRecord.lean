import Smb.Data.ProofRom
import Smb.Summary
import Smb.Buffer.Addr
import Smb.Buffer.StatusRecord
import Smb.Routine.Common

/-!
# The palette records (`GetPlayerColors`, `$85F1`; `ColorRotation`, `$89E1`)

Both append a one-entry sprite or background palette write to VRAM buffer 1, of length 4, and move the offset
`o = $0300` on by 7, so the next record overwrites the terminator.

* `GetPlayerColors` writes `$3F $10 $04`, the background color, three player colors and a terminator. The colors
  are Mario's, Luigi's or fiery (`$0753`, `$0756`), and the background color is `BackgroundColors` indexed by
  `$0744`, or by the area type `$074E` when that's 0. Neither index is bounded here, and nothing guards `o`.
* `ColorRotation` writes on every eighth frame (`$09 &&& 7 = 0`), and only while `o < $31`: `$3F $0C $04`, the
  area's background palette 3 (`$074E`) with its second color replaced by the rotating one (`$06D4`), and a
  terminator. It also advances `$06D4`, wrapping at 6.
-/
namespace Smb.Buffer
open Smb Smb.Routine

def playerColorsCode : List UInt8 :=
  smbPrg% 0x85F1 82

/-- `BackgroundColors` (8 bytes) and `PlayerColors` (12), which follow it. -/
def colorTables : List UInt8 :=
  smbPrg% 0x85CF 20

def colorRotationCode : List UInt8 :=
  smbPrg% 0x89E1 88

/-- `ColorRotatePalette` (6), `BlankPalette` (8) and `Palette3Data` (16), in ROM order. -/
def rotationTables : List UInt8 :=
  smbPrg% 0x89C3 30

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem playerColorsCode_in_rom : CodeAt rom 0x05f1 playerColorsCode := codeAt_of_matches _ _ _ (by native_decide)
theorem colorTables_in_rom : CodeAt rom 0x05cf colorTables := codeAt_of_matches _ _ _ (by native_decide)
theorem colorRotationCode_in_rom : CodeAt rom 0x09e1 colorRotationCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rotationTables_in_rom : CodeAt rom 0x09c3 rotationTables := codeAt_of_matches _ _ _ (by native_decide)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem playerColors_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x85F1 ≤ a && a ≤ 0x8642) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x05f1 playerColorsCode) (htab : CodeAt prg 0x05cf colorTables)
    (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x85F1, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, playerColorsCode, colorTables, UInt16.reduceAdd] at hcode htab
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x85F1, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary pcol hrun [hcode, htab, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero, rom_idx_not_ram] until [0x8642]
    exact finish (clear hcode htab; exact_finish pcol)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface pcol
summary_regs pcol

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem colorRotation_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x89E1 ≤ a && a ≤ 0x8A38) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x09e1 colorRotationCode) (htab : CodeAt prg 0x09c3 rotationTables)
    (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x89E1, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, colorRotationCode, rotationTables, UInt16.reduceAdd] at hcode htab
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x89E1, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary crot hrun [hcode, htab, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero, rom_idx_not_ram] until [0x8A38]
    exact finish (clear hcode htab; exact_finish crot)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface crot
summary_regs crot

/-! ## The records, stated cleanly -/

/-- The player-palette record. The background color is read from `BackgroundColors` at `$0744`, or at the area
type `$074E` when `$0744` is 0; neither index is bounded, so it's the ROM byte there. -/
def pcolFields (ram prg : UInt16 → UInt8) : List UInt8 :=
  [0x3F, 0x10, 0x04,
   bif ram 0x744 == 0 then prg ((0x85CF + (ram 0x74E).toUInt16) &&& 0x7FFF)
     else prg ((0x85CF + (ram 0x744).toUInt16) &&& 0x7FFF),
   bif ram 0x756 == 2 then 0x37 else bif ram 0x753 == 0 then 0x16 else 0x30,
   0x27,
   bif ram 0x756 == 2 then 0x16 else bif ram 0x753 == 0 then 0x18 else 0x19,
   0x00]

set_option maxHeartbeats 8000000 in
/-- Away from the scratch byte `$00` and the offset, `GetPlayerColors` lays down its record at the offset, for
any offset that leaves room for it. -/
theorem pcol_ram_record (ram prg : UInt16 → UInt8) (ho : ram 0x300 ≤ 248) (i : UInt16) (h0 : i ≠ 0)
    (h300 : i ≠ 0x300) : pcol_ram ram prg i = record ram (ram 0x300) (pcolFields ram prg) 0 i := by
  simp only [pcol_ram, pcol_c0, pcol_c1, pcol_c2, pcol_c3, pcol_c4, pcol_c5, pcol_c6, record, pcolFields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  bv_decide

theorem pcol_ram_offset (ram prg : UInt16 → UInt8) : pcol_ram ram prg 0x300 = ram 0x300 + 7 := by
  simp only [pcol_ram, pcol_c0, pcol_c1, pcol_c2, pcol_c3, pcol_c4, pcol_c5, pcol_c6]
  bv_decide

/-- Whether `ColorRotation` writes: on every eighth frame, and only while the offset is below `$31`. -/
def crotActive (ram : UInt16 → UInt8) : Bool := ram 9 &&& 7 == 0 && ram 0x300 < 0x31

/-- The rotation record: the area's palette 3 (`Palette3Data` at 4 × `$074E`), with its second color the
rotating one (`ColorRotatePalette` at `$06D4`). Written in the forms the summary reads them. -/
def crotFields (ram prg : UInt16 → UInt8) : List UInt8 :=
  [0x3F, 0x0C, 0x04,
   prg (((0x89D1 : UInt16) + (ram 0x74E <<< 1 <<< 1).toUInt16) &&& 0x7FFF),
   prg (((0x89C3 : UInt16) + (ram 0x6D4).toUInt16) &&& 0x7FFF),
   prg (((0x89D1 : UInt16) + (ram 0x74E <<< 1 <<< 1 + 1 + 1).toUInt16) &&& 0x7FFF),
   prg (((0x89D1 : UInt16) + (ram 0x74E <<< 1 <<< 1 + 1 + 1 + 1).toUInt16) &&& 0x7FFF),
   0x00]

set_option maxHeartbeats 8000000 in
/-- When it writes, `ColorRotation` lays down its record at the offset; away from the scratch byte `$00`, the
offset and the rotation index `$06D4`, nothing else changes. The guard keeps the record below `$0339`. -/
theorem crot_ram_record (ram prg : UInt16 → UInt8) (ha : crotActive ram = true) (i : UInt16) (h0 : i ≠ 0)
    (h300 : i ≠ 0x300) (h6d4 : i ≠ 0x6D4) :
    crot_ram ram prg i = record ram (ram 0x300) (crotFields ram prg) 0 i := by
  simp only [crotActive] at ha
  simp only [crot_ram, crot_c0, crot_c1, crot_c2, record, crotFields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  bv_decide

theorem crot_ram_offset (ram prg : UInt16 → UInt8) (ha : crotActive ram = true) :
    crot_ram ram prg 0x300 = ram 0x300 + 7 := by
  simp only [crotActive] at ha
  simp only [crot_ram, crot_c0, crot_c1, crot_c2]
  bv_decide

/-- Otherwise it changes nothing. -/
theorem crot_ram_idle (ram prg : UInt16 → UInt8) (ha : crotActive ram = false) (i : UInt16) :
    crot_ram ram prg i = ram i := by
  simp only [crotActive] at ha
  simp only [crot_ram, crot_c0, crot_c1, crot_c2]
  bv_decide

end Smb.Buffer
