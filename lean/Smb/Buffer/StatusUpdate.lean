import Smb.Data.ProofRom
import Smb.Summary
import Smb.Buffer.Addr
import Smb.Buffer.StatusRecord
import Smb.Routine.Common

/-!
# A score or coin update (`UpdateNumber`, `$BC36`)

`AddToScore` and `GiveOneCoin` end in `UpdateNumber` with `A` from `StatusBarNybbles`: `$02` for player 1, `$13`
for player 2. It calls `PrintStatusBarNumbers` (`$8F06`), which prints the low nybble's number and then the high
nybble's: the coins (selector 3 or 4, 5 bytes) and then the score (1 or 2, 9 bytes). So every score or coin
change appends 14 bytes, even when only one of them changed. `UpdateNumber` then blanks the score's leading digit
if it's 0, at `$02FB + o'` with `o'` the new offset, which is the first score digit.
-/
namespace Smb.Buffer
open Smb Smb.Routine

def printStatusCode : List UInt8 := smbPrg% 0x8F06 11

def updateNumberCode : List UInt8 :=
  smbPrg% 0xBC36 19

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem printStatusCode_in_rom : CodeAt rom 0x0f06 printStatusCode := codeAt_of_matches _ _ _ (by native_decide)
theorem updateNumberCode_in_rom : CodeAt rom 0x3c36 updateNumberCode := codeAt_of_matches _ _ _ (by native_decide)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem update1_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xBC36 ≤ a && a ≤ 0xBC48 || 0x8F06 ≤ a && a ≤ 0x8F5E) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hupd : CodeAt prg 0x3c36 updateNumberCode) (hpsb : CodeAt prg 0x0f06 printStatusCode)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hdata : CodeAt prg 0x0ef4 statusData)
    (hoff : CodeAt prg 0x0f00 statusOffset) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0xBC36, 0x02, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, updateNumberCode, printStatusCode, outputNumbersCode, statusData, statusOffset,
    UInt16.reduceAdd] at hupd hpsb hcode hdata hoff
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0xBC36, 0x02, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary upd1 hrun [hupd, hpsb, hcode, hdata, hoff, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack,
      dec_ge_zero] until [0xBC48]
    exact finish (clear hupd hpsb hcode hdata hoff; exact_finish upd1)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface upd1
summary_regs upd1

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem update2_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xBC36 ≤ a && a ≤ 0xBC48 || 0x8F06 ≤ a && a ≤ 0x8F5E) = true → a ≠ stop)
    (m : Nat) (x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hupd : CodeAt prg 0x3c36 updateNumberCode) (hpsb : CodeAt prg 0x0f06 printStatusCode)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hdata : CodeAt prg 0x0ef4 statusData)
    (hoff : CodeAt prg 0x0f00 statusOffset) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0xBC36, 0x13, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, updateNumberCode, printStatusCode, outputNumbersCode, statusData, statusOffset,
    UInt16.reduceAdd] at hupd hpsb hcode hdata hoff
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 300)).run ⟨⟨0xBC36, 0x13, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary upd2 hrun [hupd, hpsb, hcode, hdata, hoff, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack,
      dec_ge_zero] until [0xBC48]
    exact finish (clear hupd hpsb hcode hdata hoff; exact_finish upd2)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface upd2
summary_regs upd2

/-! ## The update, stated cleanly -/

/-- Player 1's update: the coin record (digits `$07ED`), then the score record (digits `$07DD`) over
its terminator, with a leading zero shown as the blank tile `$24`. -/
def upd1Fields (ram : UInt16 → UInt8) : List UInt8 :=
  [0x20, 0x6d, 0x02, ram 0x7ED, ram 0x7EE,
   0x20, 0x62, 0x06, bif ram 0x7DD == 0 then 0x24 else ram 0x7DD, ram 0x7DE, ram 0x7DF, ram 0x7E0, ram 0x7E1, ram 0x7E2, 0x00]

set_option maxHeartbeats 8000000 in
/-- Away from the stack bytes and the scratch bytes `$00`, `$02`, `$03`, player 1's update lays down its two
records at the offset, for any offset that leaves room for them. -/
theorem upd1_ram_record (sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 240) (i : UInt16)
    (hs : ∀ d : UInt8, d ≤ 4 → i ≠ (0x100 ||| (sp - d).toUInt16) &&& 0x7FF)
    (h0 : i ≠ 0) (h2 : i ≠ 2) (h3 : i ≠ 3) (h300 : i ≠ 0x300) :
    upd1_ram sp ram i = record ram (ram 0x300) (upd1Fields ram) 0 i := by
  have hs0 := hs 0 (by decide); have hs1 := hs 1 (by decide); have hs2 := hs 2 (by decide)
  have hs3 := hs 3 (by decide); have hs4 := hs 4 (by decide)
  simp only [upd1_ram, upd1_c0, record, upd1Fields, put, UInt16.reduceAdd] at *
  generalize ram 0x300 = o at *
  bv_decide

theorem upd1_ram_offset (sp : UInt8) (ram : UInt16 → UInt8) : upd1_ram sp ram 0x300 = ram 0x300 + 14 := by
  simp only [upd1_ram, upd1_c0]
  bv_decide

/-- Player 2's update: the coin record (digits `$07F3`), then the score record (digits `$07E3`) over
its terminator, with a leading zero shown as the blank tile `$24`. -/
def upd2Fields (ram : UInt16 → UInt8) : List UInt8 :=
  [0x20, 0x6d, 0x02, ram 0x7F3, ram 0x7F4,
   0x20, 0x62, 0x06, bif ram 0x7E3 == 0 then 0x24 else ram 0x7E3, ram 0x7E4, ram 0x7E5, ram 0x7E6, ram 0x7E7, ram 0x7E8, 0x00]

set_option maxHeartbeats 8000000 in
/-- Away from the stack bytes and the scratch bytes `$00`, `$02`, `$03`, player 2's update lays down its two
records at the offset, for any offset that leaves room for them. -/
theorem upd2_ram_record (sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 240) (i : UInt16)
    (hs : ∀ d : UInt8, d ≤ 4 → i ≠ (0x100 ||| (sp - d).toUInt16) &&& 0x7FF)
    (h0 : i ≠ 0) (h2 : i ≠ 2) (h3 : i ≠ 3) (h300 : i ≠ 0x300) :
    upd2_ram sp ram i = record ram (ram 0x300) (upd2Fields ram) 0 i := by
  have hs0 := hs 0 (by decide); have hs1 := hs 1 (by decide); have hs2 := hs 2 (by decide)
  have hs3 := hs 3 (by decide); have hs4 := hs 4 (by decide)
  simp only [upd2_ram, upd2_c0, record, upd2Fields, put, UInt16.reduceAdd] at *
  generalize ram 0x300 = o at *
  bv_decide

theorem upd2_ram_offset (sp : UInt8) (ram : UInt16 → UInt8) : upd2_ram sp ram 0x300 = ram 0x300 + 14 := by
  simp only [upd2_ram, upd2_c0]
  bv_decide

end Smb.Buffer
