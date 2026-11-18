import Smb.Data.ProofRom
import Smb.Summary
import Smb.Buffer.Addr
import Smb.Buffer.StatusRecord
import Smb.Routine.Common

/-!
# Setup writers and the selector exit

* `WriteBottomStatusLine` (`$865A`), during the intermediate screen's setup, prints the score and coins
  (`StatusUpdate`'s 14 bytes, through `GetSBNybbles`) and then, from `$865D`, the world and level: the record
  `$20 $73 $03`, world + 1, `$28` (a dash), level + 1, `0`, moving the offset on by 6.
* `OutputNumbers` returns at once for a selector of 6 or more, writing nothing. That's the second half of the
  timer's print: `RunGameTimer` prints `$A4`, whose high nybble gives selector `$0B`.
-/
namespace Smb.Buffer
open Smb Smb.Routine

def worldLevelCode : List UInt8 :=
  smbPrg% 0x865D 51

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem worldLevelCode_in_rom : CodeAt rom 0x065d worldLevelCode := codeAt_of_matches _ _ _ (by native_decide)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem worldLevel_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x865D ≤ a && a ≤ 0x868F) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x065d worldLevelCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x865D, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, worldLevelCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x865D, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary wl hrun [hcode, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero] until [0x8690]
    exact finish (clear hcode; exact_finish wl)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface wl
summary_regs wl

/-- The world-level record: address `$2073`, length 3, world + 1, a dash, level + 1, a terminator. -/
def wlFields (ram : UInt16 → UInt8) : List UInt8 := [0x20, 0x73, 0x03, ram 0x75F + 1, 0x28, ram 0x75C + 1, 0x00]

set_option maxHeartbeats 8000000 in
/-- Away from the offset, the world-level writer lays down its record at the offset and nothing else, for any
offset that leaves room for it. -/
theorem wl_ram_record (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 248) (i : UInt16) (h300 : i ≠ 0x300) :
    wl_ram ram i = record ram (ram 0x300) (wlFields ram) 0 i := by
  simp only [wl_ram, record, wlFields, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 0x75F = w at *
  generalize ram 0x75C = l at *
  bv_decide

theorem wl_ram_offset (ram : UInt16 → UInt8) : wl_ram ram 0x300 = ram 0x300 + 6 := by
  simp only [wl_ram]
  bv_decide

set_option maxHeartbeats 4000000 in
/-- A selector of 6 or more returns from `OutputNumbers` without touching memory. -/
theorem outputNumbers_exit (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0f11 outputNumbersCode) (hI : p &&& 4 ≠ 0) (ha : 6 ≤ a) :
    let t := ((CPU.runTo (σ := Plain) 0x8F5E 10).run ⟨⟨0x8F16, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.bad = false ∧ t.regs.pc = 0x8F5E ∧ t.regs.s = sp ∧ t.ram = ram := by
  dsimp only
  simp only [CodeAt, outputNumbersCode, UInt16.reduceAdd] at hcode
  generalize hr : ((CPU.runTo (σ := Plain) 0x8F5E 10).run ⟨⟨0x8F16, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  have hge : decide (a ≥ 6) = true := by simpa using ha
  sym_run hr [hcode, hi, hge]
  all_goals
    intros
    clear hcode hi
    exact ⟨rfl, rfl, rfl, rfl⟩

end Smb.Buffer
