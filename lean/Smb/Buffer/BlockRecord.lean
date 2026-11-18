import Smb.Data.ProofRom
import Smb.Summary
import Smb.Buffer.Addr
import Smb.Buffer.StatusRecord
import Smb.Routine.Common

/-!
# The block record (`WriteBlockMetatile`, `$8A6D`)

When a block changes, `WriteBlockMetatile` appends a record redrawing its 16×16 metatile: two PPU writes of two
tiles each, one per tile row. With `o = $0300` it writes, from `$0301 + o`,

  `hi, lo, 2, t0, t1, hi, lo + $20, 2, t2, t3, 0`

and sets `$0300` to `o + 10`, so the next record overwrites the terminator. The PPU address comes from the
block-buffer row offset `$02` and pointer `$06`, and the tiles from `BlockGfxData` by the metatile in `A`:
blank (`0`), brick with line (`$51`, `$58`), brick without (`$52`, `$5D`), or used block (anything else).
Through `PutBlockMetatile` (`$8A97`) and `SetVRAMOffset` (`$863F`). Nothing bounds `o`.
-/
namespace Smb.Buffer
open Smb Smb.Routine

def writeBlockCode : List UInt8 :=
  smbPrg% 0x8A6D 42

def putBlockCode : List UInt8 :=
  smbPrg% 0x8A97 113

/-- `BlockGfxData`: four tiles per metatile kind. -/
def blockGfx : List UInt8 :=
  smbPrg% 0x8A39 20

/-- `SetVRAMOffset`: `sta $0300`, `rts`. -/
def setOffsetCode : List UInt8 := smbPrg% 0x863F 4

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem writeBlockCode_in_rom : CodeAt rom 0x0a6d writeBlockCode := codeAt_of_matches _ _ _ (by native_decide)
theorem putBlockCode_in_rom : CodeAt rom 0x0a97 putBlockCode := codeAt_of_matches _ _ _ (by native_decide)
theorem blockGfx_in_rom : CodeAt rom 0x0a39 blockGfx := codeAt_of_matches _ _ _ (by native_decide)
theorem setOffsetCode_in_rom : CodeAt rom 0x063f setOffsetCode := codeAt_of_matches _ _ _ (by native_decide)

set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem block0_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8A87 ≤ a && a ≤ 0x8B07 || 0x863F ≤ a && a ≤ 0x8642) = true → a ≠ stop)
    (m : Nat) (a x sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0a6d writeBlockCode) (hput : CodeAt prg 0x0a97 putBlockCode)
    (hgfx : CodeAt prg 0x0a39 blockGfx) (hset : CodeAt prg 0x063f setOffsetCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8A87, a, x, 0, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, writeBlockCode, putBlockCode, blockGfx, setOffsetCode, UInt16.reduceAdd] at hcode hput hgfx hset
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8A87, a, x, 0, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary blk0 hrun [hcode, hput, hgfx, hset, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero]
      until [0x8642]
    exact finish (clear hcode hput hgfx hset; exact_finish blk0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface blk0
summary_regs blk0

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem block1_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8A87 ≤ a && a ≤ 0x8B07 || 0x863F ≤ a && a ≤ 0x8642) = true → a ≠ stop)
    (m : Nat) (a x sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0a6d writeBlockCode) (hput : CodeAt prg 0x0a97 putBlockCode)
    (hgfx : CodeAt prg 0x0a39 blockGfx) (hset : CodeAt prg 0x063f setOffsetCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8A87, a, x, 1, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, writeBlockCode, putBlockCode, blockGfx, setOffsetCode, UInt16.reduceAdd] at hcode hput hgfx hset
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8A87, a, x, 1, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary blk1 hrun [hcode, hput, hgfx, hset, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero]
      until [0x8642]
    exact finish (clear hcode hput hgfx hset; exact_finish blk1)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface blk1
summary_regs blk1

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem block2_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8A87 ≤ a && a ≤ 0x8B07 || 0x863F ≤ a && a ≤ 0x8642) = true → a ≠ stop)
    (m : Nat) (a x sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0a6d writeBlockCode) (hput : CodeAt prg 0x0a97 putBlockCode)
    (hgfx : CodeAt prg 0x0a39 blockGfx) (hset : CodeAt prg 0x063f setOffsetCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8A87, a, x, 2, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, writeBlockCode, putBlockCode, blockGfx, setOffsetCode, UInt16.reduceAdd] at hcode hput hgfx hset
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8A87, a, x, 2, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary blk2 hrun [hcode, hput, hgfx, hset, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero]
      until [0x8642]
    exact finish (clear hcode hput hgfx hset; exact_finish blk2)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface blk2
summary_regs blk2

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem block3_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8A87 ≤ a && a ≤ 0x8B07 || 0x863F ≤ a && a ≤ 0x8642) = true → a ≠ stop)
    (m : Nat) (a x sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0a6d writeBlockCode) (hput : CodeAt prg 0x0a97 putBlockCode)
    (hgfx : CodeAt prg 0x0a39 blockGfx) (hset : CodeAt prg 0x063f setOffsetCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8A87, a, x, 3, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, writeBlockCode, putBlockCode, blockGfx, setOffsetCode, UInt16.reduceAdd] at hcode hput hgfx hset
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 100)).run ⟨⟨0x8A87, a, x, 3, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary blk3 hrun [hcode, hput, hgfx, hset, hI, idx_ne_k, k_ne_idx, stack_ne_idx, idx_ne_stack, dec_ge_zero]
      until [0x8642]
    exact finish (clear hcode hput hgfx hset; exact_finish blk3)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
summary_interface blk3
summary_regs blk3

/-- The tile kind `WriteBlockMetatile` picks for metatile `a`, as the offset into `BlockGfxData` divided by 4. -/
def blockKind (a : UInt8) : UInt8 :=
  bif a == 0 then 3 else bif a == 0x58 || a == 0x51 then 0 else bif a == 0x5D || a == 0x52 then 1 else 2

set_option maxHeartbeats 4000000 in
/-- From `WriteBlockMetatile`'s entry to `UseBOffset`, only `Y` changes, to the metatile's kind. -/
theorem blockKind_run (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x0a6d writeBlockCode) (hI : p &&& 4 ≠ 0) :
    let t := ((CPU.runTo (σ := Plain) 0x8A87 20).run ⟨⟨0x8A6D, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.bad = false ∧ t.regs.pc = 0x8A87 ∧ t.regs.a = a ∧ t.regs.x = x ∧ t.regs.y = blockKind a ∧ t.regs.s = sp ∧
      t.ram = ram := by
  dsimp only
  simp only [CodeAt, writeBlockCode, UInt16.reduceAdd] at hcode
  generalize hr : ((CPU.runTo (σ := Plain) 0x8A87 20).run ⟨⟨0x8A6D, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hcode, hi]
  all_goals
    intros
    clear hcode hi
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    dsimp only
    simp only [blockKind]
    bv_decide

/-! ## The record, stated cleanly -/

/-- The low byte of the metatile's PPU address, from row offset `$02` and block-buffer pointer `$06`. -/
def blockLo (r2 r6 : UInt8) : UInt8 := ((r2 + 0x20) <<< 2) + ((r6 &&& 0x0F) <<< 1)

/-- The high byte: name table `$20` or `$24` (pointers from `$D0` are the odd page), the row's top bits, and the
low byte's carry. -/
def blockHi (r2 r6 : UInt8) : UInt8 :=
  (bif r6 < 0xD0 then (0x20 : UInt8) else 0x24) + ((r2 + 0x20) >>> 6) + (bif blockLo r2 r6 < ((r2 + 0x20) <<< 2) then (1 : UInt8) else 0)

/-- Kind 0, a brick with a line. -/
def blk0Fields (ram : UInt16 → UInt8) : List UInt8 :=
  [blockHi (ram 2) (ram 6), blockLo (ram 2) (ram 6), 0x02, 0x45, 0x45,
   blockHi (ram 2) (ram 6), blockLo (ram 2) (ram 6) + 0x20, 0x02, 0x47, 0x47, 0x00]

set_option maxHeartbeats 8000000 in
/-- Away from the two stack bytes, the scratch bytes `$00`, `$01`, `$03`–`$05` and the offset, a kind-0 block
record is laid down at the offset, for any offset that leaves room for it. -/
theorem blk0_ram_record (x sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 244) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (hs' : i ≠ (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h3 : i ≠ 3) (h4 : i ≠ 4) (h5 : i ≠ 5) (h300 : i ≠ 0x300) :
    blk0_ram x sp ram i = record ram (ram 0x300) (blk0Fields ram) 0 i := by
  simp only [blk0_ram, blk0_c0, record, blk0Fields, blockHi, blockLo, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 2 = r2 at *
  generalize ram 6 = r6 at *
  bv_decide

theorem blk0_ram_offset (x sp : UInt8) (ram : UInt16 → UInt8) : blk0_ram x sp ram 0x300 = ram 0x300 + 10 := by
  simp only [blk0_ram]
  bv_decide

/-- Kind 1, a brick without one. -/
def blk1Fields (ram : UInt16 → UInt8) : List UInt8 :=
  [blockHi (ram 2) (ram 6), blockLo (ram 2) (ram 6), 0x02, 0x47, 0x47,
   blockHi (ram 2) (ram 6), blockLo (ram 2) (ram 6) + 0x20, 0x02, 0x47, 0x47, 0x00]

set_option maxHeartbeats 8000000 in
/-- Away from the two stack bytes, the scratch bytes `$00`, `$01`, `$03`–`$05` and the offset, a kind-1 block
record is laid down at the offset, for any offset that leaves room for it. -/
theorem blk1_ram_record (x sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 244) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (hs' : i ≠ (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h3 : i ≠ 3) (h4 : i ≠ 4) (h5 : i ≠ 5) (h300 : i ≠ 0x300) :
    blk1_ram x sp ram i = record ram (ram 0x300) (blk1Fields ram) 0 i := by
  simp only [blk1_ram, blk1_c0, record, blk1Fields, blockHi, blockLo, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 2 = r2 at *
  generalize ram 6 = r6 at *
  bv_decide

theorem blk1_ram_offset (x sp : UInt8) (ram : UInt16 → UInt8) : blk1_ram x sp ram 0x300 = ram 0x300 + 10 := by
  simp only [blk1_ram]
  bv_decide

/-- Kind 2, a used block. -/
def blk2Fields (ram : UInt16 → UInt8) : List UInt8 :=
  [blockHi (ram 2) (ram 6), blockLo (ram 2) (ram 6), 0x02, 0x57, 0x58,
   blockHi (ram 2) (ram 6), blockLo (ram 2) (ram 6) + 0x20, 0x02, 0x59, 0x5a, 0x00]

set_option maxHeartbeats 8000000 in
/-- Away from the two stack bytes, the scratch bytes `$00`, `$01`, `$03`–`$05` and the offset, a kind-2 block
record is laid down at the offset, for any offset that leaves room for it. -/
theorem blk2_ram_record (x sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 244) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (hs' : i ≠ (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h3 : i ≠ 3) (h4 : i ≠ 4) (h5 : i ≠ 5) (h300 : i ≠ 0x300) :
    blk2_ram x sp ram i = record ram (ram 0x300) (blk2Fields ram) 0 i := by
  simp only [blk2_ram, blk2_c0, record, blk2Fields, blockHi, blockLo, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 2 = r2 at *
  generalize ram 6 = r6 at *
  bv_decide

theorem blk2_ram_offset (x sp : UInt8) (ram : UInt16 → UInt8) : blk2_ram x sp ram 0x300 = ram 0x300 + 10 := by
  simp only [blk2_ram]
  bv_decide

/-- Kind 3, a blank. -/
def blk3Fields (ram : UInt16 → UInt8) : List UInt8 :=
  [blockHi (ram 2) (ram 6), blockLo (ram 2) (ram 6), 0x02, 0x24, 0x24,
   blockHi (ram 2) (ram 6), blockLo (ram 2) (ram 6) + 0x20, 0x02, 0x24, 0x24, 0x00]

set_option maxHeartbeats 8000000 in
/-- Away from the two stack bytes, the scratch bytes `$00`, `$01`, `$03`–`$05` and the offset, a kind-3 block
record is laid down at the offset, for any offset that leaves room for it. -/
theorem blk3_ram_record (x sp : UInt8) (ram : UInt16 → UInt8) (ho : ram 0x300 ≤ 244) (i : UInt16)
    (hs : i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF) (hs' : i ≠ (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h3 : i ≠ 3) (h4 : i ≠ 4) (h5 : i ≠ 5) (h300 : i ≠ 0x300) :
    blk3_ram x sp ram i = record ram (ram 0x300) (blk3Fields ram) 0 i := by
  simp only [blk3_ram, blk3_c0, record, blk3Fields, blockHi, blockLo, put, UInt16.reduceAdd]
  generalize ram 0x300 = o at *
  generalize ram 2 = r2 at *
  generalize ram 6 = r6 at *
  bv_decide

theorem blk3_ram_offset (x sp : UInt8) (ram : UInt16 → UInt8) : blk3_ram x sp ram 0x300 = ram 0x300 + 10 := by
  simp only [blk3_ram]
  bv_decide

end Smb.Buffer
