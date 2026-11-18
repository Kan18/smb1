import Smb.Data.ProofRom
import Smb.Routine.ColumnFinish

/-!
# The column filter and its actual write instruction

A whole-loop endpoint property alone does not cover a frame ending inside the loop.
These cuts identify the value before STA and check the actual CPU.step that writes it.
The prefix and write cover arbitrary pointers; the write also permits arbitrary flags.
No full-NES supportedness or global provenance of entry at these PCs is asserted.
-/

open Smb Smb.Routine Smb.Symbolic
open Smb.Routine.ColumnCopy (copyCode)
open Smb.Routine.ColumnFinish (Finish)
namespace Smb.Routine.ColumnWrite
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- X and Y are arbitrary bytes. $06A1+X is at most $07A0, hence in RAM,
-- and cannot alias the prefix's only store, STY $00.
def PrefixPost (x y sp : UInt8) (ram prg : UInt16 → UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0x94F7 ∧ (t.regs.a = 0 ∨ 0x10 ≤ t.regs.a) ∧
  t.regs.x = x ∧ t.regs.y = y ∧ t.regs.s = sp ∧ t.prg = prg ∧
  (t.regs.p &&& 4 == 0) = false ∧
  (∀ i, i ≠ 0 → t.ram i = ram i)

-- Actual filter prefix, stopping before STA ($06),Y. Arbitrary initial bad.
-- At most twelve instructions precede the stop; fourteen is only a fuel bound.
set_option maxHeartbeats 4000000 in
theorem filter_prefix (a x y sp p : UInt8) (ram prg : UInt16 → UInt8)
    (cyc : UInt64) (bad : Bool) (hcode : CodeAt prg 0x14D6 copyCode)
    (hI : (p &&& 4 == 0) = false) :
    PrefixPost x y sp ram prg ((CPU.runTo (σ := Plain) 0x94F7 14).run
      ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 := by
  have htab : prg 0x1504 = 0x10 ∧ prg 0x1505 = 0x51 ∧ prg 0x1506 = 0x88 ∧ prg 0x1507 = 0xC0 := by
    have h := hcode
    simp only [CodeAt, copyCode, UInt16.reduceAdd] at h
    simp [h]
  simp only [CodeAt, copyCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) 0x94F7 14).run
    ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 = t
  sym_run hrun [hcode, hI]
  all_goals
    intros
    clear hcode
    simp only [PrefixPost, ← and_assoc]
    refine ⟨?_, fun i hi => ?_⟩
    · try sym_exec [bne]
      fun_congr
      bv_decide
    · try sym_exec [bne]
      fun_congr
      bv_decide

theorem prefix_finish_iff {x y sp : UInt8} {ram prg : UInt16 → UInt8} {t : Plain}
    (h : PrefixPost x y sp ram prg t) : Finish t.ram ↔ Finish ram := by
  rcases h with ⟨_,_,_,_,_,_,_,hf⟩
  unfold Finish
  rw [hf 0x770 (by decide), hf 0x75F (by decide), hf 0x75C (by decide)]

def StorePost (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (t : Plain) : Prop :=
  t.regs.pc = 0x94F9 ∧ t.regs.a = a ∧ t.regs.x = x ∧ t.regs.y = y ∧
  t.regs.s = sp ∧ t.regs.p = p ∧ t.prg = prg ∧ t.cyc = cyc + 6 ∧
  (Finish t.ram → Finish ram)

-- Actual STA ($06),Y, including opcode fetch and all six bus cycles.
-- No pointer, Y, initial-bad, or I-bit restriction; no supportedness claim.
set_option maxHeartbeats 4000000 in
theorem store_step (a x y sp p : UInt8) (ram prg : UInt16 → UInt8)
    (cyc : UInt64) (bad : Bool) (hcode : CodeAt prg 0x14F7 (smbPrg% 0x94F7 2))
    (ha : a = 0 ∨ 0x10 ≤ a) :
    StorePost a x y sp p ram prg cyc ((CPU.step (σ := Plain)).run
      ⟨⟨0x94F7,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 := by
  simp only [CodeAt, UInt16.reduceAdd] at hcode
  generalize hs : ((CPU.step (σ := Plain)).run
    ⟨⟨0x94F7,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 = t
  sym_exec [hcode] at hs
  rw [Smb.StepLemma.tail_91] at hs
  sym_exec [hcode] at hs
  subst t
  clear hcode
  simp only [StorePost, ← and_assoc]
  refine ⟨?_, ?_⟩
  · try sym_exec [bne]
    trivial
  · intro hf
    simp only [Finish] at hf ⊢
    try sym_exec [bne] at *
    bv_decide

-- The instruction bytes for the separate store cut follow from the same code fact.
theorem store_code {prg : UInt16 → UInt8} (h : CodeAt prg 0x14D6 copyCode) :
    CodeAt prg 0x14F7 (smbPrg% 0x94F7 2) := by
  simp only [CodeAt, copyCode, UInt16.reduceAdd] at h ⊢
  simp [h]

end Smb.Routine.ColumnWrite
