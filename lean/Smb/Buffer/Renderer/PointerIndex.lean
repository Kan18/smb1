import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
The real renderer's metatile-high-bit transform at `$88D0`–`$88E1` produces
graphics-table index Y in 0..3.  The following `$88E2` instruction reads the
four-entry high-byte table; this file stops immediately before that read.
-/
namespace Smb.Buffer.Renderer.PointerIndex
open Smb Smb.Routine Smb.Symbolic

def code : List UInt8 :=
  smbPrg% 0x88D0 18

def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat
theorem code_in_rom : CodeAt rom 0x08d0 code :=
  codeAt_of_matches _ _ _ (by native_decide)

set_option maxHeartbeats 4000000 in
theorem index_lt_four (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88e2 14).run s).2
    t.bad = false ∧ t.regs.pc = 0x88e2 ∧ t.regs.y < 4 ∧
      t.ram 1 = x := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x88e2 14).run
    ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x88e2
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x88e2 _ rfl]
    simp_all (config := { maxSteps := 1000000 })
    bv_decide

set_option maxHeartbeats 4000000 in
theorem index_keeps_interrupt_disable (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88e2 14).run s).2
    t.regs.p &&& 4 ≠ 0 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x88e2 14).run
    ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x88e2
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x88e2 _ rfl]
    dsimp only
    bv_decide

set_option maxHeartbeats 4000000 in
theorem index_keeps_prg (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88e2 14).run s).2
    t.prg = prg := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x88e2 14).run
    ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x88e2
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x88e2 _ rfl]

set_option maxHeartbeats 4000000 in
theorem index_keeps_offset (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88e2 14).run s).2
    t.ram 0 = ram 0 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hrun : ((CPU.runTo (σ := Plain) 0x88e2 14).run
    ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hrun [hc, hi] until 0x88e2
  all_goals
    intros
    clear hc hi
    subst hrun
    rw [runTo_snd_stop _ 0x88e2 _ rfl]
    simp_all

def highLoadCode : List UInt8 := smbPrg% 0x88E2 5
def highTable : List UInt8 := smbPrg% 0x8B0C 4

theorem highLoad_in_rom : CodeAt rom 0x08e2 highLoadCode :=
  codeAt_of_matches _ _ _ (by native_decide)
theorem highTable_in_rom : CodeAt rom 0x0b0c highTable :=
  codeAt_of_matches _ _ _ (by native_decide)

set_option maxHeartbeats 3000000 in
theorem high_pointer_from_index (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08e2 highLoadCode)
    (ht : CodeAt prg 0x0b0c highTable)
    (hI : p &&& 4 ≠ 0) (hy : y < 4) :
    let s : Plain := ⟨⟨0x88e2, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88e7 3).run s).2
    t.bad = false ∧ t.regs.pc = 0x88e7 ∧
      (t.ram 7 = 0x8b ∨ t.ram 7 = 0x8c) := by
  dsimp only
  have hcases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by bv_decide
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    simp only [CodeAt, highLoadCode, highTable, UInt16.reduceAdd] at hc ht
    generalize hr : ((CPU.runTo (σ := Plain) 0x88e7 3).run
      ⟨⟨0x88e2, a, x, _, sp, p⟩, ram, prg, cyc, false⟩).2 = t
    have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
    sym_run hr [hc, ht, hi] until 0x88e7
    all_goals
      intros
      clear hc hi
      subst hr
      rw [runTo_snd_stop _ 0x88e7 _ rfl]
      simp_all (config := { maxSteps := 1000000 })

set_option maxHeartbeats 3000000 in
theorem high_load_seam (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08e2 highLoadCode)
    (ht : CodeAt prg 0x0b0c highTable)
    (hI : p &&& 4 ≠ 0) (hy : y < 4) :
    let s : Plain := ⟨⟨0x88e2, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88e7 3).run s).2
    t.ram 0 = ram 0 ∧ t.ram 1 = ram 1 ∧
      t.regs.p &&& 4 ≠ 0 ∧ t.prg = prg := by
  dsimp only
  have hcases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by bv_decide
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    simp only [CodeAt, highLoadCode, highTable, UInt16.reduceAdd] at hc ht
    generalize hr : ((CPU.runTo (σ := Plain) 0x88e7 3).run
      ⟨⟨0x88e2, a, x, _, sp, p⟩, ram, prg, cyc, false⟩).2 = t
    have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
    sym_run hr [hc, ht, hi] until 0x88e7
    all_goals
      intros
      clear hc hi
      subst hr
      rw [runTo_snd_stop _ 0x88e7 _ rfl]
      simp_all (config := { maxSteps := 1000000 })
      all_goals bv_decide

/-- Composition of the two bounded machine runs.  The first run produces the
Y range and preserves the I flag and PRG; the second performs the real
indexed table load.  The output remains a nested run at this seam, which is
enough for the later row-body composition. -/
theorem high_pointer_from_row_entry (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 code)
    (hh : CodeAt prg 0x08e2 highLoadCode)
    (ht : CodeAt prg 0x0b0c highTable)
    (hI : p &&& 4 ≠ 0) :
    let mid := ((CPU.runTo (σ := Plain) 0x88e2 14).run
      ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    let out := ((CPU.runTo (σ := Plain) 0x88e7 3).run mid).2
    out.bad = false ∧ out.regs.pc = 0x88e7 ∧
      (out.ram 7 = 0x8b ∨ out.ram 7 = 0x8c) ∧
      out.ram 0 = ram 0 ∧ out.ram 1 = x ∧
      out.regs.p &&& 4 ≠ 0 ∧ out.prg = prg := by
  dsimp only
  have hm := index_lt_four a x y sp p ram prg cyc hc hI
  have hi := index_keeps_interrupt_disable a x y sp p ram prg cyc hc hI
  have hp := index_keeps_prg a x y sp p ram prg cyc hc hI
  have h0 := index_keeps_offset a x y sp p ram prg cyc hc hI
  rcases mid : ((CPU.runTo (σ := Plain) 0x88e2 14).run
    ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 with
    ⟨⟨pc', a', x', y', sp', p'⟩, ram', prg', cyc', bad'⟩
  dsimp only at hm hi hp h0
  rw [mid] at hm hi hp h0
  dsimp only at hm hi hp h0
  obtain ⟨hbad, hpc, hy, hrow1⟩ := hm
  subst bad' pc' prg'
  have hptr := high_pointer_from_index a' x' y' sp' p' ram' prg cyc' hh ht hi hy
  have hseam := high_load_seam a' x' y' sp' p' ram' prg cyc' hh ht hi hy
  dsimp only at hptr hseam
  obtain ⟨hb2, hpc2, hp2⟩ := hptr
  obtain ⟨h02, h12, hi2, hprg2⟩ := hseam
  simpa only [mid] using
    (show _ from ⟨hb2, hpc2, hp2, h02.trans h0, h12.trans hrow1, hi2, hprg2⟩)

end Smb.Buffer.Renderer.PointerIndex
