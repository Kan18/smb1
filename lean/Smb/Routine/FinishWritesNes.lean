import Smb.Routine.NesBusRam
import Smb.Game

/-!
# Finish-state properties of full NES bus calls

Reads, including DMA and I/O reads, preserve the RAM-only finish predicate. A write
of any value other than 2, 7 or 3 cannot create it, at any bus address. The write
consumer assumes the normal 2 KiB RAM size; it does not require Quiet, disabled DMA
or a clear unsupported flag. This is a property of the executable model's bus calls,
not yet of a complete instruction, arbitrary routine, legal history or hardware.
-/

namespace Smb.Routine.FinishWritesNes

/-- The project's finish predicate depends only on the CPU RAM array. -/
theorem finish_eq_of_ram_eq (s t : NES) (h : t.ram = s.ram) :
    finalVictory t = finalVictory s := by
  simp only [finalVictory, operMode, h]

/-- Replacing any one RAM byte with a value distinct from all required finish
values cannot create the finish predicate. No destination-range premise is needed. -/
theorem set_byte_cannot_create (s : NES) (i : Nat) (v : UInt8)
    (hs : s.ram.size = 0x800) (hv : v ≠ 2 ∧ v ≠ 7 ∧ v ≠ 3)
    (hf : finalVictory { s with ram := s.ram.set! i v } = true) :
    finalVictory s = true := by
  simp only [finalVictory, operMode, Bool.and_eq_true, beq_iff_eq] at hf ⊢
  by_cases hm : i = 0x770
  · have he := hf.1.1
    rw [hm, ByteArray.get!_set!_self _ _ _ (by omega)] at he
    exact False.elim (hv.1 he)
  by_cases hw : i = 0x75f
  · have he := hf.1.2
    rw [hw, ByteArray.get!_set!_self _ _ _ (by omega)] at he
    exact False.elim (hv.2.1 he)
  by_cases hl : i = 0x75c
  · have he := hf.2
    rw [hl, ByteArray.get!_set!_self _ _ _ (by omega)] at he
    exact False.elim (hv.2.2 he)
  rw [ByteArray.get!_set!_ne _ _ _ _ hm,
      ByteArray.get!_set!_ne _ _ _ _ hw,
      ByteArray.get!_set!_ne _ _ _ _ hl] at hf
  exact hf


/-- Includes pending DMA and arbitrary PPU/controller reads. -/
theorem read_preserves_finish (s : NES) (a : UInt16) :
    finalVictory (NES.rdS s a).2 = finalVictory s :=
  finish_eq_of_ram_eq s _ (NES.BusRam.rdS_ram s a)

theorem tick_preserves_finish (s : NES) :
    finalVictory (NES.tickS s) = finalVictory s :=
  finish_eq_of_ram_eq s _ (NES.BusRam.tickS_ram s)

theorem write_preserves_ram_size (s : NES) (a : UInt16) (v : UInt8) :
    (NES.wrS s a v).ram.size = s.ram.size := by
  rw [NES.BusRam.wrS_ram]
  split <;> simp only [ByteArray.size_set!]

/-- A bus write outside CPU RAM preserves the finish predicate for every value. -/
theorem outside_ram_preserves_finish (s : NES) (a : UInt16) (v : UInt8)
    (ha : ¬ a < 0x2000) : finalVictory (NES.wrS s a v) = finalVictory s := by
  apply finish_eq_of_ram_eq s
  rw [NES.BusRam.wrS_ram, if_neg ha]

/-- The full modeled write, including PPU effects and interrupt bookkeeping. -/
theorem write_cannot_create (s : NES) (a : UInt16) (v : UInt8)
    (hs : s.ram.size = 0x800) (hv : v ≠ 2 ∧ v ≠ 7 ∧ v ≠ 3)
    (hf : finalVictory (NES.wrS s a v) = true) : finalVictory s = true := by
  by_cases ha : a < 0x2000
  · have hr := NES.BusRam.wrS_ram s a v
    rw [if_pos ha] at hr
    have he := finish_eq_of_ram_eq { s with ram := s.ram.set! (a &&& 0x7FF).toNat v }
      (NES.wrS s a v) hr
    rw [he] at hf
    exact set_byte_cannot_create s _ v hs hv hf
  · rw [outside_ram_preserves_finish s a v ha] at hf
    exact hf

theorem filtered_values_avoid_finish (v : UInt8) (hv : v = 0 ∨ 0x10 ≤ v) :
    v ≠ 2 ∧ v ≠ 7 ∧ v ≠ 3 := by
  rcases hv with rfl | hv
  · decide
  · change 16 ≤ v.toNat at hv
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst v <;> revert hv <;> decide

theorem filtered_write_cannot_create (s : NES) (a : UInt16) (v : UInt8)
    (hs : s.ram.size = 0x800) (hv : v = 0 ∨ 0x10 ≤ v)
    (hf : finalVictory (NES.wrS s a v) = true) : finalVictory s = true :=
  write_cannot_create s a v hs (filtered_values_avoid_finish v hv) hf

/-- The same fact at the generic CPU bus primitive used by instruction semantics. -/
theorem cpu_write_cannot_create (s : NES) (a : UInt16) (v : UInt8)
    (hs : s.ram.size = 0x800) (hv : v ≠ 2 ∧ v ≠ 7 ∧ v ≠ 3)
    (hf : finalVictory ((CPU.wr (σ := NES) a v).run s).2 = true) : finalVictory s = true :=
  write_cannot_create s a v hs hv hf

/- One full modeled bus call, not a CPU-instruction or global first-write theorem.
No Quiet, I-bit, PPU, DMA, controller or supportedness hypothesis is needed. -/
theorem write_creates_finish_only (s : NES) (a : UInt16) (v : UInt8)
    (hs : s.ram.size = 0x800)
    (hbefore : finalVictory s = false)
    (hafter : finalVictory (NES.wrS s a v) = true) :
    a < 0x2000 ∧
      ((a &&& 0x7ff = 0x770 ∧ v = 2) ∨
       (a &&& 0x7ff = 0x75f ∧ v = 7) ∨
       (a &&& 0x7ff = 0x75c ∧ v = 3)) := by
  have hr := NES.BusRam.wrS_ram s a v
  by_cases ha : a < 0x2000
  · rw [if_pos ha] at hr
    have hf := hafter
    simp only [finalVictory, operMode, hr, Bool.and_eq_true, beq_iff_eq] at hf
    refine ⟨ha, ?_⟩
    by_cases hm : a &&& 0x7ff = 0x770
    · have hi : (a &&& 0x7ff).toNat = 0x770 := congrArg UInt16.toNat hm
      have hv := hf.1.1
      rw [hi, ByteArray.get!_set!_self _ _ _ (by omega)] at hv
      exact Or.inl ⟨hm, hv⟩
    by_cases hw : a &&& 0x7ff = 0x75f
    · have hi : (a &&& 0x7ff).toNat = 0x75f := congrArg UInt16.toNat hw
      have hv := hf.1.2
      rw [hi, ByteArray.get!_set!_self _ _ _ (by omega)] at hv
      exact Or.inr (Or.inl ⟨hw, hv⟩)
    by_cases hl : a &&& 0x7ff = 0x75c
    · have hi : (a &&& 0x7ff).toNat = 0x75c := congrArg UInt16.toNat hl
      have hv := hf.2
      rw [hi, ByteArray.get!_set!_self _ _ _ (by omega)] at hv
      exact Or.inr (Or.inr ⟨hl, hv⟩)
    have hnm : (a &&& 0x7ff).toNat ≠ 0x770 := fun h => hm (UInt16.toNat_inj.mp h)
    have hnw : (a &&& 0x7ff).toNat ≠ 0x75f := fun h => hw (UInt16.toNat_inj.mp h)
    have hnl : (a &&& 0x7ff).toNat ≠ 0x75c := fun h => hl (UInt16.toNat_inj.mp h)
    rw [ByteArray.get!_set!_ne _ _ _ _ hnm,
        ByteArray.get!_set!_ne _ _ _ _ hnw,
        ByteArray.get!_set!_ne _ _ _ _ hnl] at hf
    have hold : finalVictory s = true := by
      simpa only [finalVictory, operMode, Bool.and_eq_true, beq_iff_eq] using hf
    exact False.elim (Bool.false_ne_true (hbefore.symm.trans hold))
  · rw [if_neg ha] at hr
    have hold : finalVictory s = true := by
      simpa only [finalVictory, operMode, hr] using hafter
    exact False.elim (Bool.false_ne_true (hbefore.symm.trans hold))


end Smb.Routine.FinishWritesNes
