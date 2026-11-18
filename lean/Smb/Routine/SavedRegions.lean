import Smb.Routine.AbsBridge

/-! Region composition with a saved entry-memory witness. Unlike `Fits`, a
handoff may select its next entry using values protected since region entry.
The witness is unchanged by steps inside a region and refreshed only at a
checked handoff. This supports alternating parser and object tuples. -/
namespace Smb.Abs

/-- A region invariant together with facts about its entry memory. -/
def SavedInv (rom : UInt16 → UInt8) (g : Global) (rs : List Region)
    (saved : Region → (UInt16 → UInt8) → Prop) (s : NES) : Prop :=
  ∃ r ∈ rs, ∃ ram0, GInv rom r.prot g ram0 r.T s ∧ saved r ram0

/-- Logical handoffs may restore protected cells from an entry-memory witness.
They must establish an actual next-region entry, not only a projection. -/
structure SavedFits (rom : UInt16 → UInt8) (g : Global) (rs : List Region)
    (done : UInt16 → Bool) (saved : Region → (UInt16 → UInt8) → Prop) : Prop where
  chk : ∀ r ∈ rs, checkF rom r.exit r.prot g r.T = true
  idle : ∀ r ∈ rs, r.exit idlePC = false
  entries : ∀ r ∈ rs, r.entries.all (entryIn g r.T) = true
  link : ∀ r ∈ rs, ∀ ram0 b t, b ∈ r.T.at t.regs.pc →
    Holds r.prot g ram0 b t → saved r ram0 → r.exit t.regs.pc = true →
    done t.regs.pc = true ∨ ∃ r' ∈ rs, ∃ e ∈ r'.entries,
      r'.exit t.regs.pc = false ∧ Holds r'.prot g t.ram e t ∧ saved r' t.ram

theorem savedInv_step {rom : UInt16 → UInt8} {g : Global} {rs : List Region}
    {done : UInt16 → Bool} {saved : Region → (UInt16 → UInt8) → Prop} {s : NES}
    (hf : SavedFits rom g rs done saved) (h : SavedInv rom g rs saved s)
    (hd : done s.pc = false) (hg : Guard s) (hA : Clean g (CPU.step.run s).2) :
    SavedInv rom g rs saved (CPU.step.run s).2 := by
  obtain ⟨r, hr, ram0, hi, hs⟩ := h
  cases hx : r.exit s.pc with
  | false => exact ⟨r, hr, ram0, ginv_step (hf.chk r hr) (hf.idle r hr) hi hx hg hA, hs⟩
  | true =>
    obtain ⟨t, hc, ⟨b, hb, hh⟩, hrel⟩ := hi
    have hpc : s.pc = t.regs.pc := by
      rcases hrel with h1 | ⟨_, h1⟩
      · exact congrArg Regs.pc h1.regs
      · exact congrArg Regs.pc h1.regs
    rcases hf.link r hr ram0 b t hb hh hs (by simpa [← hpc] using hx) with hd' | ⟨r', hr', e, he, hx', hh', hs'⟩
    · rw [← hpc, hd] at hd'; cases hd'
    · have hi' : GInv rom r'.prot g t.ram r'.T s :=
        ⟨t, hc, inv_of_entry (List.all_eq_true.mp (hf.entries r' hr') e he) hh', hrel⟩
      exact ⟨r', hr', t.ram,
        ginv_step (hf.chk r' hr') (hf.idle r' hr') hi' (by simpa [hpc] using hx') hg hA, hs'⟩

/-- Iterate without assuming a fixed controller or fixed number of frames. -/
theorem savedInv_stepN {rom : UInt16 → UInt8} {g : Global} {rs : List Region}
    {done : UInt16 → Bool} {saved : Region → (UInt16 → UInt8) → Prop}
    (hf : SavedFits rom g rs done saved) (n : Nat) (s : NES)
    (hd : ∀ i, i < n → done (stepN i s).pc = false)
    (hg : ∀ i, i < n → Guard (stepN i s))
    (hA : ∀ i, i < n → Clean g (stepN (i + 1) s))
    (h : SavedInv rom g rs saved s) : SavedInv rom g rs saved (stepN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    exact ih (CPU.step.run s).2 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hg (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hA (i + 1) (Nat.succ_lt_succ hi))
      (savedInv_step hf h (hd 0 (Nat.succ_pos _)) (hg 0 (Nat.succ_pos _)) (hA 0 (Nat.succ_pos _)))

end Smb.Abs
