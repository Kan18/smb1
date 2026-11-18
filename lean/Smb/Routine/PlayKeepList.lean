import Smb.Routine.PlayKeep

/-!
# `PlayKeep` for any cells the other regions all protect

`rest_run_list` is `rest_run` for a list of cells `L` that every region other than the player's protects, instead of
the horizontal bytes. It's for `$0705`, `$0755` and `$0785` once the regions protect them: `$0705` for the
acceleration limit's speed at the next call, `$0755` and `$0785` for `XInv`'s scroll clause after the tail's copy.
-/
namespace Smb.Routine.PlayKeep
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle PlaySavedHandoffs

private theorem glob_at' {r : Region} {s : NES} (h : At r s) (i : UInt16) (hi : i &&& 0x7FF = i) :
    (gAt PlayParser.G i).mem (s.ram.get! i.toNat) = true := by
  obtain ⟨_, _, ram0, ⟨t, _, ⟨b, _, hb⟩, hr⟩, _, _⟩ := h
  have he : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hr with hr | ⟨_, hr⟩
    · exact hr.ram i
    · exact hr.ram i
  rw [hi] at he
  rw [he]
  exact hb.glob i

theorem rest_step_list (L : List UInt16) (hL : ∀ a ∈ L, ∀ r ∈ rest, r.prot (a &&& 0x7FF) = true)
    {r : Region} (hr : r ∈ rest) {s : NES} (h : At r s) (hd : stop s.pc = false)
    (hus : s.unmodelled = false) (hu : (CPU.step.run s).2.unmodelled = false) (hc : CleanIf (CPU.step.run s).2) :
    (∃ r1 ∈ rest, At r1 (CPU.step.run s).2 ∧ ∀ a ∈ L, ramAt (CPU.step.run s).2 a = ramAt s a) ∨ Entered s := by
  obtain ⟨r1, hr1, hat, htr, ram1, hb, hx, ha⟩ := savedFinv_step_track (rest_sub hr) (fits checked)
    (zfits preambles_checked) h hd hus hu (by
      intro hk
      apply hc
      · have hkeep := hk 0x770 (fun r hr => (modes_of hr).1) (by decide)
        have hmode := elems_single mode770 (glob_at' h 0x770 (by decide))
        exact hkeep.trans hmode
      · have hkeep := hk 0x772 (fun r hr => (modes_of hr).2) (by decide)
        have hmode := elems_single mode772 (glob_at' h 0x772 (by decide))
        exact hkeep.trans hmode)
  by_cases hin : r1 ∈ rest
  · refine Or.inl ⟨r1, hin, hat, fun a ha' => ?_⟩
    have hp := hL a ha' r1 hin
    exact (ginv_ram ha a hp).trans (ginv_ram hb a hp).symm
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr1
    have hnc : c ∉ restConfigs := fun h' => hin (List.mem_map.mpr ⟨c, h', rfl⟩)
    rcases htr with e | ⟨_, q, hq, hqpc⟩
    · rw [e] at hin; exact absurd hr hin
    · exact Or.inr ⟨hqpc.symm.trans (p_entry hc hnc hq), c, hc, hnc, hat, ram1, hb, hx, ha⟩

/-- **Along the other regions**, until the player region is entered, the cells of `L` are kept. -/
theorem rest_run_list (L : List UInt16) (hL : ∀ a ∈ L, ∀ r ∈ rest, r.prot (a &&& 0x7FF) = true)
    (n : Nat) (s : NES) (r : Region) (hr : r ∈ rest) (h : At r s)
    (hd : ∀ i, i < n → stop (stepN i s).pc = false)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hc : ∀ i, i < n → CleanIf (stepN (i + 1) s)) :
    (∃ r1 ∈ rest, At r1 (stepN n s) ∧ ∀ a ∈ L, ramAt (stepN n s) a = ramAt s a) ∨
      ∃ k, k < n ∧ (∀ a ∈ L, ramAt (stepN k s) a = ramAt s a) ∧ Entered (stepN k s) := by
  induction n generalizing s r with
  | zero => exact Or.inl ⟨r, hr, h, fun _ _ => rfl⟩
  | succ n ih =>
    rcases rest_step_list L hL hr h (hd 0 (Nat.succ_pos _)) (hu 0 (Nat.zero_le _)) (hu 1 (by omega))
        (hc 0 (Nat.succ_pos _)) with ⟨r1, hr1, h1, k1⟩ | he
    · rcases ih (CPU.step.run s).2 r1 hr1 h1 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi))
          (fun i hi => hu (i + 1) (Nat.succ_le_succ hi)) (fun i hi => hc (i + 1) (Nat.succ_lt_succ hi)) with
        ⟨r2, hr2, h2, k2⟩ | ⟨k, hk, k2, he⟩
      · exact Or.inl ⟨r2, hr2, h2, fun a ha => (k2 a ha).trans (k1 a ha)⟩
      · exact Or.inr ⟨k + 1, by omega, fun a ha => (k2 a ha).trans (k1 a ha), he⟩
    · exact Or.inr ⟨0, Nat.succ_pos _, fun _ _ => rfl, he⟩

end Smb.Routine.PlayKeep
