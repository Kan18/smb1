import Smb.Routine.PlayCycleGuard

/-! Clean buffers conditional on play mode are sufficient: every region keeps
both mode bytes. This is the form supplied by `NoOverflow`, without assuming
that play mode has already been proved for the next state. -/
namespace Smb.Routine.PlayCycle
open Smb Smb.Abs Smb.Routine.FrameGuard

def CleanIf (s : NES) : Prop :=
  s.ram.get! 0x770 = 1 → s.ram.get! 0x772 = 3 → Clean PlayParser.G s

theorem modes_protected : configs.all (fun c =>
    c.protFn 0x770 && c.protFn 0x772) = true := by native_decide

theorem mode770 : (gAt PlayParser.G 0x770).elems == [1] := by native_decide
theorem mode772 : (gAt PlayParser.G 0x772).elems == [3] := by native_decide

/-- The shared globals allow every buffer offset permitted during play. -/
theorem buffer_limits :
    (List.range 256).all (fun n => !(decide (UInt8.ofNat n ≤ 0x34)) ||
      (gAt PlayParser.G 0x300).mem (UInt8.ofNat n)) = true ∧
    (List.range 256).all (fun n => !(decide (UInt8.ofNat n ≤ 0x21)) ||
      (gAt PlayParser.G 0x340).mem (UInt8.ofNat n)) = true := by native_decide

private theorem region_modes {r : Region} (hr : r ∈ regions) :
    r.prot 0x770 = true ∧ r.prot 0x772 = true := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp modes_protected c hc)

private theorem glob_at {s : NES}
    (h : SavedFInv (romOf Smb.prg) PlayParser.G regions (reg PlayFrame.Z) Saved s)
    (i : UInt16) (hi : i &&& 0x7FF = i) :
    (gAt PlayParser.G i).mem (s.ram.get! i.toNat) = true := by
  obtain ⟨_, _, r, _, ram0, ⟨t, _, ⟨b, _, hb⟩, hr⟩, _, _⟩ := h
  have he : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hr with hr | ⟨_, hr⟩
    · exact hr.ram i
    · exact hr.ram i
  rw [hi] at he
  rw [he]
  exact hb.glob i

theorem cleanIf_step (checks : Checks) (hp : PreambleChecks) {s : NES}
    (h : SavedFInv (romOf Smb.prg) PlayParser.G regions (reg PlayFrame.Z) Saved s)
    (hd : stop s.pc = false) (hus : s.unmodelled = false)
    (hu : (CPU.step.run s).2.unmodelled = false) (hc : CleanIf (CPU.step.run s).2) :
    SavedFInv (romOf Smb.prg) PlayParser.G regions (reg PlayFrame.Z) Saved (CPU.step.run s).2 := by
  apply (savedFinv_step_region (fits checks) (zfits hp) h hd hus hu ?_).2.1
  intro hk
  apply hc
  · have hkeep := hk 0x770 (fun r hr => (region_modes hr).1) (by decide)
    have hmode := elems_single mode770 (glob_at h 0x770 (by decide))
    exact hkeep.trans hmode
  · have hkeep := hk 0x772 (fun r hr => (region_modes hr).2) (by decide)
    have hmode := elems_single mode772 (glob_at h 0x772 (by decide))
    exact hkeep.trans hmode

/-- A run-level cycle invariant with conditional buffer cleanliness. -/
theorem cleanIf_invariant (checks : Checks) (hp : PreambleChecks) (n : Nat) (s : NES)
    (hd : ∀ i, i < n → stop (stepN i s).pc = false)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hc : ∀ i, i < n → CleanIf (stepN (i + 1) s))
    (h : SavedFInv (romOf Smb.prg) PlayParser.G regions (reg PlayFrame.Z) Saved s) :
    SavedFInv (romOf Smb.prg) PlayParser.G regions (reg PlayFrame.Z) Saved (stepN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    exact ih (CPU.step.run s).2 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hu (i + 1) (Nat.succ_le_succ hi))
      (fun i hi => hc (i + 1) (Nat.succ_lt_succ hi))
      (cleanIf_step checks hp h (hd 0 (Nat.succ_pos _))
        (hu 0 (Nat.zero_le _)) (hu 1 (by omega)) (hc 0 (Nat.succ_pos _)))

end Smb.Routine.PlayCycle
