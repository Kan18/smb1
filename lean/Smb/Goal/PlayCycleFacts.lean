import Smb.Goal.PlayCycleFrames
import Smb.Routine.RunSteps

/-! Observable consequences of the checked normal-play invariant. These are
conditional on reaching and remaining in the cycle, not a reset-to-exit bound. -/
namespace Smb.Goal.OneOne
open Smb Smb.Abs Smb.Routine.PlayCycle

/-- Every shared RAM bound holds in the concrete NES state, including during
PPU bookkeeping and the closing region's NMI preamble. -/
theorem cycle_global {s : NES} (h : CycleInv s) (i : UInt16)
    (hi : i &&& 0x7FF = i) :
    (gAt Smb.Abs.PlayParser.G i).mem (s.ram.get! i.toNat) = true := by
  obtain ⟨_, _, r, _, ram0, ⟨t, _, ⟨b, _, hb⟩, hr⟩, _, _⟩ := h
  have he : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hr with hr | ⟨_, hr⟩
    · exact hr.ram i
    · exact hr.ram i
  rw [hi] at he
  rw [he]
  exact hb.glob i

private theorem world_bound : (gAt Smb.Abs.PlayParser.G 0x75F).elems == [0] := by native_decide
private theorem level_bound : (gAt Smb.Abs.PlayParser.G 0x75C).elems == [0] := by native_decide

/-- A state inside the checked normal-play invariant has not left 1-1. -/
theorem cycle_not_left {s : NES} (h : CycleInv s) : left s = false := by
  have hw := elems_single world_bound (cycle_global h 0x75F (by decide))
  have hl := elems_single level_bound (cycle_global h 0x75C (by decide))
  change s.ram.get! 0x75F = 0 at hw
  change s.ram.get! 0x75C = 0 at hl
  simp [left, byte, hw, hl]

/-- Any exit after a known cycle entry must violate one of the explicit
run conditions (supported instructions or avoidance of the open phase exits). -/
theorem normal_play_suffix_not_left (pre inputs : List UInt8)
    (hn : NoOverflow (pre ++ inputs))
    (h : CycleInv (NES.runFrames pre initial))
    (hu : (NES.runFrames pre initial).unmodelled = false)
    (hs : CycleSafeRun inputs (NES.runFrames pre initial)) :
    left (NES.runFrames inputs (NES.runFrames pre initial)) = false :=
  cycle_not_left (normal_play_after_prefix pre inputs hn h hu hs)

/-- Leaving 1-1 from a known normal-cycle state requires reaching one of the
listed open exits first. The checked invariant still holds at that first exit,
so its global and saved-entry facts are available to the next phase proof. -/
theorem leaving_crosses_open_exit (n : Nat) (s : NES) (h : CycleInv s)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hc : ∀ i, i < n → CleanIf (stepN (i + 1) s))
    (hl : left (stepN n s) = true) :
    ∃ k, k < n ∧ (stepN k s).pc ∈ openExits ∧ CycleInv (stepN k s) ∧
      ∀ i, i < k → stop (stepN i s).pc = false := by
  rcases Smb.Routine.RunSteps.first_hit (fun t => stop t.pc) n s with hd | ⟨k, hk, hs, hd⟩
  · have hi := normal_play_run n s (fun i hi => hd i (Nat.le_of_lt hi)) hu hc h
    have hf := cycle_not_left hi
    rw [hl] at hf
    cases hf
  · have hi := normal_play_run k s hd (fun i hi => hu i (Nat.le_trans hi hk))
      (fun i hi => hc i (Nat.lt_of_lt_of_le hi hk)) h
    have hkn : k < n := by
      rcases Nat.lt_or_eq_of_le hk with hk | rfl
      · exact hk
      · have hf := cycle_not_left hi
        rw [hl] at hf
        cases hf
    exact ⟨k, hkn, List.contains_iff_mem.mp hs, hi, hd⟩

end Smb.Goal.OneOne
