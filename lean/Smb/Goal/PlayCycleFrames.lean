import Smb.Goal.PlayCycle
import Smb.Routine.PlayCycleFrames

/-! Connect the normal-play frame invariant to the actual `runClean` predicate.
Supported execution and avoidance of open exits remain separate assumptions. -/
namespace Smb.Goal.OneOne
open Smb Smb.Routine.PlayCycle

def CycleSafeGo : Nat → NES → Prop
  | 0, _ => True
  | n + 1, s => s.frameDone = true ∨
    (stop s.pc = false ∧ (CPU.step.run s).2.unmodelled = false ∧
      CycleSafeGo n (CPU.step.run s).2)

def CycleSafeRun : List UInt8 → NES → Prop
  | [], _ => True
  | b :: l, s => CycleSafeGo NES.frameFuel (startFrame b s) ∧
      (NES.frame b 0 s).unmodelled = false ∧ CycleSafeRun l (NES.frame b 0 s)

theorem cycleGoClear_of_clean (n : Nat) (s : NES)
    (hc : goClean n s = true) (hs : CycleSafeGo n s) : CycleGoClear n s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    by_cases hf : s.frameDone = true
    · exact Or.inl hf
    · have hf' : s.frameDone = false := Bool.eq_false_iff.mpr hf
      rcases hs with h | ⟨hd, hu, hs⟩
      · exact (hf h).elim
      · simp only [goClean, hf', Bool.false_or, Bool.and_eq_true] at hc
        exact Or.inr ⟨hd, hu, play_cleanIf_of_cleanAt hc.1, ih _ hc.2 hs⟩

theorem cycleRunClear_of_clean (inputs : List UInt8) (s : NES)
    (hc : runClean inputs s = true) (hs : CycleSafeRun inputs s) : CycleRunClear inputs s := by
  induction inputs generalizing s with
  | nil => trivial
  | cons b l ih =>
    simp only [runClean, Bool.and_eq_true] at hc
    obtain ⟨h1, h2, h3⟩ := hs
    exact ⟨cycleGoClear_of_clean _ _ hc.1.2 h1, h2, ih _ hc.2 h3⟩

/-- The normal-play invariant across real frames of a clean run. -/
theorem normal_play_clean_frames (inputs : List UInt8) (s : NES)
    (h : CycleInv s) (hu : s.unmodelled = false)
    (hc : runClean inputs s = true) (hs : CycleSafeRun inputs s) :
    CycleInv (NES.runFrames inputs s) :=
  normal_play_frames inputs s h hu (cycleRunClear_of_clean inputs s hc hs)

/-- A clean run supplies cleanliness to its suffix, at the actual reached state. -/
theorem runClean_suffix (pre suffix : List UInt8) (s : NES)
    (h : runClean (pre ++ suffix) s = true) :
    runClean suffix (NES.runFrames pre s) = true := by
  induction pre generalizing s with
  | nil => exact h
  | cons b l ih =>
    simp only [List.cons_append, runClean, Bool.and_eq_true] at h
    exact ih _ h.2

/-- `NoOverflow` from reset supplies the buffer assumption after any prefix.
Entry into the cycle, supported execution and open-exit exclusion are explicit. -/
theorem normal_play_after_prefix (pre inputs : List UInt8)
    (hn : NoOverflow (pre ++ inputs))
    (h : CycleInv (NES.runFrames pre initial))
    (hu : (NES.runFrames pre initial).unmodelled = false)
    (hs : CycleSafeRun inputs (NES.runFrames pre initial)) :
    CycleInv (NES.runFrames inputs (NES.runFrames pre initial)) :=
  normal_play_clean_frames inputs _ h hu (runClean_suffix pre inputs initial hn) hs

end Smb.Goal.OneOne
