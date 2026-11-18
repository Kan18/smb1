import Smb.Goal.PlayCycleFacts
import Smb.Routine.UnmodelledRun

/-! For supported runs, only avoidance of the explicit open phase exits is
needed in addition to entry into the cycle and the goal's buffer assumption. -/
namespace Smb.Goal.OneOne
open Smb Smb.Routine.PlayCycle

/-- The instructions actually executed before frame completion avoid open exits. -/
def CycleClosedGo : Nat → NES → Prop
  | 0, _ => True
  | n + 1, s => s.frameDone = true ∨
      (stop s.pc = false ∧ CycleClosedGo n (CPU.step.run s).2)

def CycleClosedRun : List UInt8 → NES → Prop
  | [], _ => True
  | b :: l, s => CycleClosedGo NES.frameFuel (startFrame b s) ∧
      CycleClosedRun l (NES.frame b 0 s)

theorem cycleSafeGo_of_supported (n : Nat) (s : NES)
    (hu : (NES.frame.go n s).unmodelled = false) (hc : CycleClosedGo n s) :
    CycleSafeGo n s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    by_cases hd : s.frameDone = true
    · exact Or.inl hd
    · rcases hc with hf | ⟨hc, ht⟩
      · exact (hd hf).elim
      · simp only [NES.frame.go, hd, ite_false] at hu
        exact Or.inr ⟨hc, Sticky.go_clear n _ hu, ih _ hu ht⟩

theorem cycleSafeRun_of_supported (inputs : List UInt8) (s : NES)
    (hu : (NES.runFrames inputs s).unmodelled = false) (hc : CycleClosedRun inputs s) :
    CycleSafeRun inputs s := by
  induction inputs generalizing s with
  | nil => trivial
  | cons b l ih =>
    obtain ⟨hc, ht⟩ := hc
    have hf := Sticky.runFrames_clear l (NES.frame b 0 s) hu
    exact ⟨cycleSafeGo_of_supported _ _ hf hc, hf, ih _ hu ht⟩

/-- The final support check implies every intermediate support premise. -/
theorem supported_normal_play_suffix (pre inputs : List UInt8)
    (hn : NoOverflow (pre ++ inputs))
    (h : CycleInv (NES.runFrames pre initial))
    (hu : (NES.runFrames (pre ++ inputs) initial).unmodelled = false)
    (hc : CycleClosedRun inputs (NES.runFrames pre initial)) :
    CycleInv (NES.runFrames (pre ++ inputs) initial) ∧
      left (NES.runFrames (pre ++ inputs) initial) = false := by
  rw [Sticky.runFrames_append] at hu ⊢
  have hi := normal_play_after_prefix pre inputs hn h (Sticky.runFrames_clear inputs _ hu)
    (cycleSafeRun_of_supported inputs _ hu hc)
  exact ⟨hi, cycle_not_left hi⟩

end Smb.Goal.OneOne
