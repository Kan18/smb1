import Smb.Routine.UnmodelledExec
import Smb.Routine.RunSteps
import Smb.Routine.FrameRun

/-! A supported final state certifies support throughout the preceding run.
This is error-flag monotonicity, not a theorem that gameplay stays supported. -/
namespace Smb.Sticky
open Smb.Abs Smb.Routine.RunSteps Smb.Routine.FrameRun

theorem stepN_clear (n : Nat) (s : NES) (h : (stepN n s).unmodelled = false) :
    s.unmodelled = false := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact step s (ih (CPU.step.run s).2 h)

theorem stepN_prefix_clear (n i : Nat) (s : NES) (hi : i ≤ n)
    (h : (stepN n s).unmodelled = false) : (stepN i s).unmodelled = false := by
  have he : n = i + (n - i) := by omega
  rw [he, stepN_add] at h
  exact stepN_clear (n - i) (stepN i s) h

theorem go_clear (n : Nat) (s : NES) (h : (NES.frame.go n s).unmodelled = false) :
    s.unmodelled = false := by
  induction n generalizing s with
  | zero => simp [NES.frame.go] at h
  | succ n ih =>
    by_cases hd : s.frameDone = true
    · simpa only [NES.frame.go, hd, ite_true] using h
    · simp only [NES.frame.go, hd, ite_false] at h
      exact step s (ih _ h)

theorem frame_clear (b0 b1 : UInt8) (s : NES)
    (h : (NES.frame b0 b1 s).unmodelled = false) : s.unmodelled = false :=
  go_clear NES.frameFuel (startFrame b0 b1 s) h

theorem runFrames_clear (inputs : List UInt8) (s : NES)
    (h : (NES.runFrames inputs s).unmodelled = false) : s.unmodelled = false := by
  induction inputs generalizing s with
  | nil => exact h
  | cons b l ih => exact frame_clear b 0 s (ih _ h)

theorem runFrames_append (pre inputs : List UInt8) (s : NES) :
    NES.runFrames (pre ++ inputs) s = NES.runFrames inputs (NES.runFrames pre s) := by
  induction pre generalizing s with
  | nil => rfl
  | cons b l ih => exact ih (NES.frame b 0 s)

theorem runFrames_prefix_clear (pre inputs : List UInt8) (s : NES)
    (h : (NES.runFrames (pre ++ inputs) s).unmodelled = false) :
    (NES.runFrames pre s).unmodelled = false := by
  rw [runFrames_append] at h
  exact runFrames_clear inputs _ h

/-- Once set, the unsupported-model flag remains set through any controller list. -/
theorem runFrames_sticky (inputs : List UInt8) (s : NES) (h : s.unmodelled = true) :
    (NES.runFrames inputs s).unmodelled = true := by
  cases hu : (NES.runFrames inputs s).unmodelled with
  | true => rfl
  | false =>
    have hs := runFrames_clear inputs s hu
    rw [h] at hs
    cases hs

end Smb.Sticky
