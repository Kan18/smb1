import Smb.Routine.PlayCycle
import Smb.Routine.FrameRun

/-! Carry the saved normal-play invariant across actual controller changes and
frame boundaries. Initial entry, supported execution, clean buffers, and avoidance
of the explicitly listed open exits remain hypotheses. -/
namespace Smb.Routine.FrameRun
open Smb NES Smb.Abs Smb.Routine.PpuFrame Smb.Routine.FrameGuard

theorem savedFinv_start {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region}
    {saved : Region → (UInt16 → UInt8) → Prop} {s : NES} (p0 p1 : UInt8)
    (h : SavedFInv rom g rs Z saved s) : SavedFInv rom g rs Z saved (startFrame p0 p1 s) := by
  obtain ⟨hS, hP, r, hr, ram0, ⟨t, hc, hinv, hrel⟩, hsaved, hz⟩ := h
  refine ⟨Sch.of_sv hS ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩,
    hP, r, hr, ram0, ⟨t, hc, hinv, ?_⟩, hsaved, fun e => ?_⟩
  · rcases hrel with h1 | ⟨h2, h3⟩
    · exact Or.inl (RelD_start p0 p1 h1)
    · exact Or.inr ⟨h2, RelOn_start p0 p1 h3⟩
  · rcases hz e with h1 | h1
    · exact Or.inl (ZStage_start p0 p1 h1)
    · exact Or.inr h1

end Smb.Routine.FrameRun

namespace Smb.Routine.PlayCycle
open Smb Smb.Abs Smb.Routine.FrameGuard Smb.Routine.FrameRun

abbrev CycleInv (s : NES) : Prop :=
  SavedFInv (romOf Smb.prg) PlayParser.G regions (reg PlayFrame.Z) Saved s

/-- Instruction conditions until this frame's loop finishes. -/
def CycleGoClear : Nat → NES → Prop
  | 0, _ => True
  | n + 1, s => s.frameDone = true ∨
    (stop s.pc = false ∧ (CPU.step.run s).2.unmodelled = false ∧
      CleanIf (CPU.step.run s).2 ∧ CycleGoClear n (CPU.step.run s).2)

theorem cycle_go (n : Nat) (s : NES) (h : CycleInv s) (hus : s.unmodelled = false)
    (hc : CycleGoClear n s) (hgo : (NES.frame.go n s).unmodelled = false) :
    CycleInv (NES.frame.go n s) := by
  induction n generalizing s with
  | zero => simp [NES.frame.go] at hgo
  | succ n ih =>
    simp only [NES.frame.go] at hgo ⊢
    split
    · exact h
    · rename_i hfd
      simp only [hfd, if_false] at hgo
      rcases hc with hd | ⟨hd, hu, hA, hc⟩
      · exact absurd hd hfd
      · exact ih _ (cleanIf_step checked preambles_checked h hd hus hu hA) hu hc hgo

/-- Conditions on the actual frame loop for each controller byte. -/
def CycleRunClear : List UInt8 → NES → Prop
  | [], _ => True
  | b :: l, s => CycleGoClear NES.frameFuel (startFrame b 0 s) ∧
      (NES.frame b 0 s).unmodelled = false ∧ CycleRunClear l (NES.frame b 0 s)

/-- The checked cycle across a list of arbitrary controller bytes, under its
explicit run conditions. This is not a reset-to-exit or timing bound. -/
theorem normal_play_frames (inputs : List UInt8) (s : NES) (h : CycleInv s)
    (hus : s.unmodelled = false) (hc : CycleRunClear inputs s) :
    CycleInv (NES.runFrames inputs s) := by
  induction inputs generalizing s with
  | nil => exact h
  | cons b l ih =>
    obtain ⟨h1, h2, h3⟩ := hc
    exact ih _ (cycle_go _ _ (savedFinv_start b 0 h) hus h1 h2) h2 h3

end Smb.Routine.PlayCycle
