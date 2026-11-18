import Smb.Game

/-!
# Reusing states at the start of a model frame

`NES.frame` replaces the old pad values, poll count and frame-done flag before
executing any instruction. Equality after precisely that update therefore
preserves every future common input continuation. RAM, controller history,
timing, open-bus state and supportedness are all retained.

These are generic equality proofs, with no replay or native computation.
They justify a comparison key and normalization at every frame boundary; they
do not certify a search's enumeration or reported number of distinct states.
-/
namespace Smb.FrameReuse

/-- Exactly the record update at the entry to `NES.frame`. -/
def prepare (pad0 pad1 : UInt8) (s : NES) : NES :=
  { s with pad0, pad1, polls := 0, frameDone := false }

/-- A representative for comparison before assigning the next frame's inputs. -/
def canonical (s : NES) : NES := prepare 0 0 s

theorem frame_congr (pad0 pad1 : UInt8) (s t : NES)
    (h : prepare pad0 pad1 s = prepare pad0 pad1 t) :
    NES.frame pad0 pad1 s = NES.frame pad0 pad1 t :=
  congrArg (NES.frame.go NES.frameFuel) h

theorem canonical_frame_congr (s t : NES) (h : canonical s = canonical t)
    (pad0 pad1 : UInt8) : NES.frame pad0 pad1 s = NES.frame pad0 pad1 t := by
  apply frame_congr pad0 pad1 s t
  simpa only [canonical, prepare] using congrArg (prepare pad0 pad1) h

/-- A nonempty common continuation gives equal complete states. -/
theorem canonical_nonempty_states (s t : NES) (h : canonical s = canonical t)
    (inputs : List UInt8) (hn : inputs ≠ []) :
    NES.runFrames inputs s = NES.runFrames inputs t := by
  cases inputs with
  | nil => exact False.elim (hn rfl)
  | cons a rest =>
    change NES.runFrames rest (NES.frame a 0 s) = NES.runFrames rest (NES.frame a 0 t)
    rw [canonical_frame_congr s t h a 0]

/-- Every common suffix, including empty, has equal finish and unsupported flags.
This does not assert that future execution stays supported. -/
theorem canonical_all_outcomes (s t : NES) (h : canonical s = canonical t)
    (inputs : List UInt8) :
    finalVictory (NES.runFrames inputs s) = finalVictory (NES.runFrames inputs t) ∧
    (NES.runFrames inputs s).unmodelled = (NES.runFrames inputs t).unmodelled := by
  cases inputs with
  | nil =>
    constructor
    · simpa only [NES.runFrames, List.foldl_nil, canonical, prepare, finalVictory, operMode]
        using congrArg finalVictory h
    · simpa only [NES.runFrames, List.foldl_nil, canonical, prepare]
        using congrArg NES.unmodelled h
  | cons a rest =>
    rw [canonical_nonempty_states s t h (a :: rest) (List.cons_ne_nil a rest)]
    exact ⟨rfl, rfl⟩

/-- Replacing the frame-entry fields does not change the next complete state. -/
theorem frame_after_canonical (pad0 pad1 : UInt8) (s : NES) :
    NES.frame pad0 pad1 (canonical s) = NES.frame pad0 pad1 s :=
  canonical_frame_congr (canonical s) s rfl pad0 pad1

/-- Execute a fixed input sequence while normalizing at every frame boundary. -/
def runCanonical (inputs : List UInt8) (s : NES) : NES :=
  inputs.foldl (fun state pad => canonical (NES.frame pad 0 state)) (canonical s)

/-- Repeated normalization agrees with one normalization after ordinary execution. -/
theorem runCanonical_eq (inputs : List UInt8) (s : NES) :
    runCanonical inputs s = canonical (NES.runFrames inputs s) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons pad rest ih =>
    change runCanonical rest (NES.frame pad 0 (canonical s)) =
      canonical (NES.runFrames rest (NES.frame pad 0 s))
    rw [ih, frame_after_canonical]

/-- Every-boundary normalization preserves victory and unsupported outcomes,
including for an empty input sequence. No reachability or support premise is needed. -/
theorem runCanonical_outcomes (inputs : List UInt8) (s : NES) :
    finalVictory (runCanonical inputs s) = finalVictory (NES.runFrames inputs s) ∧
    (runCanonical inputs s).unmodelled = (NES.runFrames inputs s).unmodelled := by
  rw [runCanonical_eq]
  exact ⟨rfl, rfl⟩

end Smb.FrameReuse
