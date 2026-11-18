import Smb.LocalBound.Range172

/-!
# Exactly three frames remain from one fixed full NES state

From `Smb.LocalBound.entry`, the complete state after the first 17,863 aligned
HappyLee inputs, every input list shorter than three fails to finish and remains
supported. Three neutral inputs finish and remain supported. All 256 controller-1
bytes are allowed, including Start, Select and Left+Right; controller 2 stays idle.

This is a fixed-entry result in the NES model, not a whole-run lower bound. It does
not show that every successful run visits this entry or cannot reach a better state
earlier. The endpoint is `Smb.finalVictory` at a model frame boundary, not an RTA
clock or the end of a movie's input. Physical NES equivalence is not established.

The generic bridge is kernel-checked without native evaluation. Its three finite
certificate premises use `native_decide`, so the closed theorem additionally trusts
the Lean compiler under the project's existing policy. Unsupported successors are
explicitly excluded by the conclusion; they are never treated as losing states.

This is an optional target. The range-module import chain serializes its expensive
checks. Keep it outside the default targets and `Smb.Routine.All`.
-/
namespace Smb.LocalBound

/-- The minimum remaining time from this exact entry is three supported model frames. -/
theorem exact_three :
    (∀ inputs : List UInt8, inputs.length < 3 →
      let s := NES.runFrames inputs entry;
      finalVictory s = false ∧ s.unmodelled = false) ∧
    (let s := NES.runFrames [0, 0, 0] entry;
      finalVictory s = true ∧ s.unmodelled = false) :=
  threeRangeBridge entry range0 range86 range172

end Smb.LocalBound
