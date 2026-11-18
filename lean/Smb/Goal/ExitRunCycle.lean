import Smb.Goal.ExitRun
import Smb.Routine.FramesBound

/-!
# From the exit pipe to the pole, with the speed limit from the cycle

`exit_crossing` with `FrameLimited` replaced by the normal-play cycle (`FramesBound.frames_inv`): the 233 frames hold
for a run that meets the cycle's conditions from the pipe's exit, unless one of its frames is odd (a player call
still running at the frame's end, a second call, or a phase exit). The first 34 frames still follow the model on
the pipe's top (`Follows`), as in `exit_crossing`.
-/
namespace Smb.Goal.OneOne

open Smb.Routine (ramAt)
open Smb.LocalBound.HorizontalDistance
open Smb.Movement
open Smb.Routine.FramesBound Smb.Routine.PlayKeep Smb.Routine.PlayCycle
open Smb.Routine.HorizontalLimit (leftL)

theorem exit_crossing_cycle {inputs : List UInt8} {i j : Nat} (hij : i ≤ j) (hj : j ≤ inputs.length)
    (hcyc : CycleInv (at' inputs i)) (hpc : (at' inputs i).pc = 0x8057) (hus : (at' inputs i).unmodelled = false)
    (hH : XInvH (ramAt (at' inputs i)))
    (hno : NoOverflow (inputs.take j)) (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (Smb.Abs.stepN m (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (Smb.Abs.stepN k (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (Smb.Abs.stepN k (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f)))))
    (hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00)
    (hs : view exitMode (at' inputs i) = exitStart)
    (hm : ∀ f, i ≤ f → f < i + 34 → Follows exitMode inputs i f)
    (hd : pos (at' inputs i) + 137984 ≤ pos (at' inputs j)) :
    i + 233 ≤ j ∨ ∃ f, i ≤ f ∧ f < j ∧ ∃ J, at' inputs (f + 1) = Smb.Abs.stepN J (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f)) ∧
      Odd (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f)) J := by
  have hat := rest_of_idle hcyc hpc
  have hinv := frames_inv inputs i j hij hj hat hus hH hno hu hB hL
  -- Over the whole stretch, at least 216 frames, so past the first 34.
  rcases hinv (j - i) (by omega) with ⟨_, _, _, hb, _⟩ | ⟨f, hf1, hf2, h⟩
  · rw [show i + (j - i) = j by omega] at hb
    have hb' : pos (at' inputs j) ≤ pos (at' inputs i) + 640 * (j - i) := hb
    have h34 : i + 34 ≤ j := by omega
    rcases hinv 34 h34 with ⟨hat34, hus34, hH34, _, hL34⟩ | ⟨f, hf1, hf2, h⟩
    · -- From frame 34 on, the speed limit again, after the model's bound on the first 34.
      have h2 := exit_launch_bound hs hm
      rcases frames_bound inputs (i + 34) j h34 hj hat34 hus34 hH34
          hno hu (fun f h1 h2 => hB f (by omega) h2) (by omega) with
        h3 | ⟨f, hf1, hf2, h⟩
      · have h3' : pos (at' inputs j) ≤ pos (at' inputs (i + 34)) + 640 * (j - (i + 34)) := h3
        left; omega
      · exact Or.inr ⟨f, by omega, hf2, h⟩
    · exact Or.inr ⟨f, hf1, by omega, h⟩
  · exact Or.inr ⟨f, hf1, by omega, h⟩

end Smb.Goal.OneOne
