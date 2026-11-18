import Smb.Goal.StartRun

/-!
# From the exit pipe to the pole

The first 34 frames follow the model on the pipe's top, whose exact bound is `launch_exit`, and the rest use only the speed limit. That gives `X` 3155 no sooner than 233 frames after control, the frame the TAS gets there. `X` 3155 is where Mario can enter the pole's column, so this is the first part of the 240 frames to a low grab; `docs/lower-bound-1-1.md` has the rest.

`Follows` is a hypothesis, and here it asks more than at the start of the level: it's false for a run that goes back and touches the pipe's side, or walks off its left end, which the model leaves out. Those runs lose too much to matter, but aren't handled yet.
-/
namespace Smb.Goal.OneOne

open Smb.Movement
open Smb.Routine (ramAt)
open Smb.LocalBound.HorizontalDistance

theorem exit_launch_bound {inputs : List UInt8} {i : Nat} (hs : view exitMode (at' inputs i) = exitStart)
    (hm : ∀ f, i ≤ f → f < i + 34 → Follows exitMode inputs i f) :
    pos (at' inputs (i + 34)) ≤ pos (at' inputs i) + 11024 := by
  obtain ⟨l, hl, ha, _, h2⟩ := follows_run (m := exitMode) (inputs := inputs) (i := i) 34 (fun n hn => hm _ (by omega) (by omega))
  rw [hs] at ha h2
  have := launch_exit_bound l hl ha
  omega

/-- 539 pixels from the exit pipe's start takes 233 frames. -/
theorem exit_crossing {inputs : List UInt8} {i j : Nat} (hij : i ≤ j) (h0 : InWindow (ramAt (at' inputs i)))
    (hf : ∀ f, i ≤ f → f < j → FrameLimited inputs f) (hs : view exitMode (at' inputs i) = exitStart)
    (hm : ∀ f, i ≤ f → f < i + 34 → Follows exitMode inputs i f)
    (hd : pos (at' inputs i) + 137984 ≤ pos (at' inputs j)) : i + 233 ≤ j := by
  have h1 := speed_edge (speedLimited_of_frames hij h0 hf) hd
  have h2 := exit_launch_bound hs hm
  have hw : InWindow (ramAt (at' inputs (i + 34))) := (hf (i + 33) (by omega) (by omega)).2.1
  have h3 := pos_le_of_limited (inputs := inputs) (i := i + 34) (j := j) (by omega) hw (fun f h1' h2' => hf f (by omega) h2')
  omega

/-- The TAS gets there on exactly that frame. -/
theorem tas_crossing : pos (at' tasInputs 1047) + 137984 ≤ pos (at' tasInputs 1280) ∧ pos (at' tasInputs 1279) < pos (at' tasInputs 1047) + 137984 := by
  native_decide

/-- The model starts where the game does, on the TAS. -/
theorem tas_exit_start : view exitMode (at' tasInputs 1047) = exitStart := by native_decide

end Smb.Goal.OneOne
