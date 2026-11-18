import Smb.Goal.LaunchRun
import Smb.Routine.FramesBound

/-!
# From the start to the pipe, with the speed limit from the cycle after the launch

`pipe_368'` with `FrameLimited` asked only of the launch's first 33 frames, which `launch_bound'` needs; past them the
speed limit comes from the normal-play cycle (`FramesBound.frames_inv`), unless one of the frames is odd (a player
call still running at the frame's end, a second call, or a phase exit).
-/
namespace Smb.Goal.OneOne

open Smb.Abs Smb.Abs.LaunchPhase
open Smb.Movement
open Smb.Routine (ramAt)
open Smb.LocalBound.HorizontalDistance
open Smb.Routine.FramesBound Smb.Routine.PlayKeep Smb.Routine.PlayCycle
open Smb.Routine.HorizontalLimit (leftL)

/-- At control, the launch's bounds put the screen's left edge at 0 and Mario on it, at most `$4F` pixels in: `XInvH`. -/
theorem xinvH_of_lstate {inputs : List UInt8} {i : Nat} (hS : LState inputs i) :
    XInvH (ramAt (at' inputs i)) ∧ leftL (ramAt (at' inputs i)) = 0 := by
  have hc := lcells (Smb.Routine.LaunchPhase.glob_of_finv hS.inv)
  have hx := hc.x
  refine ⟨⟨hS.speed, ?_, hc.plat, Or.inl ?_⟩, ?_⟩
  · simp only [Smb.Routine.HorizontalLimit.edgeR, leftL, Smb.Routine.pos16, hc.l1, hc.l2, hc.r1, hc.r2]; decide
  · simp only [Smb.Routine.HorizontalLimit.pixelP, leftL, Smb.Routine.pos16, hc.l1, hc.l2, hc.page]
    generalize ramAt (at' inputs i) 0x86 = X at *
    bv_decide (config := { enums := false })
  · simp only [leftL, Smb.Routine.pos16, hc.l1, hc.l2]; decide

theorem pipe_368_cycle {inputs : List UInt8} {i j : Nat} (hij : i ≤ j) (hj : j ≤ inputs.length)
    (hf : ∀ f, i ≤ f → f < i + 33 → FrameLimited inputs f) (hS : LState inputs i)
    (hs : view openGround (at' inputs i) = start) (hp : pos (at' inputs i) = 40 * 256)
    (hok : ∀ f, i ≤ f → f < i + 32 → FrameOk inputs f) (hn : NoOverflow (inputs.take j))
    (hcyc : CycleInv (at' inputs i)) (hus : (at' inputs i).unmodelled = false)
    (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (Smb.Abs.stepN m (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (Smb.Abs.stepN k (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (Smb.Abs.stepN k (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f)))))
    (hjh : j < horizon)
    (hd : pos (at' inputs i) + 224256 ≤ pos (at' inputs j)) :
    i + 368 ≤ j ∨ ∃ f, i ≤ f ∧ f < j ∧ ∃ J, at' inputs (f + 1) = Smb.Abs.stepN J (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f)) ∧
      Odd (Smb.Routine.FrameRun.startFrame inputs[f]! 0 (at' inputs f)) J := by
  have hat := rest_of_idle hcyc hS.pc
  obtain ⟨hH, hl0⟩ := xinvH_of_lstate hS
  have hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00 := by
    rw [hl0]; simp only [horizon] at hjh; simp; omega
  have hinv := frames_inv inputs i j hij hj hat hus hH hn hu hB hL
  rcases hinv (j - i) (by omega) with ⟨_, _, _, hb, _⟩ | ⟨f, hf1, hf2, h⟩
  · rw [show i + (j - i) = j by omega] at hb
    have hb' : pos (at' inputs j) ≤ pos (at' inputs i) + 640 * (j - i) := hb
    have h33 : i + 33 ≤ j := by omega
    have h2 := launch_bound' (window_of hH (by omega)) hf hS hs hp hok (fun f _ h2' hl => goClean_at hn (by omega) hl)
    rcases hinv 33 h33 with ⟨hat33, hus33, hH33, _, hL33⟩ | ⟨f, hf1, hf2, h⟩
    · rcases frames_bound inputs (i + 33) j h33 hj hat33 hus33 hH33
          hn hu (fun f h1 h2 => hB f (by omega) h2) (by omega) with
        h3 | ⟨f, hf1, hf2, h⟩
      · have h3' : pos (at' inputs j) ≤ pos (at' inputs (i + 33)) + 640 * (j - (i + 33)) := h3
        left; omega
      · exact Or.inr ⟨f, by omega, hf2, h⟩
    · exact Or.inr ⟨f, hf1, by omega, h⟩
  · exact Or.inr ⟨f, hf1, by omega, h⟩

end Smb.Goal.OneOne
