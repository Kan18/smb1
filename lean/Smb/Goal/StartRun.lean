import Smb.Goal.OneOne
import Smb.Movement.LaunchCheck

/-!
# The start of 1-1, from the movement model

From control to the first pipe. The first 33 frames follow `Smb.Movement`'s model, whose exact bound `launch_33` is, and the other frames use only the speed limit. Together they make the edge's weight 368, which the TAS meets.

Near the screen's left edge the game clamps the position, and the model doesn't. So `Follows` is only asked of frames at most 28 pixels behind the start, and a run that drops further back has lost too much to matter: `pipe_368` handles it with the speed limit alone.

`Follows` and the start's state are hypotheses here.
-/
namespace Smb.Goal.OneOne

open Smb.Movement
open Smb.Routine (ramAt)
open Smb.Routine.HorizontalLimit (phi XStep)
open Smb.LocalBound.HorizontalDistance

/-- The cells the model describes. -/
def stateOf (s : NES) : S :=
  { v := byte s 0x57, f := byte s 0x705, abs := byte s 0x700, face := byte s 0x33, move := byte s 0x45, st := byte s 0x1D,
    t783 := byte s 0x783, r703 := byte s 0x703, y := byte s 0xCE, ysub := byte s 0x416, vy := byte s 0x9F, vf := byte s 0x433,
    g := byte s 0x709, gfall := byte s 0x70A, y0 := byte s 0x708, rise := byte s 0x706, prevA := byte s 0x0D &&& 0x80 }

def view (m : Mode) (s : NES) : S := norm m (stateOf s)

/-- This frame is one of the model's in mode `m`, for a stretch from frame `i`, for some input: it needn't be the pad's byte, since a held Select or Start only reaches `$6FC` on its first frame. -/
def Follows (m : Mode) (inputs : List UInt8) (i f : Nat) : Prop :=
  ∃ o : Frame, o.allowed m (view m (at' inputs f)) ((pos (at' inputs f) : Int) - pos (at' inputs i)) ∧
    view m (at' inputs (f + 1)) = nextS m o (view m (at' inputs f)) ∧
    (pos (at' inputs (f + 1)) : Int) = pos (at' inputs f) + delta m o (view m (at' inputs f))

/-- A stretch of frames that follow the model is one of its runs. -/
theorem follows_run {m : Mode} {inputs : List UInt8} {i : Nat} (k : Nat) (h : ∀ n, n < k → Follows m inputs i (i + n)) :
    ∃ l : List Frame, l.length = k ∧ RunOk m l (view m (at' inputs i)) 0 ∧ (run m l (view m (at' inputs i)) 0).1 = view m (at' inputs (i + k)) ∧
      (pos (at' inputs i) : Int) + (run m l (view m (at' inputs i)) 0).2 = pos (at' inputs (i + k)) := by
  induction k with
  | zero => exact ⟨[], rfl, trivial, rfl, by simp [run]⟩
  | succ k ih =>
    obtain ⟨l, hl, ha, h1, h2⟩ := ih (fun n hn => h n (by omega))
    obtain ⟨o, h0, h3, h4⟩ := h k (by omega)
    refine ⟨l ++ [o], by simp [hl], ?_, ?_, ?_⟩
    · refine runOk_append _ _ _ _ 0 ha ?_
      have h5 : (run m l (view m (at' inputs i)) 0).2 = (pos (at' inputs (i + k)) : Int) - pos (at' inputs i) := by omega
      rw [h1, h5]
      exact ⟨h0, trivial⟩
    · simp only [run_append, run, h1]
      exact h3.symm
    · simp only [run_append, run, h1]
      have h5 : (pos (at' inputs (i + (k + 1))) : Int) = pos (at' inputs (i + k)) + delta m o (view m (at' inputs (i + k))) := h4
      omega

/-- The speed limit, as a bound on the position. -/
theorem pos_le_of_limited {inputs : List UInt8} {i j : Nat} (hij : i ≤ j) (h0 : InWindow (ramAt (at' inputs i)))
    (h : ∀ f, i ≤ f → f < j → FrameLimited inputs f) : pos (at' inputs j) ≤ pos (at' inputs i) + 640 * (j - i) := by
  have hs := speedLimited_of_frames hij h0 h
  by_cases hc : pos (at' inputs i) ≤ pos (at' inputs j)
  · have := speed_edge (D := pos (at' inputs j) - pos (at' inputs i)) hs (by omega)
    omega
  · omega

theorem exists_first {P : Nat → Prop} (n : Nat) (h : ∃ m, m ≤ n ∧ P m) : ∃ m, m ≤ n ∧ P m ∧ ∀ k, k < m → ¬ P k := by
  induction n with
  | zero =>
    obtain ⟨m, h1, h2⟩ := h
    exact ⟨m, h1, h2, fun k hk => by omega⟩
  | succ n ih =>
    by_cases hc : ∃ m, m ≤ n ∧ P m
    · obtain ⟨m, h1, h2, h3⟩ := ih hc
      exact ⟨m, by omega, h2, h3⟩
    · obtain ⟨m, h1, h2⟩ := h
      refine ⟨m, h1, h2, fun k hk hp => hc ⟨k, ?_, hp⟩⟩
      have : m ≠ n + 1 ∨ m = n + 1 := by omega
      rcases this with h3 | h3
      · exact absurd ⟨m, by omega, h2⟩ hc
      · omega

/-- At most 40.5625 pixels in 33 frames, whatever the inputs, with `Follows` asked only away from the screen's edge. -/
theorem launch_bound {inputs : List UInt8} {i : Nat} (h0 : InWindow (ramAt (at' inputs i)))
    (hf : ∀ f, i ≤ f → f < i + 33 → FrameLimited inputs f) (hs : view openGround (at' inputs i) = start)
    (hm : ∀ f, i ≤ f → f < i + 33 → pos (at' inputs i) ≤ pos (at' inputs f) + 7168 → Follows openGround inputs i f) :
    pos (at' inputs (i + 33)) ≤ pos (at' inputs i) + 10384 := by
  by_cases hall : ∀ m, m < 33 → pos (at' inputs i) ≤ pos (at' inputs (i + m)) + 7168
  · obtain ⟨l, hl, ha, _, h2⟩ := follows_run (inputs := inputs) (i := i) 33 (fun m hm' => hm _ (by omega) (by omega) (hall m hm'))
    rw [hs] at ha h2
    have := launch_33_bound l hl ha
    omega
  · have hex : ∃ m, m ≤ 33 ∧ m < 33 ∧ ¬ pos (at' inputs i) ≤ pos (at' inputs (i + m)) + 7168 := by
      simp only [Classical.not_forall] at hall
      obtain ⟨m, hm1, hm2⟩ := hall
      exact ⟨m, by omega, hm1, hm2⟩
    obtain ⟨m, _, ⟨hm1, hm2⟩, hmin⟩ := exists_first 33 hex
    have hb : ∀ n, n < m → pos (at' inputs i) ≤ pos (at' inputs (i + n)) + 7168 := by
      intro n hn
      by_cases hc : pos (at' inputs i) ≤ pos (at' inputs (i + n)) + 7168
      · exact hc
      · exact absurd ⟨by omega, hc⟩ (hmin n hn)
    obtain ⟨l, hl, _, _, h2⟩ := follows_run (inputs := inputs) (i := i) m (fun n hn => hm _ (by omega) (by omega) (hb n hn))
    have hv : speedOk (view openGround (at' inputs i)).v = true := by
      rw [hs]
      decide
    have h3 := (run_le openGround l _ 0 hv).2
    rw [hl] at h3
    have hw : InWindow (ramAt (at' inputs (i + m))) := by
      cases m with
      | zero => exact h0
      | succ m => exact (hf (i + m) (by omega) (by omega)).2.1
    have h4 := pos_le_of_limited (inputs := inputs) (i := i + m) (j := i + 33) (by omega) hw (fun f h1 h2 => hf f (by omega) h2)
    have h5 : i + 33 - (i + m) = 33 - m := by omega
    rw [h5] at h4
    omega

/-- From a start to a pipe at least 876 pixels on takes 368 frames: 33 from the launch, and 335 at the speed limit for the rest. -/
theorem pipe_368 {inputs : List UInt8} {i j : Nat} (hij : i ≤ j) (h0 : InWindow (ramAt (at' inputs i)))
    (hf : ∀ f, i ≤ f → f < j → FrameLimited inputs f) (hs : view openGround (at' inputs i) = start)
    (hm : ∀ f, i ≤ f → f < i + 33 → pos (at' inputs i) ≤ pos (at' inputs f) + 7168 → Follows openGround inputs i f)
    (hd : pos (at' inputs i) + 224256 ≤ pos (at' inputs j)) : i + 368 ≤ j := by
  have h1 := speed_edge (speedLimited_of_frames hij h0 hf) hd
  have h2 := launch_bound h0 (fun f h1' h2' => hf f h1' (by omega)) hs hm
  have hw : InWindow (ramAt (at' inputs (i + 33))) := (hf (i + 32) (by omega) (by omega)).2.1
  have h3 := pos_le_of_limited (inputs := inputs) (i := i + 33) (j := j) (by omega) hw (fun f h1' h2' => hf f (by omega) h2')
  omega

end Smb.Goal.OneOne
