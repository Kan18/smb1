import Smb.Movement.Launch

namespace Smb.Movement

theorem launch_33 : verified openGround starts (40 * 256 + 0x90) 33 = true := by native_decide

/-- From the start, no run gets further in 33 frames than 40.5625 pixels. -/
theorem launch_33_bound (l : List Frame) (hl : l.length = 33) (ha : RunOk openGround l start 0) :
    (run openGround l start 0).2 ≤ 40 * 256 + 0x90 :=
  verified_sound _ _ _ _ launch_33 l hl (start, 0) (by simp [starts]) ha

theorem launch_31 : verified openGround starts (35 * 256 + 0x90) 31 = true := by native_decide

theorem launch_32 : verified openGround starts (38 * 256 + 0x10) 32 = true := by native_decide

/-- Waiting out the frames left over changes nothing. -/
theorem run_stills (m : Mode) (k : Nat) (s : S) (p : Int) : RunOk m (List.replicate k Frame.still) s p ∧ run m (List.replicate k Frame.still) s p = (s, p) := by
  induction k with
  | zero => exact ⟨trivial, rfl⟩
  | succ k ih =>
    refine ⟨⟨trivial, ?_⟩, ?_⟩
    · simpa [nextS, delta] using ih.1
    · simpa [List.replicate_succ, run, nextS, delta] using ih.2

/-- From the start, no run of at most 31 frames gets further than 35.5625 pixels. -/
theorem launch_31_le (l : List Frame) (hl : l.length ≤ 31) (ha : RunOk openGround l start 0) :
    (run openGround l start 0).2 ≤ 35 * 256 + 0x90 := by
  have hs := run_stills openGround (31 - l.length) (run openGround l start 0).1 (run openGround l start 0).2
  have h := verified_sound _ _ _ _ launch_31 (l ++ List.replicate (31 - l.length) Frame.still) (by simp; omega) (start, 0) (by simp [starts])
    (runOk_append _ _ _ _ _ ha hs.1)
  simp only [run_append] at h
  rw [hs.2] at h
  exact h

/-- From the start, no run gets further in 32 frames than 38.0625 pixels. -/
theorem launch_32_bound (l : List Frame) (hl : l.length = 32) (ha : RunOk openGround l start 0) :
    (run openGround l start 0).2 ≤ 38 * 256 + 0x10 :=
  verified_sound _ _ _ _ launch_32 l hl (start, 0) (by simp [starts]) ha

/-- The exit pipe's top, which ends 21 pixels on at `X` 2637, over the floor. -/
def exitMode : Mode := ⟨144, 176, 21 * 256, true⟩

/-- Mario at the first frame of control on top of the exit pipe. -/
def exitStart : S :=
  { start with y := 144, gfall := 0x28 }

theorem launch_exit : verified exitMode #[(exitStart, 0)] (43 * 256 + 0x10) 34 = true := by native_decide

/-- From the exit pipe's top, no run gets further in 34 frames than 43.0625 pixels. -/
theorem launch_exit_bound (l : List Frame) (hl : l.length = 34) (ha : RunOk exitMode l exitStart 0) :
    (run exitMode l exitStart 0).2 ≤ 43 * 256 + 0x10 :=
  verified_sound _ _ _ _ launch_exit l hl (exitStart, 0) (by simp) ha

end Smb.Movement
