import Smb.Routine.FrameGuard

/-!
# Runs as instruction counts

`NES.frame.go` and `CPU.runTo` both run instructions until something comes up. Each is `stepN` for some count, so what's proved along `stepN` applies to both.
-/
namespace Smb.Routine.RunSteps
open Smb NES Smb.Abs Smb.Routine.FrameGuard

theorem stepN_succ (n : Nat) (s : NES) : stepN (n + 1) s = (CPU.step.run (stepN n s)).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (CPU.step.run s).2

theorem stepN_add (a b : Nat) (s : NES) : stepN (a + b) s = stepN b (stepN a s) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, stepN_succ, stepN_succ, ih]

/-- A frame's loop runs up to the instruction that ends the frame. -/
theorem go_stepN (n : Nat) (s : NES) (h : (NES.frame.go n s).unmodelled = false) :
    ∃ j, NES.frame.go n s = stepN j s ∧ (stepN j s).frameDone = true ∧ ∀ i, i < j → (stepN i s).frameDone = false := by
  induction n generalizing s with
  | zero => simp [NES.frame.go] at h
  | succ n ih =>
    simp only [NES.frame.go] at h ⊢
    by_cases hd : s.frameDone = true
    · simp only [hd, ite_true]
      exact ⟨0, rfl, hd, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · simp only [hd] at h ⊢
      obtain ⟨j, h1, h2, h3⟩ := ih _ h
      refine ⟨j + 1, h1, h2, fun i hi => ?_⟩
      cases i with
      | zero => exact Bool.eq_false_iff.mpr hd
      | succ i => exact h3 i (Nat.lt_of_succ_lt_succ hi)

/-- Either a test never comes up in `j` instructions, or there's a first time it does. -/
theorem first_hit (P : NES → Bool) (j : Nat) (s : NES) :
    (∀ i, i ≤ j → P (stepN i s) = false) ∨ ∃ k, k ≤ j ∧ P (stepN k s) = true ∧ ∀ i, i < k → P (stepN i s) = false := by
  induction j with
  | zero =>
    cases h : P s with
    | false =>
      refine Or.inl fun i hi => ?_
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact h
    | true => exact Or.inr ⟨0, Nat.le_refl _, h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ j ih =>
    rcases ih with h | ⟨k, hk, h1, h2⟩
    · cases hp : P (stepN (j + 1) s) with
      | false =>
        refine Or.inl fun i hi => ?_
        rcases Nat.lt_or_eq_of_le hi with hl | rfl
        · exact h i (Nat.le_of_lt_succ hl)
        · exact hp
      | true => exact Or.inr ⟨j + 1, Nat.le_refl _, hp, fun i hi => h i (Nat.le_of_lt_succ hi)⟩
    · exact Or.inr ⟨k, Nat.le_succ_of_le hk, h1, h2⟩

/-- `runTo` runs up to the first time the address comes up, or until its fuel runs out. -/
theorem runTo_stepN (stop : UInt16) (n : Nat) (s : NES) :
    ∃ k, k ≤ n ∧ ((CPU.runTo (σ := NES) stop n).run s).2 = stepN k s ∧ ∀ i, i < k → (stepN i s).pc ≠ stop := by
  induction n generalizing s with
  | zero => exact ⟨0, Nat.le_refl _, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    by_cases hp : s.pc = stop
    · refine ⟨0, Nat.zero_le _, ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      show ((if (CPU.getRegs (σ := NES) |>.run s).1.pc = stop then pure () else do CPU.step; CPU.runTo stop n : StateM NES Unit).run s).2 = s
      have : (CPU.getRegs (σ := NES) |>.run s).1.pc = s.pc := rfl
      simp [this, hp]
      rfl
    · obtain ⟨k, hk, h1, h2⟩ := ih (CPU.step.run s).2
      refine ⟨k + 1, Nat.succ_le_succ hk, ?_, fun i hi => ?_⟩
      · rw [show stepN (k + 1) s = stepN k (CPU.step.run s).2 from rfl, ← h1]
        have : (CPU.getRegs (σ := NES) |>.run s).1.pc = s.pc := rfl
        show ((if (CPU.getRegs (σ := NES) |>.run s).1.pc = stop then pure () else do CPU.step; CPU.runTo stop n : StateM NES Unit).run s).2 = _
        simp [this, hp]
        rfl
      · cases i with
        | zero => exact hp
        | succ i => exact h2 i (Nat.lt_of_succ_lt_succ hi)

end Smb.Routine.RunSteps
