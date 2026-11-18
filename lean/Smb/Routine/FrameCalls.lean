import Smb.Routine.PlayerJoin

/-!
# One frame of normal play: at most one player call

`frame_calls`: a frame (`NES.frame`) that starts in one of the regions other than the player's, and meets the cycle's
conditions on every instruction (`CycleGoClear`), either makes no player call, and ends with Mario's horizontal bytes
as they were, or makes exactly one, complete, from `$8175` to `$AF01`. Then the bytes reach `$B0E9` as they were at
the frame's start, `XStep` holds from there to `$AF01` (with
the Y speed in range and `XInv` at `$B0E9`), and the frame ends with the bytes as at `$AF01`, back in the other
regions. The exceptions are named: a call still running when the frame ends (`Lag`), a second call in the same
frame, and a phase exit. So `minimum_frames`'s count of updates against frames needs no separate scheduling argument
on the frames this covers.
-/
namespace Smb.Routine.FrameCalls
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle Smb.Routine.PlayKeep
open Smb.Routine.PlayerJoin Smb.Routine.RunSteps Smb.Routine.FrameRun Smb.Routine.BlockPrefix
open Smb.Routine.HorizontalLimit

theorem at_start {r : Region} {s : NES} (p0 p1 : UInt8) (h : At r s) : At r (startFrame p0 p1 s) := by
  obtain ⟨hS, hP, ram0, ⟨t, hc, hinv, hrel⟩, hsaved, hz⟩ := h
  refine ⟨Sch.of_sv hS ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, hP, ram0, ⟨t, hc, hinv, ?_⟩, hsaved,
    fun e => ?_⟩
  · rcases hrel with h1 | ⟨h2, h3⟩
    · exact Or.inl (RelD_start p0 p1 h1)
    · exact Or.inr ⟨h2, RelOn_start p0 p1 h3⟩
  · rcases hz e with h1 | h1
    · exact Or.inl (ZStage_start p0 p1 h1)
    · exact Or.inr h1

/-- The frame loop's conditions, at each of its instructions. -/
theorem go_clear (n : Nat) (y : NES) (hc : CycleGoClear n y) (hgo : (NES.frame.go n y).unmodelled = false) :
    ∃ j, NES.frame.go n y = stepN j y ∧ (∀ i, i < j → (stepN i y).frameDone = false) ∧
      ∀ i, i < j → stop (stepN i y).pc = false ∧ (stepN (i + 1) y).unmodelled = false ∧ CleanIf (stepN (i + 1) y) := by
  induction n generalizing y with
  | zero => simp [NES.frame.go] at hgo
  | succ n ih =>
    simp only [NES.frame.go] at hgo ⊢
    by_cases hd : y.frameDone = true
    · simp only [hd, ite_true]
      exact ⟨0, rfl, fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · simp only [hd] at hgo ⊢
      rcases hc with hd' | ⟨h1, h2, h3, h4⟩
      · exact absurd hd' hd
      obtain ⟨j, e, hf, hj⟩ := ih _ h4 hgo
      refine ⟨j + 1, e, fun i hi => ?_, fun i hi => ?_⟩
      · cases i with
        | zero => exact Bool.eq_false_iff.mpr hd
        | succ i => exact hf i (Nat.lt_of_succ_lt_succ hi)
      · cases i with
        | zero => exact ⟨h1, h2, h3⟩
        | succ i => exact hj i (Nat.lt_of_succ_lt_succ hi)

/-- What `routine_run` asks at `$B0E9` beyond its region's bounds: `XInv` and the Y speed in range. -/
def Covered (r : UInt16 → UInt8) : Prop :=
  XInv r ∧ r 0x9F + 0x40 < 0x80

/-- The frame's one player call: entered with the frame's horizontal bytes, `XStep` from `$B0E9` to `$AF01` when
the Y speed is in range (or a phase exit), and the frame's end with the bytes as at `$AF01`. -/
def Call (x : NES) (y : NES) (J : Nat) : Prop :=
  ∃ kB jA, kB < jA ∧ jA ≤ J ∧ (stepN kB y).pc = 0xB0E9 ∧ (∀ a ∈ hbytes, ramAt (stepN kB y) a = ramAt x a) ∧
    (stepN jA y).pc = 0xAF01 ∧
    (Covered (ramAt (stepN kB y)) →
      (XStep (ramAt (stepN kB y)) (ramAt (stepN jA y)) ∧
        (Launch.Far (ramAt (stepN kB y)) → Launch.LStep (ramAt (stepN kB y)) (ramAt (stepN jA y)))) ∨
        (∃ m, kB ≤ m ∧ m ≤ jA ∧ EndExit (stepN m y).pc) ∨
        ∃ k u, EndExit u.regs.pc ∧ ((CPU.runTo (σ := Plain) 0xAF01 (jA - kB)).run (stepN kB y).toPlain).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2) ∧
    ∀ a ∈ hbytes, ramAt (stepN J y) a = ramAt (stepN jA y) a

/-- **One frame of normal play.** -/
theorem frame_calls (x : NES) (r : Region) (hr : r ∈ rest) (hx : At r x) (hus : x.unmodelled = false) (b : UInt8)
    (hc : CycleGoClear NES.frameFuel (startFrame b 0 x)) (hgo : (NES.frame b 0 x).unmodelled = false) :
    ∃ J, NES.frame b 0 x = stepN J (startFrame b 0 x) ∧ (∀ m, m < J → (stepN m (startFrame b 0 x)).frameDone = false) ∧
      (((∃ r1 ∈ rest, At r1 (NES.frame b 0 x)) ∧ ∀ a ∈ hbytes, ramAt (NES.frame b 0 x) a = ramAt x a) ∨
       ((∃ r1 ∈ rest, At r1 (NES.frame b 0 x)) ∧ Call x (startFrame b 0 x) J) ∨
       -- A call still running when the frame ends.
       (∃ k, k < J ∧ Entered (stepN k (startFrame b 0 x)) ∧ ∀ i, k ≤ i → i ≤ J → (stepN i (startFrame b 0 x)).pc ≠ 0xAF01) ∨
       -- A second call after the first.
       (∃ k, k < J ∧ (stepN k (startFrame b 0 x)).pc = 0xAF01 ∧ ∃ k2, k < k2 ∧ k2 < J ∧ Entered (stepN k2 (startFrame b 0 x)))) := by
  generalize hy : startFrame b 0 x = y at hc ⊢
  have hgo' : (NES.frame.go NES.frameFuel y).unmodelled = false := by rw [← hy]; exact hgo
  obtain ⟨J, hJ, hfd, hcond⟩ := go_clear _ y hc hgo'
  have hframe : NES.frame b 0 x = stepN J y := by rw [frame_def, hy]; exact hJ
  rw [hframe]
  refine ⟨J, rfl, hfd, ?_⟩
  have hyat : At r y := by rw [← hy]; exact at_start b 0 hx
  have hyu : y.unmodelled = false := by rw [← hy]; exact hus
  have hkx : ∀ a ∈ hbytes, ramAt y a = ramAt x a := fun a _ => by rw [← hy]; rfl
  have hu : ∀ i, i ≤ J → (stepN i y).unmodelled = false := by
    intro i hi
    cases i with
    | zero => exact hyu
    | succ i => exact (hcond i (by omega)).2.1
  rcases rest_run J y r hr hyat (fun i hi => (hcond i hi).1) hu (fun i hi => (hcond i hi).2.2) with
    ⟨r1, hr1, h1, hk1⟩ | ⟨kE, hkE, hk1, hent⟩
  · exact Or.inl ⟨⟨r1, hr1, h1⟩, fun a ha => (hk1 a ha).trans (hkx a ha)⟩
  · -- The player region was entered; does it return within the frame?
    rcases first_hit (fun w => w.pc == 0xAF01) (J - kE) (stepN kE y) with hnone | ⟨d, hd, hhit, hbefore⟩
    · refine Or.inr (Or.inr (Or.inl ⟨kE, hkE, hent, fun i hi1 hi2 e => ?_⟩))
      have := hnone (i - kE) (by omega)
      rw [← stepN_add, show kE + (i - kE) = i by omega] at this
      simp [e] at this
    · have hpcA : (stepN (kE + d) y).pc = 0xAF01 := by rw [stepN_add]; simpa using hhit
      have hfirst : ∀ i, i < d → (stepN i (stepN kE y)).pc ≠ 0xAF01 := by
        intro i hi e
        have := hbefore i hi
        simp [e] at this
      obtain ⟨kB, hkBd, hpcB, hkb, hrest⟩ := player_frame (stepN kE y) hent d (by rw [← stepN_add]; exact hpcA) hfirst
        (fun i hi => by
          rw [← stepN_add]
          rcases Nat.lt_or_ge (kE + i) J with h | h
          · exact ne_B1E5 (hcond _ h).1
          · have hiJ : kE + i = kE + d := by omega
            rw [hiJ, hpcA]; decide)
      -- The cycle's invariant at `$AF01`, and back into the other regions.
      have hcyc : CycleInv (stepN (kE + d) y) :=
        normal_play_run (kE + d) y (fun i hi => (hcond i (by omega)).1) (fun i hi => hu i (by omega))
          (fun i hi => (hcond i (by omega)).2.2) (savedFinv_of_at (rest_sub hr) hyat)
      obtain ⟨r2, hr2, hat2⟩ := rest_of_exit hcyc hpcA
      have hshift (i : Nat) : stepN i (stepN (kE + d) y) = stepN (kE + d + i) y := (stepN_add _ _ _).symm
      rcases rest_run (J - (kE + d)) (stepN (kE + d) y) r2 hr2 hat2
          (fun i hi => by rw [hshift]; exact (hcond _ (by omega)).1)
          (fun i hi => by rw [hshift]; exact hu _ (by omega))
          (fun i hi => by rw [hshift, show kE + d + (i + 1) = (kE + d + i) + 1 by omega]; exact (hcond _ (by omega)).2.2) with
        ⟨r3, hr3, h3, hk3⟩ | ⟨k2, hk2, _, hent2⟩
      · have hend : stepN (J - (kE + d)) (stepN (kE + d) y) = stepN J y := by
          rw [hshift]; congr 1; omega
        rw [hend] at h3 hk3
        have e1 : stepN kB (stepN kE y) = stepN (kE + kB) y := (stepN_add _ _ _).symm
        rw [e1] at hpcB hkb hrest
        have hkbH : ∀ a ∈ hbytes, ramAt (stepN (kE + kB) y) a = ramAt x a := by
          intro a ha
          have ha' : a ∈ kbytes := by
            simp only [hbytes, List.mem_cons, List.not_mem_nil, or_false] at ha
            simp only [kbytes, List.mem_cons, List.not_mem_nil, or_false]
            rcases ha with h | h | h | h | h | h | h | h | h | h <;> simp [h]
          exact (hkb a ha').trans ((hk1 a ha).trans (hkx a ha))
        have hdA : stepN d (stepN kE y) = stepN (kE + d) y := (stepN_add _ _ _).symm
        refine Or.inr (Or.inl ⟨⟨r3, hr3, h3⟩, kE + kB, kE + d, by omega, by omega, hpcB, hkbH, hpcA, ?_, hk3⟩)
        rintro ⟨hinv, h1⟩
        rcases hrest hinv h1 with h | ⟨m, hm1, hm2, hend'⟩ | h
        · rw [hdA] at h; exact Or.inl h
        · refine Or.inr (Or.inl ⟨kE + m, by omega, by omega, ?_⟩)
          rw [stepN_add]; exact hend'
        · refine Or.inr (Or.inr ?_)
          rw [show kE + d - (kE + kB) = d - kB by omega]
          exact h
      · refine Or.inr (Or.inr (Or.inr ⟨kE + d, by omega, hpcA, kE + d + k2, ?_, by omega, ?_⟩))
        · have : 0 < k2 := by
            rcases Nat.eq_zero_or_pos k2 with h0 | h0
            · subst h0
              have := hent2.1
              rw [show stepN 0 (stepN (kE + d) y) = stepN (kE + d) y from rfl, hpcA] at this
              exact absurd this (by decide)
            · exact h0
          omega
        · rw [← hshift]; exact hent2

end Smb.Routine.FrameCalls
