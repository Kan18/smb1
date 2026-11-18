import Smb.Goal.LaunchFrames

/-!
# The launch, from the ROM

`launch_frame` chained over the launch's frames. `launch_32` is a search result on the model's runs; `launch_chain` shows the game's frames are such a run, as long as Mario stays in the window where the model applies, and `launch_bound'` then gets the same bound as `launch_bound` without `Follows` as a hypothesis.

What's still assumed, besides `NoOverflow`: the start's cells, and each frame's `Timing`.
-/
namespace Smb.Goal.OneOne

open Smb.Abs Smb.Abs.LaunchPhase
open Smb.Movement
open Smb.Routine (ramAt)
open Smb.Routine.HorizontalLimit (phi XStep)
open Smb.LocalBound.HorizontalDistance

/-- What's assumed of a frame of the launch. -/
def FrameOk (inputs : List UInt8) (f : Nat) : Prop :=
  ∀ (h : f < inputs.length), (at' inputs (f + 1)).unmodelled = false ∧
    ∀ j, at' inputs (f + 1) = Smb.Abs.stepN j (Smb.Routine.FrameRun.startFrame inputs[f] 0 (at' inputs f)) → Timing (Smb.Routine.FrameRun.startFrame inputs[f] 0 (at' inputs f)) j

/-- A clean run's frames are clean. -/
theorem runClean_go (l : List UInt8) (s : NES) (f : Nat) (hf : f < l.length) (h : runClean l s = true) :
    goClean NES.frameFuel (startFrame l[f] (NES.runFrames (l.take f) s)) = true := by
  induction l generalizing s f with
  | nil => simp at hf
  | cons b l ih =>
    simp only [runClean, Bool.and_eq_true] at h
    cases f with
    | zero => exact h.1.2
    | succ f => exact ih _ f (by simpa using hf) h.2

/-- `NoOverflow`, frame by frame. -/
theorem goClean_at {inputs : List UInt8} {j f : Nat} (hn : NoOverflow (inputs.take j)) (hj : f < j) (hf : f < inputs.length) :
    goClean NES.frameFuel (startFrame inputs[f] (at' inputs f)) = true := by
  have hl : f < (inputs.take j).length := by simp; omega
  have h := runClean_go _ _ f hl hn
  have e1 : (inputs.take j)[f] = inputs[f] := by simp
  have e2 : (inputs.take j).take f = inputs.take f := by rw [List.take_take]; congr 1; omega
  rw [e1, e2] at h
  exact h

theorem at_past {inputs : List UInt8} {f : Nat} (h : ¬ f < inputs.length) : at' inputs (f + 1) = at' inputs f := by
  simp only [at']
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- What holds at a frame's start, through the launch. -/
structure LState (inputs : List UInt8) (f : Nat) : Prop where
  pc : (at' inputs f).pc = 0x8057
  inv : FInvAt (at' inputs f)
  v : VReach (vcells (stateOf (at' inputs f)))
  speed : speedOk (ramAt (at' inputs f) 0x57) = true

/-- One frame, with or without an input. -/
theorem lstate_step {inputs : List UInt8} {i f : Nat} (h : LState inputs f) (hlo : 12 ≤ ramAt (at' inputs f) 0x86) (hhi : ramAt (at' inputs f) 0x86 ≤ 75) (hok : FrameOk inputs f)
    (hcl : ∀ h : f < inputs.length, goClean NES.frameFuel (startFrame inputs[f] (at' inputs f)) = true) :
    LState inputs (f + 1) ∧ Follows openGround inputs i f := by
  by_cases hf : f < inputs.length
  · obtain ⟨hun, hT⟩ := hok hf
    obtain ⟨p, inv, v, hfo⟩ := launch_frame (i := i) hf h.inv h.pc h.v hlo hhi h.speed hun (hcl hf) hT
    refine ⟨⟨p, inv, v, ?_⟩, hfo⟩
    obtain ⟨o, _, hnext, _⟩ := hfo
    have h0 : speedOk (view openGround (at' inputs f)).v = true := by
      have e : (view openGround (at' inputs f)).v = ramAt (at' inputs f) 0x57 := by
        simp only [view]; exact norm_v _ _
      rw [e]; exact h.speed
    have h1 : speedOk (view openGround (at' inputs (f + 1))).v = true := by
      rw [hnext]
      cases o with
      | still => exact h0
      | go g l i => exact step_ok _ _ _ _ _ h0
    have e : (view openGround (at' inputs (f + 1))).v = ramAt (at' inputs (f + 1)) 0x57 := by
      simp only [view]; exact norm_v _ _
    rw [← e]; exact h1
  · have e := at_past hf
    refine ⟨by rw [show LState inputs (f + 1) = LState inputs (f + 1) from rfl]; exact ⟨by rw [e]; exact h.pc, by rw [e]; exact h.inv, by rw [e]; exact h.v, by rw [e]; exact h.speed⟩, ⟨.still, trivial, ?_, ?_⟩⟩
    · rw [e]; rfl
    · rw [e]; simp [delta]

/-- The launch's frames follow the model, as long as Mario stays in the model's window. -/
theorem launch_chain {inputs : List UInt8} {i : Nat} (h0 : LState inputs i) (hs : view openGround (at' inputs i) = start) (hp : pos (at' inputs i) = 40 * 256)
    (hok : ∀ f, i ≤ f → f < i + 32 → FrameOk inputs f)
    (hcl : ∀ f, i ≤ f → f < i + 32 → ∀ h : f < inputs.length, goClean NES.frameFuel (startFrame inputs[f] (at' inputs f)) = true) :
    ∀ n, n ≤ 32 → (∀ m, m < n → pos (at' inputs i) ≤ pos (at' inputs (i + m)) + 7168) → LState inputs (i + n) ∧ ∀ m, m < n → Follows openGround inputs i (i + m) := by
  intro n
  induction n with
  | zero => exact fun _ _ => ⟨h0, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | succ n ih =>
    intro hn hw
    obtain ⟨hL, hF⟩ := ih (by omega) (fun m hm => hw m (by omega))
    obtain ⟨l, hl, ha, _, h2⟩ := follows_run (inputs := inputs) (i := i) n hF
    rw [hs] at ha h2
    have hb := launch_31_le l (by omega) ha
    have hc := lcells (Smb.Routine.LaunchPhase.glob_of_finv hL.inv)
    have hpos := pos_of_cells hc
    have hq := (ramAt (at' inputs (i + n)) 0x400).toNat_lt
    have hw0 := hw n (by omega)
    have hlo : 12 ≤ ramAt (at' inputs (i + n)) 0x86 := by
      rw [UInt8.le_iff_toNat_le]
      have : (12 : UInt8).toNat = 12 := rfl
      omega
    have hhi : ramAt (at' inputs (i + n)) 0x86 ≤ 75 := by
      rw [UInt8.le_iff_toNat_le]
      have : (75 : UInt8).toNat = 75 := rfl
      omega
    obtain ⟨h3, h4⟩ := lstate_step (i := i) hL hlo hhi (hok _ (by omega) (by omega)) (hcl _ (by omega) (by omega))
    refine ⟨h3, fun m hm => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | rfl
    · exact hF m h
    · exact h4

/-- The launch's bound, with its frames following the model by `launch_chain`. The last frame only needs the speed limit, since by then Mario's at full speed. -/
theorem launch_bound' {inputs : List UInt8} {i : Nat} (h0 : InWindow (ramAt (at' inputs i)))
    (hf : ∀ f, i ≤ f → f < i + 33 → FrameLimited inputs f) (hS : LState inputs i) (hs : view openGround (at' inputs i) = start) (hp : pos (at' inputs i) = 40 * 256)
    (hok : ∀ f, i ≤ f → f < i + 32 → FrameOk inputs f)
    (hcl : ∀ f, i ≤ f → f < i + 32 → ∀ h : f < inputs.length, goClean NES.frameFuel (startFrame inputs[f] (at' inputs f)) = true) :
    pos (at' inputs (i + 33)) ≤ pos (at' inputs i) + 10384 := by
  by_cases hall : ∀ m, m < 32 → pos (at' inputs i) ≤ pos (at' inputs (i + m)) + 7168
  · obtain ⟨_, hF⟩ := launch_chain hS hs hp hok hcl 32 (Nat.le_refl _) hall
    obtain ⟨l, hl, ha, _, h2⟩ := follows_run (inputs := inputs) (i := i) 32 hF
    rw [hs] at ha h2
    have h3 := launch_32_bound l hl ha
    have hw : InWindow (ramAt (at' inputs (i + 32))) := (hf (i + 31) (by omega) (by omega)).2.1
    have h4 := pos_le_of_limited (inputs := inputs) (i := i + 32) (j := i + 33) (by omega) hw (fun f h1 h2 => hf f (by omega) h2)
    have h5 : i + 33 - (i + 32) = 1 := by omega
    rw [h5] at h4
    omega
  · have hex : ∃ m, m ≤ 32 ∧ m < 32 ∧ ¬ pos (at' inputs i) ≤ pos (at' inputs (i + m)) + 7168 := by
      simp only [Classical.not_forall] at hall
      obtain ⟨m, hm1, hm2⟩ := hall
      exact ⟨m, by omega, hm1, hm2⟩
    obtain ⟨m, _, ⟨hm1, hm2⟩, hmin⟩ := exists_first 32 hex
    have hb : ∀ n, n < m → pos (at' inputs i) ≤ pos (at' inputs (i + n)) + 7168 := by
      intro n hn
      by_cases hc : pos (at' inputs i) ≤ pos (at' inputs (i + n)) + 7168
      · exact hc
      · exact absurd ⟨by omega, hc⟩ (hmin n hn)
    obtain ⟨_, hF⟩ := launch_chain hS hs hp hok hcl m (by omega) hb
    obtain ⟨l, hl, _, _, h2⟩ := follows_run (inputs := inputs) (i := i) m hF
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

/-- **The first pipe, from the ROM.** From first control, 56 tiles take at least 368 frames. This is `pipe_368` with its `Follows` hypothesis discharged: what's assumed is `NoOverflow`, the speed limit on every frame, what `FrameOk` asks of the launch's frames, and the state at control. -/
theorem pipe_368' {inputs : List UInt8} {i j : Nat} (hij : i ≤ j) (h0 : InWindow (ramAt (at' inputs i)))
    (hf : ∀ f, i ≤ f → f < j → FrameLimited inputs f) (hS : LState inputs i) (hs : view openGround (at' inputs i) = start) (hp : pos (at' inputs i) = 40 * 256)
    (hok : ∀ f, i ≤ f → f < i + 32 → FrameOk inputs f) (hn : NoOverflow (inputs.take j))
    (hd : pos (at' inputs i) + 224256 ≤ pos (at' inputs j)) : i + 368 ≤ j := by
  have h1 := speed_edge (speedLimited_of_frames hij h0 hf) hd
  have h2 := launch_bound' h0 (fun f h1' h2' => hf f h1' (by omega)) hS hs hp hok (fun f _ h2' hl => goClean_at hn (by omega) hl)
  have hw : InWindow (ramAt (at' inputs (i + 33))) := (hf (i + 32) (by omega) (by omega)).2.1
  have h3 := pos_le_of_limited (inputs := inputs) (i := i + 33) (j := j) (by omega) hw (fun f h1' h2' => hf f (by omega) h2')
  omega

end Smb.Goal.OneOne
