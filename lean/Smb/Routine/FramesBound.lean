import Smb.Routine.FrameCalls
import Smb.Routine.FrameChain
import Smb.Goal.OneOne
import Smb.Goal.PlayCycle
import Smb.Routine.UnmodelledRun

/-!
# The speed limit over frames of normal play

`frames_bound`: over frames `i` to `j` of the actual frame loop (`at'`), from a cycle state in a region other than
the player's, for a run within `NoOverflow` and modelled at frame `j`, Mario's progress measure grows by at most 640
sub-pixels (2.5 pixels) a frame: `pos (at' j) ≤ pos (at' i) + 640 (j - i)`, unless some frame is odd: a player call
still running when the frame ends, a second call in one frame, a phase exit, or an instruction at one of the cycle's
open exits. What's asked beyond that is local to single states: `XInv`'s horizontal part at frame `i`'s start (`XInvH`), and at every entry to
`PlayerCtrlRoutine` the Y speed in range and `XInv`'s scroll clause (`EntryOK`); and the screen's left edge at frame
`i` far enough below page `$7F` that 3 pixels a frame can't reach it. The window (`InWindow`) that makes 24-bit
progress real progress follows from that: each call moves the edge at most 3 pixels (`XStep`), and Mario is at most
`$F0` pixels right of it (`window_of`).
-/
namespace Smb.Routine.FramesBound
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle Smb.Routine.PlayKeep
open Smb.Routine.PlayerJoin Smb.Routine.FrameRun Smb.Routine.HorizontalLimit Smb.Routine.FrameCalls
open Smb.Routine.BlockPrefix Smb.Goal Smb.LocalBound.HorizontalDistance

/-- `XInv` without its scroll clause: what the horizontal bytes alone give. -/
def XInvH (r : UInt16 → UInt8) : Prop :=
  speedOk (r 0x57) = true ∧ edgeR r = leftL r + 255 ∧ r 0x3A1 = 0 ∧
  (pixelP r - leftL r ≤ 0xF0 ∨ pixelP r - leftL r = 0xFFFF)

/-- `XInv`'s scroll clause. -/
def Scroll (r : UInt16 → UInt8) : Prop :=
  0x50 ≤ r 0x755 → r 0x785 = 0 → pixelP r - leftL r ≠ 0 ∧ pixelP r - leftL r < 0x8000

/-- What's asked at each entry to `PlayerCtrlRoutine`. -/
def EntryOK (r : UInt16 → UInt8) : Prop :=
  r 0x9F + 0x40 < 0x80 ∧ Scroll r

theorem xinvH_congr {r r' : UInt16 → UInt8} (hk : ∀ a ∈ hbytes, r' a = r a) (h : XInvH r) : XInvH r' := by
  have hP : pixelP r' = pixelP r := by simp only [pixelP, hk 0x86 (by simp [hbytes]), hk 0x6D (by simp [hbytes])]
  have hL : leftL r' = leftL r := by simp only [leftL, hk 0x71A (by simp [hbytes]), hk 0x71C (by simp [hbytes])]
  have hR : edgeR r' = edgeR r := by simp only [edgeR, hk 0x71B (by simp [hbytes]), hk 0x71D (by simp [hbytes])]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hk 0x57 (by simp [hbytes])]; exact h1, by rw [hR, hL]; exact h2,
    by rw [hk 0x3A1 (by simp [hbytes])]; exact h3, by rw [hP, hL]; exact h4⟩

theorem xinvH_of_step {b a : UInt16 → UInt8} (hX : XStep b a) : XInvH a := by
  obtain ⟨h1, h2, h3, h4, _⟩ := hX
  exact ⟨h1, h2, h3, by rcases h4 with h | ⟨h, _⟩ <;> first | exact Or.inl h | exact Or.inr h⟩

theorem leftL_congr {r r' : UInt16 → UInt8} (hk : ∀ a ∈ hbytes, r' a = r a) : leftL r' = leftL r := by
  simp only [leftL, hk 0x71A (by simp [hbytes]), hk 0x71C (by simp [hbytes])]

/-- `InWindow` from `XInvH` and the screen's left edge below page `$7F`: Mario is at most `$F0` pixels right of it, or
just behind it, where `phi` is the edge. -/
theorem window_of {r : UInt16 → UInt8} (hH : XInvH r) (hL : (leftL r).toNat < 0x7F00) : InWindow r := by
  obtain ⟨_, _, _, hd⟩ := hH
  have hL' : leftL r < 0x7F00 := UInt16.lt_iff_toNat_lt.mpr (by simpa using hL)
  have h : phi r < 0x800000 := by
    unfold phi
    generalize pixelP r = P at *
    generalize leftL r = L at *
    generalize r 0x400 = s
    simp only [pack]
    bv_decide (config := { enums := false })
  unfold InWindow
  simpa using UInt32.lt_iff_toNat_lt.mp h

/-- A 16-bit advance of at most 3 from below `$FF00` is an advance of at most 3. -/
theorem edge_nat {a b : UInt16} (h : b - a ≤ 3) (ha : a.toNat < 0xFF00) : b.toNat ≤ a.toNat + 3 := by
  have ha' : a < 0xFF00 := UInt16.lt_iff_toNat_lt.mpr (by simpa using ha)
  have h1 : b ≤ a + 3 := by bv_decide
  have h2 : (a + 3).toNat = a.toNat + 3 := by
    rw [UInt16.toNat_add]
    simp only [UInt16.reduceToNat]
    omega
  have := UInt16.le_iff_toNat_le.mp h1
  omega

/-- Mario's pixel X shifted by `$8000`, so that the positions the window allows (from just behind a left edge at 0
to page `$7F`) don't wrap. -/
def xs (r : UInt16 → UInt8) : Nat := (pixelP r + 0x8000).toNat

theorem pixelP_congr {r r' : UInt16 → UInt8} (hk : ∀ a ∈ hbytes, r' a = r a) : pixelP r' = pixelP r := by
  simp only [pixelP, hk 0x6D (by simp [hbytes]), hk 0x86 (by simp [hbytes])]

theorem xs_range {r : UInt16 → UInt8} (hH : XInvH r) (hL : (leftL r).toNat < 0x7F00) :
    4 ≤ pixelP r + 0x8000 ∧ pixelP r + 0x8000 ≤ 0xFFFB := by
  obtain ⟨_, _, _, hd⟩ := hH
  have hL' : leftL r < 0x7F00 := UInt16.lt_iff_toNat_lt.mpr (by simpa using hL)
  generalize pixelP r = P at *
  generalize leftL r = L at *
  constructor <;> bv_decide (config := { enums := false })

/-- A 16-bit step of at most 4 either way, away from the wrap, is a step of at most 4. -/
theorem xs_step {a b : UInt16} (h : b - a + 4 ≤ 8) (h1 : 4 ≤ a + 0x8000) (h2 : a + 0x8000 ≤ 0xFFFB) :
    (b + 0x8000).toNat ≤ (a + 0x8000).toNat + 4 ∧ (a + 0x8000).toNat ≤ (b + 0x8000).toNat + 4 := by
  have e1 : b + 0x8000 ≤ (a + 0x8000) + 4 := by bv_decide
  have e2 : (a + 0x8000) - 4 ≤ b + 0x8000 := by bv_decide
  have n1 : ((a + 0x8000) + 4).toNat = (a + 0x8000).toNat + 4 := by
    have := UInt16.le_iff_toNat_le.mp h2
    rw [UInt16.toNat_add]
    simp only [UInt16.reduceToNat] at *
    omega
  have n2 : ((a + 0x8000) - 4).toNat = (a + 0x8000).toNat - 4 := by
    have := UInt16.le_iff_toNat_le.mp h1
    rw [UInt16.toNat_sub_of_le _ _ h1]
    simp only [UInt16.reduceToNat]
  have := UInt16.le_iff_toNat_le.mp e1
  have := UInt16.le_iff_toNat_le.mp e2
  have := UInt16.le_iff_toNat_le.mp h1
  simp only [UInt16.reduceToNat] at *
  omega

/-- An odd frame: a call still running at its end, a second call, or a phase exit. -/
def Odd (y : NES) (J : Nat) : Prop :=
  (∃ k, k < J ∧ Entered (stepN k y) ∧ ∀ i, k ≤ i → i ≤ J → (stepN i y).pc ≠ 0xAF01) ∨
  (∃ k, k < J ∧ (stepN k y).pc = 0xAF01 ∧ ∃ k2, k < k2 ∧ k2 < J ∧ Entered (stepN k2 y)) ∨
  (∃ m, m ≤ J ∧ EndExit (stepN m y).pc) ∨
  (∃ kB d k u, EndExit u.regs.pc ∧
    ((CPU.runTo (σ := Plain) 0xAF01 d).run (stepN kB y).toPlain).2 = ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2) ∨
  (∃ k, k < J ∧ stop (stepN k y).pc = true)

/-! ### The frame's instruction conditions from `NoOverflow`

`CycleGoClear` asks three things of each instruction until the frame ends: it isn't at one of the cycle's open exits,
the step stays modelled, and the buffer offsets are within the limits (`CleanIf`). `NoOverflow` gives the limits,
a modelled state at the end gives the rest of the run modelled (the flag is sticky), and an instruction at an open exit
is one more kind of odd frame. -/

theorem runClean_frame (l : List UInt8) (s : NES) (f : Nat) (hf : f < l.length) (h : runClean l s = true) :
    goClean NES.frameFuel (Smb.Goal.startFrame l[f] (NES.runFrames (l.take f) s)) = true := by
  induction l generalizing s f with
  | nil => simp at hf
  | cons b l ih =>
    simp only [runClean, Bool.and_eq_true] at h
    cases f with
    | zero => exact h.1.2
    | succ f => exact ih _ f (by simpa using hf) h.2

theorem goClean_frame {inputs : List UInt8} {j f : Nat} (hn : NoOverflow (inputs.take j)) (hj : f < j)
    (hf : f < inputs.length) :
    goClean NES.frameFuel (Smb.Goal.startFrame inputs[f] (at' inputs f)) = true := by
  have hl : f < (inputs.take j).length := by simp; omega
  have h := runClean_frame _ _ f hl hn
  have e1 : (inputs.take j)[f] = inputs[f] := by simp
  have e2 : (inputs.take j).take f = inputs.take f := by rw [List.take_take]; congr 1; omega
  rw [e1, e2] at h
  exact h

/-- A modelled state at frame `j` means modelled at every earlier frame. -/
theorem at_clear {inputs : List UInt8} {m j : Nat} (hmj : m ≤ j) (h : (at' inputs j).unmodelled = false) :
    (at' inputs m).unmodelled = false := by
  unfold at' at *
  rw [show j = m + (j - m) by omega, List.take_add] at h
  exact Smb.Sticky.runFrames_prefix_clear _ _ _ h

/-- A frame's loop within `NoOverflow`'s limits that ends modelled meets `CycleGoClear`, unless an instruction is at
an open exit first. -/
theorem goClear_or_stop : ∀ (n : Nat) (y : NES), goClean n y = true → (NES.frame.go n y).unmodelled = false →
    CycleGoClear n y ∨ ∃ k, (∀ m, m ≤ k → (stepN m y).frameDone = false) ∧ stop (stepN k y).pc = true
  | 0, _, _, _ => Or.inl trivial
  | n + 1, y, hc, hu => by
    by_cases hd : y.frameDone = true
    · exact Or.inl (Or.inl hd)
    · have hd' : y.frameDone = false := Bool.eq_false_iff.mpr hd
      cases hs : stop y.pc with
      | true => exact Or.inr ⟨0, fun m hm => by obtain rfl : m = 0 := Nat.le_zero.mp hm; exact hd', hs⟩
      | false =>
        simp only [goClean, hd', Bool.false_or, Bool.and_eq_true] at hc
        have hu' : (NES.frame.go n (CPU.step.run y).2).unmodelled = false := by
          simpa only [NES.frame.go, hd', Bool.false_eq_true, ite_false] using hu
        rcases goClear_or_stop n _ hc.2 hu' with h | ⟨k, hk, hks⟩
        · exact Or.inl (Or.inr ⟨hs, Smb.Sticky.go_clear n _ hu', Smb.Goal.OneOne.play_cleanIf_of_cleanAt hc.1, h⟩)
        · refine Or.inr ⟨k + 1, fun m hm => ?_, hks⟩
          cases m with
          | zero => exact hd'
          | succ m => exact hk m (by omega)

/-- **One frame**: back in the other regions, `XInvH` again, and at most 640 sub-pixels of progress; or odd. -/
theorem frame_step (x : NES) (r : Region) (hr : r ∈ rest) (hx : At r x) (hus : x.unmodelled = false) (b : UInt8)
    (hcl : goClean NES.frameFuel (Smb.Goal.startFrame b x) = true) (hgo : (NES.frame b 0 x).unmodelled = false)
    (hH : XInvH (ramAt x))
    (hB : ∀ k, (∀ m, m < k → (stepN m (startFrame b 0 x)).frameDone = false) →
      (stepN k (startFrame b 0 x)).pc = 0xB0E9 → EntryOK (ramAt (stepN k (startFrame b 0 x))))
    (hL0 : (leftL (ramAt x)).toNat + 3 < 0x7F00) :
    ((∃ r1 ∈ rest, At r1 (NES.frame b 0 x)) ∧ XInvH (ramAt (NES.frame b 0 x)) ∧
      (phi (ramAt (NES.frame b 0 x))).toNat ≤ (phi (ramAt x)).toNat + 640 ∧
      (leftL (ramAt (NES.frame b 0 x))).toNat ≤ (leftL (ramAt x)).toNat + 3 ∧
      xs (ramAt (NES.frame b 0 x)) ≤ xs (ramAt x) + 4 ∧ xs (ramAt x) ≤ xs (ramAt (NES.frame b 0 x)) + 4) ∨
    ∃ J, NES.frame b 0 x = stepN J (startFrame b 0 x) ∧ Odd (startFrame b 0 x) J := by
  have hgo' : (NES.frame.go NES.frameFuel (startFrame b 0 x)).unmodelled = false := hgo
  rcases goClear_or_stop NES.frameFuel (startFrame b 0 x) hcl hgo' with hc | ⟨k, hk, hks⟩
  case inr =>
    obtain ⟨J, hJ, hJd, _⟩ := Smb.Routine.RunSteps.go_stepN _ _ hgo'
    have hkJ : k < J := by
      refine Nat.lt_of_not_le fun h => ?_
      have := hk J h
      rw [hJd] at this
      cases this
    exact Or.inr ⟨J, hJ, Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hkJ, hks⟩)))⟩
  obtain ⟨J, hJ, hfd, hcases⟩ := frame_calls x r hr hx hus b hc hgo
  rcases hcases with ⟨hat, hk⟩ | ⟨hat, kB, jA, hkj, hjJ, hpcB, hkB, hpcA, hstep, hafter⟩ | hlag | hsecond
  · refine Or.inl ⟨hat, xinvH_congr hk hH, ?_, ?_, ?_, ?_⟩
    · rw [Smb.Routine.FrameChain.phi_congr hk]; omega
    · rw [leftL_congr hk]; omega
    · unfold xs; rw [pixelP_congr hk]; omega
    · unfold xs; rw [pixelP_congr hk]; omega
  · have hcov : Covered (ramAt (stepN kB (startFrame b 0 x))) := by
      obtain ⟨t4, t5⟩ := hB kB (fun m hm => hfd m (by omega)) hpcB
      obtain ⟨g1, g2, g3, g4⟩ := xinvH_congr hkB hH
      exact ⟨⟨g1, g2, g3, g4, t5⟩, t4⟩
    rcases hstep hcov with ⟨hX, _⟩ | hend | hplain
    · have hka : ∀ a ∈ hbytes, ramAt (stepN J (startFrame b 0 x)) a = ramAt (stepN jA (startFrame b 0 x)) a := hafter
      have hE : (leftL (ramAt (stepN jA (startFrame b 0 x)))).toNat ≤ (leftL (ramAt x)).toNat + 3 := by
        have h6 := hX.2.2.2.2.2.1
        rw [leftL_congr hkB] at h6
        exact edge_nat h6 (by omega)
      have hW0 := window_of hH (by omega)
      have hW1 := window_of (xinvH_of_step hX) (by omega)
      unfold InWindow at hW0 hW1
      rw [hJ]
      have hX7 := hX.2.2.2.2.2.2
      rw [pixelP_congr hkB] at hX7
      have hxr := xs_range hH (by omega)
      have hxs := xs_step hX7 hxr.1 hxr.2
      refine Or.inl ⟨by rw [← hJ]; exact hat, xinvH_congr hka (xinvH_of_step hX), ?_, by rw [leftL_congr hka]; exact hE,
        by unfold xs; rw [pixelP_congr hka]; exact hxs.1, by unfold xs; rw [pixelP_congr hka]; exact hxs.2⟩
      rw [Smb.Routine.FrameChain.phi_congr hka]
      rw [← Smb.Routine.FrameChain.phi_congr hkB] at hW0 ⊢
      exact modular_to_nat _ _ hW0 hW1 hX.2.2.2.2.1
    · exact Or.inr ⟨J, hJ, Or.inr (Or.inr (Or.inl (by
        obtain ⟨m, _, hm2, he⟩ := hend
        exact ⟨m, by omega, he⟩)))⟩
    · exact Or.inr ⟨J, hJ, Or.inr (Or.inr (Or.inr (Or.inl ⟨kB, jA - kB, hplain⟩)))⟩
  · exact Or.inr ⟨J, hJ, Or.inl hlag⟩
  · exact Or.inr ⟨J, hJ, Or.inr (Or.inl hsecond)⟩

theorem at_succ' (inputs : List UInt8) (f : Nat) (hf : f < inputs.length) :
    at' inputs (f + 1) = NES.frame inputs[f]! 0 (at' inputs f) := by
  have e : inputs[f]! = inputs[f] := by simp [hf]
  rw [e]
  simp only [at', NES.runFrames, List.take_add_one, List.getElem?_eq_getElem hf, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

set_option maxRecDepth 10000 in
/-- **The frames' invariant**: after `n` frames, the run is back in the other regions with `XInvH`, and `phi` has
grown at most 640 a frame; or one of those frames was odd. -/
theorem frames_inv (inputs : List UInt8) (i j : Nat) (hij : i ≤ j) (hj : j ≤ inputs.length)
    (hat : ∃ r ∈ rest, At r (at' inputs i)) (hus : (at' inputs i).unmodelled = false) (hH : XInvH (ramAt (at' inputs i)))
    (hno : NoOverflow (inputs.take j)) (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (stepN m (startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (stepN k (startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))))
    (hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00) :
    ∀ n, i + n ≤ j →
      ((∃ r ∈ rest, At r (at' inputs (i + n))) ∧ (at' inputs (i + n)).unmodelled = false ∧
        XInvH (ramAt (at' inputs (i + n))) ∧
        (phi (ramAt (at' inputs (i + n)))).toNat ≤ (phi (ramAt (at' inputs i))).toNat + 640 * n ∧
        (leftL (ramAt (at' inputs (i + n)))).toNat ≤ (leftL (ramAt (at' inputs i))).toNat + 3 * n ∧
        xs (ramAt (at' inputs (i + n))) ≤ xs (ramAt (at' inputs i)) + 4 * n ∧
        xs (ramAt (at' inputs i)) ≤ xs (ramAt (at' inputs (i + n))) + 4 * n) ∨
      ∃ f, i ≤ f ∧ f < i + n ∧ ∃ J, at' inputs (f + 1) = stepN J (startFrame inputs[f]! 0 (at' inputs f)) ∧
        Odd (startFrame inputs[f]! 0 (at' inputs f)) J := by
  intro n
  induction n with
  | zero =>
    intro _
    exact Or.inl ⟨hat, hus, hH, by simp, by simp, by simp only [Nat.add_zero, Nat.mul_zero, Nat.le_refl],
      by simp only [Nat.add_zero, Nat.mul_zero, Nat.le_refl]⟩
  | succ n ih =>
    intro hn
    rcases ih (by omega) with ⟨⟨r, hr, hr'⟩, hu', hHn, hbound, hedge, hx1, hx2⟩ | ⟨f, hf1, hf2, rest'⟩
    · have hsucc := at_succ' inputs (i + n) (by omega)
      have hcf : goClean NES.frameFuel (Smb.Goal.startFrame inputs[i + n]! (at' inputs (i + n))) = true := by
        have e : inputs[i + n]! = inputs[i + n]'(by omega) := by simp [show i + n < inputs.length by omega]
        rw [e]; exact goClean_frame hno (by omega) (by omega)
      have hgf : (NES.frame inputs[i + n]! 0 (at' inputs (i + n))).unmodelled = false := by
        rw [← hsucc]; exact at_clear (by omega) hu
      rcases frame_step (at' inputs (i + n)) r hr hr' hu' inputs[i + n]! hcf hgf hHn
          (hB (i + n) (by omega) (by omega)) (by omega) with
        ⟨hat1, hH1, hb1, he1, hy1, hy2⟩ | ⟨J, hJ, hodd⟩
      · rw [← hsucc] at hat1 hH1 hb1 he1 hgf hy1 hy2
        rw [show i + (n + 1) = i + n + 1 by omega]
        refine Or.inl ⟨hat1, hgf, hH1, ?_, by omega, by omega, by omega⟩
        rw [Nat.mul_succ, ← Nat.add_assoc]
        exact Nat.le_trans hb1 (Nat.add_le_add_right hbound 640)
      · exact Or.inr ⟨i + n, by omega, by omega, J, hsucc.trans hJ, hodd⟩
    · exact Or.inr ⟨f, hf1, by omega, rest'⟩

/-- **Reach**: between any two frames `a ≤ b` of a stretch from `i` with no odd frame before `b`, Mario's X moves at
most 4 pixels a frame either way. It's what bounds how many block or coin columns his collision points can touch in a
few updates, which the VRAM buffer's window counts rest on. -/
theorem frames_reach (inputs : List UInt8) (i j : Nat) (hij : i ≤ j) (hj : j ≤ inputs.length)
    (hat : ∃ r ∈ rest, At r (at' inputs i)) (hus : (at' inputs i).unmodelled = false) (hH : XInvH (ramAt (at' inputs i)))
    (hno : NoOverflow (inputs.take j)) (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (stepN m (startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (stepN k (startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))))
    (hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00)
    (a b : Nat) (hia : i ≤ a) (hab : a ≤ b) (hbj : b ≤ j) :
    (xs (ramAt (at' inputs b)) ≤ xs (ramAt (at' inputs a)) + 4 * (b - a) ∧
      xs (ramAt (at' inputs a)) ≤ xs (ramAt (at' inputs b)) + 4 * (b - a)) ∨
    ∃ f, i ≤ f ∧ f < b ∧ ∃ J, at' inputs (f + 1) = stepN J (startFrame inputs[f]! 0 (at' inputs f)) ∧
      Odd (startFrame inputs[f]! 0 (at' inputs f)) J := by
  rcases frames_inv inputs i j hij hj hat hus hH hno hu hB hL (a - i) (by omega) with
    ⟨hatA, husA, hHA, _, hLA, _, _⟩ | ⟨f, hf1, hf2, h⟩
  · rw [show i + (a - i) = a by omega] at hatA husA hHA hLA
    have hnoB : NoOverflow (inputs.take b) := by
      have := runClean_take (inputs.take j) initial b hno
      rwa [List.take_take, Nat.min_eq_left hbj] at this
    rcases frames_inv inputs a b hab (by omega) hatA husA hHA hnoB (at_clear hbj hu)
        (fun f h1 h2 => hB f (by omega) (by omega)) (by omega) (b - a) (by omega) with
      ⟨_, _, _, _, _, hx1, hx2⟩ | ⟨f, hf1, hf2, h⟩
    · rw [show a + (b - a) = b by omega] at hx1 hx2
      exact Or.inl ⟨hx1, hx2⟩
    · exact Or.inr ⟨f, by omega, by omega, h⟩
  · exact Or.inr ⟨f, hf1, by omega, h⟩

/-- **Frames of normal play keep the speed limit.** -/
theorem frames_bound (inputs : List UInt8) (i j : Nat) (hij : i ≤ j) (hj : j ≤ inputs.length)
    (hat : ∃ r ∈ rest, At r (at' inputs i)) (hus : (at' inputs i).unmodelled = false) (hH : XInvH (ramAt (at' inputs i)))
    (hno : NoOverflow (inputs.take j)) (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (stepN m (startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (stepN k (startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))))
    (hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00) :
    (phi (ramAt (at' inputs j))).toNat ≤ (phi (ramAt (at' inputs i))).toNat + 640 * (j - i) ∨
      ∃ f, i ≤ f ∧ f < j ∧ ∃ J, at' inputs (f + 1) = stepN J (startFrame inputs[f]! 0 (at' inputs f)) ∧
        Odd (startFrame inputs[f]! 0 (at' inputs f)) J := by
  rcases frames_inv inputs i j hij hj hat hus hH hno hu hB hL (j - i) (by omega) with ⟨_, _, _, hb, _, _, _⟩ | ⟨f, hf1, hf2, h⟩
  · left
    rw [show i + (j - i) = j by omega] at hb
    exact hb
  · exact Or.inr ⟨f, hf1, by omega, h⟩

/-- `frames_bound` in the goal's terms: the conclusion of `StartRun.pos_le_of_limited`, from the cycle instead of
`FrameLimited`. -/
theorem pos_le_of_cycle (inputs : List UInt8) (i j : Nat) (hij : i ≤ j) (hj : j ≤ inputs.length)
    (hat : ∃ r ∈ rest, At r (at' inputs i)) (hus : (at' inputs i).unmodelled = false) (hH : XInvH (ramAt (at' inputs i)))
    (hno : NoOverflow (inputs.take j)) (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (stepN m (startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (stepN k (startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))))
    (hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00) :
    pos (at' inputs j) ≤ pos (at' inputs i) + 640 * (j - i) ∨
      ∃ f, i ≤ f ∧ f < j ∧ ∃ J, at' inputs (f + 1) = stepN J (startFrame inputs[f]! 0 (at' inputs f)) ∧
        Odd (startFrame inputs[f]! 0 (at' inputs f)) J :=
  frames_bound inputs i j hij hj hat hus hH hno hu hB hL

/-- The player region has no box at the idle loop. -/
theorem idle_all : configs.all (fun c => !c.entries.all (fun e => e.pc == 0x8175) ||
    ((c.tableWith PlayParser.G Smb.prg).at 0x8057).isEmpty) = true := by native_decide

/-- A cycle state in the idle loop, where frames end, is in one of the regions other than the player's. -/
theorem rest_of_idle {s : NES} (h : CycleInv s) (hpc : s.pc = 0x8057) : ∃ r ∈ rest, At r s := by
  obtain ⟨hS, hP, r, hr, ram0, hi, hs, hz⟩ := h
  by_cases hrr : r ∈ rest
  · exact ⟨r, hrr, hS, hP, ram0, hi, hs, hz⟩
  · exfalso
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    have hk : c.entries.all (fun e => e.pc == 0x8175) = true := by
      cases hk : c.entries.all (fun e => e.pc == 0x8175) with
      | true => rfl
      | false => exact absurd (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simp [hk]⟩, rfl⟩) hrr
    have he : ((c.tableWith PlayParser.G Smb.prg).at 0x8057).isEmpty = true := by
      have := List.all_eq_true.mp idle_all c hc
      simpa [hk] using this
    obtain ⟨t, _, ⟨b, hbm, _⟩, hrel⟩ := hi
    have hspc : s.pc = t.regs.pc := by
      rcases hrel with h1 | ⟨_, h1⟩
      · exact congrArg Regs.pc h1.regs
      · exact congrArg Regs.pc h1.regs
    have hbm' : b ∈ (c.tableWith PlayParser.G Smb.prg).at 0x8057 := by rw [← hpc, hspc]; exact hbm
    rw [List.isEmpty_iff.mp he] at hbm'
    cases hbm'

/-- `pos_le_of_cycle` from a cycle state in the idle loop, the form `PlayCycleWitness.tas_in_cycle` gives. -/
theorem pos_le_of_idle (inputs : List UInt8) (i j : Nat) (hij : i ≤ j) (hj : j ≤ inputs.length)
    (hcyc : CycleInv (at' inputs i)) (hpc : (at' inputs i).pc = 0x8057) (hus : (at' inputs i).unmodelled = false)
    (hH : XInvH (ramAt (at' inputs i)))
    (hno : NoOverflow (inputs.take j)) (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (stepN m (startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (stepN k (startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))))
    (hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00) :
    pos (at' inputs j) ≤ pos (at' inputs i) + 640 * (j - i) ∨
      ∃ f, i ≤ f ∧ f < j ∧ ∃ J, at' inputs (f + 1) = stepN J (startFrame inputs[f]! 0 (at' inputs f)) ∧
        Odd (startFrame inputs[f]! 0 (at' inputs f)) J :=
  frames_bound inputs i j hij hj (rest_of_idle hcyc hpc) hus hH hno hu hB hL

end Smb.Routine.FramesBound
