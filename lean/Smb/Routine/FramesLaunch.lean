import Smb.Routine.FramesBound

/-!
# The acceleration limit over frames of normal play

`frames_launch_edge`: from rest (`upSpeed` at most 255 at frame `i`), covering `D` with `gain m < D` takes at least
`m + 1` frames, unless a frame is odd. It's `launch_updates` with the player calls as updates: `FrameCalls` gives at most
one per frame, each with `XStep` and, where Mario is at least 8 px from the screen's left edge (`Far`), `LStep`; and
every other region keeps the horizontal bytes and `$0705` between calls, so the next call starts no further ahead and
no faster than the last one ended. Beyond `frames_bound`'s hypotheses it asks `Far` at each entry to
`PlayerCtrlRoutine`.
-/
namespace Smb.Routine.FramesLaunch
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle Smb.Routine.PlayKeep
open Smb.Routine.PlayerJoin Smb.Routine.FrameRun Smb.Routine.HorizontalLimit Smb.Routine.FrameCalls
open Smb.Routine.FramesBound Smb.Routine.BlockPrefix Smb.Goal Smb.LocalBound.HorizontalDistance
open Smb.Routine.Launch (LStep upSpeed Far gain launch_updates)

theorem upSpeed_congr {r r' : UInt16 → UInt8} (hk : ∀ a ∈ hbytes, r' a = r a) : upSpeed r' = upSpeed r := by
  have h57 := hk 0x57 (by simp [hbytes])
  have h705 := hk 0x705 (by simp [hbytes])
  unfold upSpeed
  rw [h57, h705]

theorem inWindow_congr {r r' : UInt16 → UInt8} (hk : ∀ a ∈ hbytes, r' a = r a) (h : InWindow r) : InWindow r' := by
  unfold InWindow at *
  rw [Smb.Routine.FrameChain.phi_congr hk]
  exact h

/-- **One frame**, recording its player call: none, and the bytes are kept; or one, from `bR` at `$B0E9` to `aR` at
`$AF01`, with both limits; or the frame is odd. -/
theorem frame_stepL (x : NES) (r : Region) (hr : r ∈ rest) (hx : At r x) (hus : x.unmodelled = false) (b : UInt8)
    (hcl : goClean NES.frameFuel (Smb.Goal.startFrame b x) = true) (hgo : (NES.frame b 0 x).unmodelled = false)
    (hH : XInvH (ramAt x))
    (hB : ∀ k, (∀ m, m < k → (stepN m (startFrame b 0 x)).frameDone = false) →
      (stepN k (startFrame b 0 x)).pc = 0xB0E9 →
      EntryOK (ramAt (stepN k (startFrame b 0 x))) ∧ Far (ramAt (stepN k (startFrame b 0 x))))
    (hL0 : (leftL (ramAt x)).toNat + 3 < 0x7F00) :
    ((∃ r1 ∈ rest, At r1 (NES.frame b 0 x)) ∧ XInvH (ramAt (NES.frame b 0 x)) ∧
      (∀ a ∈ hbytes, ramAt (NES.frame b 0 x) a = ramAt x a)) ∨
    ((∃ r1 ∈ rest, At r1 (NES.frame b 0 x)) ∧ XInvH (ramAt (NES.frame b 0 x)) ∧
      (leftL (ramAt (NES.frame b 0 x))).toNat ≤ (leftL (ramAt x)).toNat + 3 ∧
      ∃ bR aR : UInt16 → UInt8, XStep bR aR ∧ LStep bR aR ∧ InWindow bR ∧ InWindow aR ∧
        (∀ a ∈ hbytes, bR a = ramAt x a) ∧ (∀ a ∈ hbytes, ramAt (NES.frame b 0 x) a = aR a)) ∨
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
    exact Or.inr (Or.inr ⟨J, hJ, Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hkJ, hks⟩)))⟩)
  obtain ⟨J, hJ, hfd, hcases⟩ := frame_calls x r hr hx hus b hc hgo
  rcases hcases with ⟨hat, hk⟩ | ⟨hat, kB, jA, hkj, hjJ, hpcB, hkB, hpcA, hstep, hafter⟩ | hlag | hsecond
  · exact Or.inl ⟨hat, xinvH_congr hk hH, hk⟩
  · obtain ⟨⟨t4, t5⟩, hfar⟩ := hB kB (fun m hm => hfd m (by omega)) hpcB
    have hcov : Covered (ramAt (stepN kB (startFrame b 0 x))) := by
      obtain ⟨g1, g2, g3, g4⟩ := xinvH_congr hkB hH
      exact ⟨⟨g1, g2, g3, g4, t5⟩, t4⟩
    rcases hstep hcov with ⟨hX, hL⟩ | hend | hplain
    · have hka : ∀ a ∈ hbytes, ramAt (NES.frame b 0 x) a = ramAt (stepN jA (startFrame b 0 x)) a := by
        rw [hJ]; exact hafter
      have hE : (leftL (ramAt (stepN jA (startFrame b 0 x)))).toNat ≤ (leftL (ramAt x)).toNat + 3 := by
        have h6 := hX.2.2.2.2.2.1
        rw [leftL_congr hkB] at h6
        exact edge_nat h6 (by omega)
      refine Or.inr (Or.inl ⟨hat, xinvH_congr hka (xinvH_of_step hX), by rw [leftL_congr hka]; exact hE, _, _, hX,
        hL hfar, inWindow_congr hkB (window_of hH (by omega)), window_of (xinvH_of_step hX) (by omega), hkB, hka⟩)
    · exact Or.inr (Or.inr ⟨J, hJ, Or.inr (Or.inr (Or.inl (by
        obtain ⟨m, _, hm2, he⟩ := hend
        exact ⟨m, by omega, he⟩)))⟩)
    · exact Or.inr (Or.inr ⟨J, hJ, Or.inr (Or.inr (Or.inr (Or.inl ⟨kB, jA - kB, hplain⟩)))⟩)
  · exact Or.inr (Or.inr ⟨J, hJ, Or.inl hlag⟩)
  · exact Or.inr (Or.inr ⟨J, hJ, Or.inr (Or.inl hsecond)⟩)

/-- What `n` frames give: the run back in the other regions with `XInvH`, and `c ≤ n` calls recorded as `entry`
and `out`, chained by the kept bytes; or an odd frame. -/
def Carried (inputs : List UInt8) (i n c : Nat) (entry out : Nat → UInt16 → UInt8) : Prop :=
  c ≤ n ∧ (∃ r ∈ rest, At r (at' inputs (i + n))) ∧ (at' inputs (i + n)).unmodelled = false ∧
    XInvH (ramAt (at' inputs (i + n))) ∧
    (∀ k, k < c → XStep (entry k) (out k) ∧ LStep (entry k) (out k) ∧ InWindow (entry k) ∧ InWindow (out k)) ∧
    (∀ k, k + 1 < c → ∀ a ∈ hbytes, entry (k + 1) a = out k a) ∧
    (c = 0 → ∀ a ∈ hbytes, ramAt (at' inputs (i + n)) a = ramAt (at' inputs i) a) ∧
    (0 < c → ∀ a ∈ hbytes, entry 0 a = ramAt (at' inputs i) a) ∧
    (0 < c → ∀ a ∈ hbytes, ramAt (at' inputs (i + n)) a = out (c - 1) a) ∧
    (leftL (ramAt (at' inputs (i + n)))).toNat ≤ (leftL (ramAt (at' inputs i))).toNat + 3 * n

theorem frames_launch_inv (inputs : List UInt8) (i j : Nat) (hj : j ≤ inputs.length)
    (hat : ∃ r ∈ rest, At r (at' inputs i)) (hus : (at' inputs i).unmodelled = false) (hH : XInvH (ramAt (at' inputs i)))
    (hno : NoOverflow (inputs.take j)) (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (stepN m (startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (stepN k (startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))) ∧
        Far (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))))
    (hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00) :
    ∀ n, i + n ≤ j → (∃ c entry out, Carried inputs i n c entry out) ∨
      ∃ f, i ≤ f ∧ f < i + n ∧ ∃ J, at' inputs (f + 1) = stepN J (startFrame inputs[f]! 0 (at' inputs f)) ∧
        Odd (startFrame inputs[f]! 0 (at' inputs f)) J := by
  intro n
  induction n with
  | zero =>
    intro _
    refine Or.inl ⟨0, fun _ => ramAt (at' inputs i), fun _ => ramAt (at' inputs i), Nat.le_refl _, hat, hus, hH,
      fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (by omega), fun _ _ _ => rfl,
      fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0), by simp⟩
  | succ n ih =>
    intro hn
    rcases ih (by omega) with ⟨c, entry, out, hcn, ⟨r, hr, hr'⟩, hu', hHn, hcalls, hchain, h0c, hfirst, hlast, hedge⟩ |
        ⟨f, hf1, hf2, rest'⟩
    · have hsucc := at_succ' inputs (i + n) (by omega)
      have hcf : goClean NES.frameFuel (Smb.Goal.startFrame inputs[i + n]! (at' inputs (i + n))) = true := by
        have e : inputs[i + n]! = inputs[i + n]'(by omega) := by simp [show i + n < inputs.length by omega]
        rw [e]; exact goClean_frame hno (by omega) (by omega)
      have hgf : (NES.frame inputs[i + n]! 0 (at' inputs (i + n))).unmodelled = false := by
        rw [← hsucc]; exact at_clear (by omega) hu
      have e1 : i + (n + 1) = i + n + 1 := by omega
      rcases frame_stepL (at' inputs (i + n)) r hr hr' hu' inputs[i + n]! hcf hgf hHn
          (hB (i + n) (by omega) (by omega)) (by omega) with
        ⟨hat1, hH1, hk1⟩ | ⟨hat1, hH1, he1, bR, aR, hX, hLs, hWb, hWa, hkb, hka⟩ | ⟨J, hJ, hodd⟩
      · rw [← hsucc] at hat1 hH1 hk1 hgf
        rw [e1]
        refine Or.inl ⟨c, entry, out, by omega, hat1, hgf, hH1, hcalls, hchain, fun h0 a ha => ?_, hfirst,
          fun hpos a ha => (hk1 a ha).trans (hlast hpos a ha), ?_⟩
        · exact (hk1 a ha).trans (h0c h0 a ha)
        · rw [show i + (n + 1) = i + n + 1 by omega, leftL_congr hk1]; omega
      · rw [← hsucc] at hat1 hH1 hka hgf he1
        rw [e1]
        let entry' : Nat → UInt16 → UInt8 := fun k => if k = c then bR else entry k
        let out' : Nat → UInt16 → UInt8 := fun k => if k = c then aR else out k
        refine Or.inl ⟨c + 1, entry', out', by omega, hat1, hgf, hH1, fun k hk => ?_, fun k hk a ha => ?_,
          fun h => absurd h (by omega), fun _ a ha => ?_, fun _ a ha => ?_,
          by rw [show i + (n + 1) = i + n + 1 by omega]; omega⟩
        · by_cases hkc : k = c
          · subst hkc; simp only [entry', out', eq_self_iff_true, if_true]; exact ⟨hX, hLs, hWb, hWa⟩
          · simp only [entry', out', hkc, if_false]; exact hcalls k (by omega)
        · by_cases hkc : k + 1 = c
          · have hk' : k ≠ c := by omega
            simp only [entry', out', hkc, hk', if_true, if_false]
            have := hkb a ha
            rw [this]
            have hcpos : 0 < c := by omega
            have := hlast hcpos a ha
            rw [show c - 1 = k by omega] at this
            exact this
          · have hk' : k ≠ c := by omega
            simp only [entry', out', hkc, hk', if_false]
            exact hchain k (by omega) a ha
        · by_cases hc0 : c = 0
          · subst hc0; simp only [entry', eq_self_iff_true, if_true]
            exact (hkb a ha).trans (h0c rfl a ha)
          · have h0 : (0 : Nat) ≠ c := fun h => hc0 h.symm
            simp only [entry', h0, if_false]
            exact hfirst (by omega) a ha
        · simp only [out', show c + 1 - 1 = c by omega, eq_self_iff_true, if_true]
          exact hka a ha
      · exact Or.inr ⟨i + n, by omega, by omega, J, hsucc.trans hJ, hodd⟩
    · exact Or.inr ⟨f, hf1, by omega, rest'⟩

/-- **From rest, covering `D` takes more than `m` frames** if `gain m < D`, unless a frame is odd. -/
theorem frames_launch_edge (inputs : List UInt8) (i j m D : Nat) (hij : i ≤ j) (hj : j ≤ inputs.length)
    (hat : ∃ r ∈ rest, At r (at' inputs i)) (hus : (at' inputs i).unmodelled = false) (hH : XInvH (ramAt (at' inputs i)))
    (hno : NoOverflow (inputs.take j)) (hu : (at' inputs j).unmodelled = false)
    (hB : ∀ f, i ≤ f → f < j → ∀ k, (∀ m, m < k → (stepN m (startFrame inputs[f]! 0 (at' inputs f))).frameDone = false) →
      (stepN k (startFrame inputs[f]! 0 (at' inputs f))).pc = 0xB0E9 →
      EntryOK (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))) ∧
        Far (ramAt (stepN k (startFrame inputs[f]! 0 (at' inputs f)))))
    (hL : (leftL (ramAt (at' inputs i))).toNat + 3 * (j - i) < 0x7F00)
    (h0 : (upSpeed (ramAt (at' inputs i))).toNat ≤ 255)
    (hd : pos (at' inputs i) + D ≤ pos (at' inputs j)) (hm : gain m < D) :
    i + (m + 1) ≤ j ∨ ∃ f, i ≤ f ∧ f < j ∧ ∃ J, at' inputs (f + 1) = stepN J (startFrame inputs[f]! 0 (at' inputs f)) ∧
      Odd (startFrame inputs[f]! 0 (at' inputs f)) J := by
  rcases frames_launch_inv inputs i j hj hat hus hH hno hu hB hL (j - i) (by omega) with
    ⟨c, entry, out, hcn, _, _, hHj, hcalls, hchain, h0c, hfirst, hlast, hedge⟩ | ⟨f, hf1, hf2, h⟩
  · left
    have ej : i + (j - i) = j := by omega
    rw [ej] at hlast h0c
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · exfalso
      have hp : pos (at' inputs j) = pos (at' inputs i) := by
        show (phi (ramAt (at' inputs j))).toNat = (phi (ramAt (at' inputs i))).toNat
        rw [Smb.Routine.FrameChain.phi_congr (h0c hc0)]
      omega
    · let entry' : Nat → UInt16 → UInt8 := fun k => if k = c then ramAt (at' inputs j) else entry k
      have hm1 : m + 1 ≤ c := by
        refine launch_updates entry' out c m D (fun k hk => ?_) (fun k hk => (hcalls k hk).2.2.2)
          (fun k hk => ?_) (fun k hk _ => ?_) (fun k hk => ?_) (fun k hk => ?_) ?_ ?_ hm
        · by_cases hkc : k = c
          · simp only [entry', hkc, eq_self_iff_true, if_true]
            rw [ej] at hHj hedge
            exact window_of hHj (by omega)
          · simp only [entry', hkc, if_false]; exact (hcalls k (by omega)).2.2.1
        · have hk' : k ≠ c := by omega
          simp only [entry', hk', if_false]; exact (hcalls k hk).1
        · have hk' : k ≠ c := by omega
          simp only [entry', hk', if_false]; exact (hcalls k hk).2.1
        · have hk1 : ∀ a ∈ hbytes, entry' (k + 1) a = out k a := by
            by_cases hkc : k + 1 = c
            · simp only [entry', hkc, eq_self_iff_true, if_true]
              intro a ha
              have := hlast hcpos a ha
              rw [show c - 1 = k by omega] at this
              exact this
            · simp only [entry', hkc, if_false]; exact hchain k (by omega)
          rw [Smb.Routine.FrameChain.phi_congr hk1]; exact Nat.le_refl _
        · have hk1 : ∀ a ∈ hbytes, entry' (k + 1) a = out k a := by
            by_cases hkc : k + 1 = c
            · simp only [entry', hkc, eq_self_iff_true, if_true]
              intro a ha
              have := hlast hcpos a ha
              rw [show c - 1 = k by omega] at this
              exact this
            · simp only [entry', hkc, if_false]; exact hchain k (by omega)
          rw [upSpeed_congr hk1]; simp
        · have h0' : (0 : Nat) ≠ c := by omega
          simp only [entry', h0', if_false]
          rw [upSpeed_congr (hfirst hcpos)]; exact h0
        · have h0' : (0 : Nat) ≠ c := by omega
          simp only [entry', h0', if_false, eq_self_iff_true, if_true]
          have hp : pos (at' inputs i) = (phi (entry 0)).toNat := by
            show (phi (ramAt (at' inputs i))).toNat = _
            rw [Smb.Routine.FrameChain.phi_congr (hfirst hcpos)]
          have hp2 : pos (at' inputs j) = (phi (ramAt (at' inputs j))).toNat := rfl
          omega
      omega
  · exact Or.inr ⟨f, hf1, by omega, h⟩

end Smb.Routine.FramesLaunch
