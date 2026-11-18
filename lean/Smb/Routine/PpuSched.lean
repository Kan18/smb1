import Smb.Routine.AbsIO

/-!
# The PPU's event schedule

`Sch` is what holds of the PPU's event state at every bus cycle, for any program: the current event's position is ahead of the frame position, and vblank is set only between its start at
dot 342 and the next event. So when vblank starts, the position is known. It is the model's guard against a burst of more than 64 events, `unmodelled`, that makes this conditional.
-/
set_option maxRecDepth 20000
namespace Smb.NES

/-- The event schedule's shape. `lt` is what `SchW` weakens while events are being handled. -/
structure SchW (s : NES) : Prop where
  idx : s.evIdx = 0 ∨ s.evIdx = 1 ∨ s.evIdx = 2 ∨ s.evIdx = 3 ∨ s.evIdx = 4 ∨ s.evIdx = 6 ∨ s.evIdx = 7
  le : s.fpos ≤ phPos s s.evIdx
  nle : s.nextEv ≤ phPos s s.evIdx
  ncase : s.nextEv = phPos s s.evIdx ∨ s.nextEv = s.hitPos ∨ s.nextEv = s.overflowPos
  skip : s.skipped ≤ 1
  flen : (s.evIdx = 4 ∨ s.evIdx = 6 ∨ s.evIdx = 7) → s.flen = 262 * 341 - s.skipped
  lineL : (s.evIdx = 4 ∨ s.evIdx = 6) → s.line < 240
  line240 : (s.evIdx = 7 ∨ s.evIdx = 0 ∨ s.evIdx = 1 ∨ s.evIdx = 2) → s.line = 240
  line0 : s.evIdx = 3 → s.line = 0
  none : (s.evIdx = 0 ∨ s.evIdx = 1) → s.hitPos = NONE ∧ s.overflowPos = NONE
  vbl1 : s.vbl = true → s.evIdx = 1
  dead : s.dead = 0

theorem min3 (a h o : UInt32) : min a (min h o) ≤ a ∧ (min a (min h o) = a ∨ min a (min h o) = h ∨ min a (min h o) = o) := by
  have hm : ∀ x y : UInt32, min x y = if x ≤ y then x else y := fun _ _ => rfl
  simp only [hm]
  split <;> split <;> simp_all <;> bv_decide (config := { enums := false })

/-- All of `SchW` but what `sched` sets. -/
structure Pre (y : NES) : Prop where
  idx : y.evIdx = 0 ∨ y.evIdx = 1 ∨ y.evIdx = 2 ∨ y.evIdx = 3 ∨ y.evIdx = 4 ∨ y.evIdx = 6 ∨ y.evIdx = 7
  le : y.fpos ≤ phPos y y.evIdx
  skip : y.skipped ≤ 1
  flen : (y.evIdx = 4 ∨ y.evIdx = 6 ∨ y.evIdx = 7) → y.flen = 262 * 341 - y.skipped
  lineL : (y.evIdx = 4 ∨ y.evIdx = 6) → y.line < 240
  line240 : (y.evIdx = 7 ∨ y.evIdx = 0 ∨ y.evIdx = 1 ∨ y.evIdx = 2) → y.line = 240
  line0 : y.evIdx = 3 → y.line = 0
  none : (y.evIdx = 0 ∨ y.evIdx = 1) → y.hitPos = NONE ∧ y.overflowPos = NONE
  vbl1 : y.vbl = true → y.evIdx = 1
  dead : y.dead = 0

theorem phPos_ne (y : NES) (h : Pre y) : phPos y y.evIdx ≠ NONE := by
  rcases h.idx with e | e | e | e | e | e | e
  all_goals rw [e]
  · simp [phPos, NONE]
  · simp [phPos, NONE]
  · simp [phPos, NONE]
  · simp [phPos, NONE]
  · have h1 := h.lineL (Or.inl e)
    have h2 := h.skip
    simp only [phPos, line0, NONE]
    revert h1 h2
    bv_decide (config := { enums := false })
  · have h1 := h.lineL (Or.inr e)
    have h2 := h.skip
    simp only [phPos, line0, NONE]
    revert h1 h2
    bv_decide (config := { enums := false })
  · have h1 := h.flen (Or.inr (Or.inr e))
    have h2 := h.skip
    simp only [phPos, NONE, h1]
    revert h2
    bv_decide (config := { enums := false })

theorem idx_lt (y : NES) (h : Pre y) : ¬ (y.evIdx ≥ 8) := by
  rcases h.idx with e | e | e | e | e | e | e <;> rw [e] <;> decide

theorem sched_eq (y : NES) (h : Pre y) : sched y = { y with nextEv := min (phPos y y.evIdx) (min y.hitPos y.overflowPos) } := by
  have h1 := phPos_ne y h
  have h2 := idx_lt y h
  have h3 : (phPos y y.evIdx != NONE) = true := by simpa using h1
  simp only [sched, sched.go, h2, h3, if_false, if_true]

theorem sched_five (y : NES) (h5 : y.evIdx = 5) (h : Pre { y with evIdx := 6 }) : sched y = sched { y with evIdx := 6 } := by
  have h1 := phPos_ne _ h
  have h2 := idx_lt _ h
  have h3 : (phPos { y with evIdx := 6 } 6 != NONE) = true := by simpa using h1
  have h4 : ¬ ((6 : UInt8) ≥ 8) := by decide
  have h7 : (phPos y 5 != NONE) = false := by simp [phPos]
  have h8 : y.evIdx + 1 = 6 := by rw [h5]; rfl
  simp [sched, sched.go, h5, h7, h3, h8]

theorem sch_sched (y : NES) (h : Pre y) : SchW (sched y) := by
  rw [sched_eq y h]
  obtain ⟨m1, m2⟩ := min3 (phPos y y.evIdx) y.hitPos y.overflowPos
  exact { idx := h.idx, le := h.le, nle := m1, ncase := m2, skip := h.skip, flen := h.flen, lineL := h.lineL, line240 := h.line240, line0 := h.line0, none := h.none, vbl1 := h.vbl1, dead := h.dead }

theorem fetchSprite0_sch (x : NES) :
    (fetchSprite0 x).fpos = x.fpos ∧ (fetchSprite0 x).line = x.line ∧ (fetchSprite0 x).skipped = x.skipped ∧ (fetchSprite0 x).flen = x.flen ∧
    (fetchSprite0 x).evIdx = x.evIdx ∧ (fetchSprite0 x).hitPos = x.hitPos ∧ (fetchSprite0 x).overflowPos = x.overflowPos ∧ (fetchSprite0 x).vbl = x.vbl ∧ (fetchSprite0 x).dead = x.dead := by
  unfold fetchSprite0; dsimp only
  repeat' split
  all_goals simp

/-- What a line's end does before it moves to the next line. -/
def lineEndMid (s : NES) : NES :=
  if s.mask &&& 0x18 != 0 then
    let s := fetchSprite0 { s with v := incY s.v }
    { s with oamaddr := 0, v := (s.v &&& 0xFBE0) ||| (s.t &&& 0x041F) }
  else { s with sp0x := 0x100 }

theorem lineEndMid_sch (x : NES) :
    (lineEndMid x).fpos = x.fpos ∧ (lineEndMid x).line = x.line ∧ (lineEndMid x).skipped = x.skipped ∧ (lineEndMid x).flen = x.flen ∧
    (lineEndMid x).evIdx = x.evIdx ∧ (lineEndMid x).vbl = x.vbl ∧ (lineEndMid x).dead = x.dead := by
  have h := fetchSprite0_sch { x with v := incY x.v }
  obtain ⟨a, b, c, d, e, _, _, g, i⟩ := h
  unfold lineEndMid
  split
  · exact ⟨a, b, c, d, e, g, i⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem handle_six (x : NES) (e : x.evIdx = 6) (h1 : ¬ ((x.hitPos == x.nextEv) = true)) (h2 : ¬ ((x.overflowPos == x.nextEv) = true)) :
    handleEv x = (let s := lineEndMid x
      let s := { s with line := s.line + 1 }
      if s.line < (240 : UInt32) then sched { s with evIdx := 4 } else sched { s with evIdx := 7 }) := by
  unfold handleEv
  rw [if_neg h1, if_neg h2]
  split
  all_goals first
    | rfl
    | (exfalso; simp_all; done)

theorem sch_sched5 (y : NES) (h5 : y.evIdx = 5) (h : Pre { y with evIdx := 6 }) : SchW (sched y) := by
  rw [sched_five y h5 h]
  exact sch_sched _ h

/-- Handling the due event keeps the shape. -/
theorem sch_handleEv (x : NES) (h : SchW x) (hdue : x.nextEv ≤ x.fpos) : SchW (handleEv x) := by
  have base : Pre x := { idx := h.idx, le := h.le, skip := h.skip, flen := h.flen, lineL := h.lineL, line240 := h.line240, line0 := h.line0, none := h.none, vbl1 := h.vbl1, dead := h.dead }
  unfold handleEv
  split
  · exact sch_sched _ { idx := h.idx, le := h.le, skip := h.skip, flen := h.flen, lineL := h.lineL, line240 := h.line240, line0 := h.line0,
                        none := fun e => ⟨rfl, (h.none e).2⟩, vbl1 := h.vbl1, dead := h.dead }
  split
  · exact sch_sched _ { idx := h.idx, le := h.le, skip := h.skip, flen := h.flen, lineL := h.lineL, line240 := h.line240, line0 := h.line0,
                        none := fun e => ⟨(h.none e).1, rfl⟩, vbl1 := h.vbl1, dead := h.dead }
  rename_i hn1 hn2
  have hnh : x.nextEv ≠ x.hitPos := by intro e; apply hn1; simp [e]
  have hno : x.nextEv ≠ x.overflowPos := by intro e; apply hn2; simp [e]
  have hnp : x.nextEv = phPos x x.evIdx := by
    rcases h.ncase with e | e | e
    · exact e
    · exact absurd e hnh
    · exact absurd e hno
  have hfp : x.fpos = phPos x x.evIdx := by
    have h1 := h.le
    rw [hnp] at hdue
    revert h1 hdue
    generalize phPos x x.evIdx = q
    generalize x.fpos = f
    bv_decide (config := { enums := false })
  have hskip := h.skip
  rcases h.idx with e | e | e | e | e | e | e
  · -- vblank starts
    simp only [e]
    exact sch_sched _ { idx := by simp, le := by simp only [phPos]; rw [e] at hfp; simp only [phPos] at hfp; rw [hfp]; decide,
                        skip := hskip, flen := by simp, lineL := by simp, line240 := fun _ => h.line240 (Or.inr (Or.inl e)), line0 := by simp,
                        none := fun _ => h.none (Or.inl e), vbl1 := fun _ => rfl, dead := h.dead }
  · -- vblank ends
    simp only [e]
    rw [e] at hfp
    simp only [phPos] at hfp
    exact sch_sched _ { idx := by simp, le := by simp only [phPos]; rw [hfp]; decide,
                        skip := hskip, flen := by simp, lineL := by simp, line240 := fun _ => h.line240 (Or.inr (Or.inr (Or.inl e))), line0 := by simp,
                        none := by simp, vbl1 := by simp, dead := rfl }
  · -- pre-render copy
    simp only [e]
    rw [e] at hfp
    simp only [phPos] at hfp
    have hv : x.vbl ≠ true := fun hv => by rw [h.vbl1 hv] at e; exact absurd e (by decide)
    exact sch_sched _ { idx := by simp, le := by simp only [phPos]; rw [hfp]; decide,
                        skip := hskip, flen := by simp, lineL := by simp, line240 := by simp, line0 := fun _ => rfl,
                        none := by simp, vbl1 := fun hv' => absurd hv' hv, dead := h.dead }
  · -- odd-frame skip
    simp only [e]
    rw [e] at hfp
    simp only [phPos] at hfp
    have hv : x.vbl ≠ true := fun hv => by rw [h.vbl1 hv] at e; exact absurd e (by decide)
    have hl := h.line0 e
    have hsk : ∀ c : Prop, ∀ [Decidable c], (if c then (1 : UInt32) else 0) ≤ 1 := by
      intro c _; split <;> decide
    generalize hS : (if x.odd != 0 && x.mask &&& 0x18 != 0 then (1 : UInt32) else 0) = S
    have hS1 : S ≤ 1 := by rw [← hS]; exact hsk _
    exact sch_sched _ { idx := by simp, le := by
                          simp only [phPos, NES.line0, hl, hfp]
                          revert hS1; bv_decide (config := { enums := false }),
                        skip := hS1, flen := fun _ => rfl, lineL := fun _ => by simp only [hl]; decide, line240 := by simp, line0 := by simp,
                        none := by simp, vbl1 := fun hv' => absurd hv' hv, dead := h.dead }
  · -- line start
    simp only [e]
    rw [e] at hfp
    simp only [phPos] at hfp
    have hv : x.vbl ≠ true := fun hv => by rw [h.vbl1 hv] at e; exact absurd e (by decide)
    have hl := h.lineL (Or.inl e)
    have hfl := h.flen (Or.inl e)
    exact sch_sched5 _ rfl { idx := by simp, le := by
                               simp only [phPos, NES.line0, hfp]
                               revert hl hskip; bv_decide (config := { enums := false }),
                             skip := hskip, flen := fun _ => hfl, lineL := fun _ => hl, line240 := by simp, line0 := by simp,
                             none := by simp, vbl1 := fun hv' => absurd hv' hv, dead := h.dead }
  · -- line end
    suffices hgoal : SchW (let s := lineEndMid x
        let s := { s with line := s.line + 1 }
        if s.line < (240 : UInt32) then sched { s with evIdx := 4 } else sched { s with evIdx := 7 }) by
      have := handle_six x e hn1 hn2
      unfold handleEv at this
      rw [if_neg hn1, if_neg hn2] at this
      rw [this]
      exact hgoal
    rw [e] at hfp
    simp only [phPos] at hfp
    have hv : x.vbl ≠ true := fun hv => by rw [h.vbl1 hv] at e; exact absurd e (by decide)
    have hl := h.lineL (Or.inr e)
    have hfl := h.flen (Or.inr (Or.inl e))
    obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := lineEndMid_sch x
    dsimp only
    rw [m2]
    generalize hM : lineEndMid x = M at m1 m2 m3 m4 m5 m6 m7
    have hv' : M.vbl ≠ true := by rw [m6]; exact hv
    split
    · rename_i hlt
      exact sch_sched _ { idx := by simp, le := by
                            simp only [phPos, NES.line0, m1, m3, hfp]
                            revert hl hskip hlt; bv_decide (config := { enums := false }),
                          skip := by rw [m3]; exact hskip, flen := fun _ => by rw [m4, m3]; exact hfl, lineL := fun _ => hlt, line240 := by simp, line0 := by simp,
                          none := by simp, vbl1 := fun hv2 => absurd hv2 hv', dead := by rw [m7]; exact h.dead }
    · rename_i hlt
      exact sch_sched _ { idx := by simp, le := by
                            simp only [phPos, m1, m4, hfl, hfp, NES.line0]
                            revert hl hskip hlt; bv_decide (config := { enums := false }),
                          skip := by rw [m3]; exact hskip, flen := fun _ => by rw [m4, m3]; exact hfl, lineL := by simp,
                          line240 := fun _ => by revert hl hlt; simp only; bv_decide (config := { enums := false }), line0 := by simp,
                          none := by simp, vbl1 := fun hv2 => absurd hv2 hv', dead := by rw [m7]; exact h.dead }
  · -- frame end
    simp only [e]
    rw [e] at hfp
    simp only [phPos] at hfp
    have hv : x.vbl ≠ true := fun hv => by rw [h.vbl1 hv] at e; exact absurd e (by decide)
    exact sch_sched _ { idx := by simp, le := by
                          simp only [phPos]
                          have : x.fpos - x.flen = 0 := by rw [hfp]; simp
                          rw [this]; decide,
                        skip := by show (0 : UInt32) ≤ 1; decide, flen := by simp, lineL := by simp, line240 := fun _ => h.line240 (Or.inl e), line0 := by simp,
                        none := by simp, vbl1 := fun hv' => absurd hv' hv, dead := h.dead }

/-- The schedule at a cycle boundary, unless the model has flagged itself. -/
structure SchS (s : NES) : Prop extends SchW s where
  lt : s.fpos < phPos s s.evIdx

def Sch (s : NES) : Prop := s.unmodelled = true ∨ SchS s

theorem go_unm (n : Nat) (y : NES) : (sched.go n y).unmodelled = y.unmodelled := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    simp only [sched.go]
    split
    · rfl
    · split
      · rfl
      · rw [ih]

theorem sched_unm (y : NES) : (sched y).unmodelled = y.unmodelled := by
  simp only [sched, go_unm]

theorem fetchSprite0_unm (x : NES) : (fetchSprite0 x).unmodelled = x.unmodelled := by
  unfold fetchSprite0; dsimp only
  repeat' split
  all_goals rfl

theorem lineEndMid_unm (x : NES) : (lineEndMid x).unmodelled = x.unmodelled := by
  unfold lineEndMid
  split
  · exact fetchSprite0_unm _
  · rfl

theorem handleEv_mono (x : NES) (h : x.unmodelled = true) : (handleEv x).unmodelled = true := by
  unfold handleEv
  split
  · rw [sched_unm]; exact h
  split
  · rw [sched_unm]; exact h
  split
  · rw [sched_unm]; exact h
  · rw [sched_unm]; exact h
  · rw [sched_unm]; simp [h]
  · rw [sched_unm]; exact h
  · rw [sched_unm]; exact h
  · dsimp only
    repeat' split
    all_goals rw [sched_unm]
    all_goals simp [fetchSprite0_unm, h]
  · rw [sched_unm]; exact h
  · exact h

theorem events_go (n : Nat) (x : NES) (h : x.unmodelled = true ∨ SchW x) : (ppuEvents.go n x).unmodelled = true ∨ SchS (ppuEvents.go n x) := by
  induction n generalizing x with
  | zero => exact Or.inl rfl
  | succ n ih =>
    simp only [ppuEvents.go]
    split
    · rename_i hdue
      apply ih
      rcases h with h | h
      · exact Or.inl (handleEv_mono x h)
      · exact Or.inr (sch_handleEv x h hdue)
    · rename_i hdue
      rcases h with h | h
      · exact Or.inl h
      · refine Or.inr { toSchW := h, lt := ?_ }
        have h1 := h.nle
        have h2 : x.fpos < x.nextEv := by revert hdue; simp only [ge_iff_le]; generalize x.fpos = f; generalize x.nextEv = q; bv_decide (config := { enums := false })
        revert h1 h2
        generalize x.fpos = f; generalize x.nextEv = q; generalize phPos x x.evIdx = r
        bv_decide (config := { enums := false })

/-- One dot. -/
theorem sch_adv (s : NES) (h : Sch s) : Sch (advancePpu s 1) := by
  simp only [advancePpu, Sch]
  have hw : s.unmodelled = true ∨ SchW { s with fpos := s.fpos + 1 } := by
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr { idx := h.idx, le := ?_, nle := h.nle, ncase := h.ncase, skip := h.skip, flen := h.flen, lineL := h.lineL, line240 := h.line240, line0 := h.line0, none := h.none, vbl1 := h.vbl1, dead := h.dead }
      have hlt := h.lt
      show s.fpos + 1 ≤ phPos { s with fpos := s.fpos + 1 } s.evIdx
      have e : phPos { s with fpos := s.fpos + 1 } s.evIdx = phPos s s.evIdx := rfl
      rw [e]
      revert hlt
      generalize s.fpos = f; generalize phPos s s.evIdx = r
      bv_decide (config := { enums := false })
  split
  · exact events_go 64 _ hw
  · rename_i hdue
    have := events_go 1 { s with fpos := s.fpos + 1 } hw
    simp only [ppuEvents.go, hdue, if_false] at this
    exact this

/-- `y` is `x` as far as the schedule looks. -/
structure SV (x y : NES) : Prop where
  idx : y.evIdx = x.evIdx
  fpos : y.fpos = x.fpos
  next : y.nextEv = x.nextEv
  skip : y.skipped = x.skipped
  flen : y.flen = x.flen
  line : y.line = x.line
  hit : y.hitPos = x.hitPos
  ovf : y.overflowPos = x.overflowPos
  dead : y.dead = x.dead
  vbl : y.vbl = true → x.vbl = true
  unm : x.unmodelled = true → y.unmodelled = true

theorem phPos_of_sv {x y : NES} (h : SV x y) : phPos y y.evIdx = phPos x x.evIdx := by
  simp only [phPos, NES.line0, h.idx, h.skip, h.line, h.flen]

theorem Sch.of_sv {x y : NES} (hs : Sch x) (h : SV x y) : Sch y := by
  rcases hs with hs | hs
  · exact Or.inl (h.unm hs)
  · have hp := phPos_of_sv h
    exact Or.inr {
      idx := by rw [h.idx]; exact hs.idx
      le := by rw [h.fpos, hp]; exact hs.le
      nle := by rw [h.next, hp]; exact hs.nle
      ncase := by rw [h.next, hp, h.hit, h.ovf]; exact hs.ncase
      skip := by rw [h.skip]; exact hs.skip
      flen := by rw [h.idx, h.flen, h.skip]; exact hs.flen
      lineL := by rw [h.idx, h.line]; exact hs.lineL
      line240 := by rw [h.idx, h.line]; exact hs.line240
      line0 := by rw [h.idx, h.line]; exact hs.line0
      none := by rw [h.idx, h.hit, h.ovf]; exact hs.none
      vbl1 := fun hv => by rw [h.idx]; exact hs.vbl1 (h.vbl hv)
      dead := by rw [h.dead]; exact hs.dead
      lt := by rw [h.fpos, hp]; exact hs.lt }

theorem sv_refl (x : NES) : SV x x := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩

theorem sv_regRead (x : NES) (a : UInt16) : SV x (ppuRegRead x a).2 := by
  unfold ppuRegRead
  dsimp only
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, id⟩
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, by intro h; simp [show x.ioDecay.unmodelled = x.unmodelled from rfl, h]⟩
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, by intro h; simp [show x.ioDecay.unmodelled = x.unmodelled from rfl, h]⟩
    | skip

theorem sv_mem (x : NES) (a : UInt16) (b : UInt8) : SV x (ppuMemWrite x a b) := by
  unfold ppuMemWrite
  dsimp only
  repeat' first
    | exact sv_refl x
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
    | split

/-- A register write other than `$2001` during a visible line. -/
theorem sv_regWrite (x : NES) (a : UInt16) (b : UInt8) (hr : (a &&& 7 == 1) = false) : SV x (ppuRegWrite x a b) := by
  have hm := fun x a b => sv_mem x a b
  have hm1 := fun x a b => (hm x a b).idx
  have hm2 := fun x a b => (hm x a b).fpos
  have hm3 := fun x a b => (hm x a b).next
  have hm4 := fun x a b => (hm x a b).skip
  have hm5 := fun x a b => (hm x a b).flen
  have hm6 := fun x a b => (hm x a b).line
  have hm7 := fun x a b => (hm x a b).hit
  have hm8 := fun x a b => (hm x a b).ovf
  have hm9 := fun x a b => (hm x a b).dead
  have hmv : ∀ x a b, (ppuMemWrite x a b).vbl = x.vbl := by
    intro x a b
    unfold ppuMemWrite
    dsimp only
    repeat' first | rfl | split
  have hmu : ∀ x a b, (ppuMemWrite x a b).unmodelled = x.unmodelled := by
    intro x a b
    unfold ppuMemWrite
    dsimp only
    repeat' first | rfl | split
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.evIdx, hm1, setOam, ite_self]
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.fpos, hm2, setOam, ite_self]
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.nextEv, hm3, setOam, ite_self]
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.skipped, hm4, setOam, ite_self]
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.flen, hm5, setOam, ite_self]
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.line, hm6, setOam, ite_self]
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.hitPos, hm7, setOam, ite_self]
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.overflowPos, hm8, setOam, ite_self]
  · unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.dead, hm9, setOam, ite_self]
  · intro hv
    have : (ppuRegWrite x a b).vbl = x.vbl := by
      unfold ppuRegWrite; simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.vbl, hmv, setOam, ite_self]
    rw [← this]; exact hv
  · intro hu
    unfold ppuRegWrite
    simp only [hr, Bool.false_eq_true, if_false, apply_ite NES.unmodelled, hmu, setOam, hu, Bool.true_or, ite_self]

theorem reg1_unm (x : NES) (a : UInt16) (b : UInt8) (hu : x.unmodelled = true) : (ppuRegWrite x a b).unmodelled = true := by
  have hmu : ∀ x a b, (ppuMemWrite x a b).unmodelled = x.unmodelled := by
    intro x a b
    unfold ppuMemWrite
    dsimp only
    repeat' first | rfl | split
  unfold ppuRegWrite
  simp only [apply_ite NES.unmodelled, hmu, setOam, sched_unm, hu, Bool.true_or, ite_self]

/-- `$2001`, outside a visible line's sprite phase. -/
theorem sv_reg1 (x : NES) (a : UInt16) (b : UInt8) (hr : a &&& 7 = 1) (hs : SchS x) (he : x.evIdx ≠ 6) : SV x (ppuRegWrite x a b) := by
  have hed : (x.dead != 0) = false := by simp [hs.dead]
  have r0 : ((1 : UInt16) == 0) = false := by decide
  have r1 : ((1 : UInt16) == 1) = true := by decide
  have he5 : (x.evIdx == 5) = false := by
    rcases hs.idx with e | e | e | e | e | e | e <;> rw [e] <;> decide
  have he6 : (x.evIdx == 6) = false := by simpa using he
  have hline : x.line < 240 → ¬ (x.fpos ≥ NES.line0 x + x.line * 341) := by
    intro h1 h2
    have hlt := hs.lt
    have hsk := hs.skip
    rcases hs.idx with e | e | e | e | e | e | e
    · have := hs.line240 (Or.inr (Or.inl e)); rw [this] at h1; exact absurd h1 (by decide)
    · have := hs.line240 (Or.inr (Or.inr (Or.inl e))); rw [this] at h1; exact absurd h1 (by decide)
    · have := hs.line240 (Or.inr (Or.inr (Or.inr e))); rw [this] at h1; exact absurd h1 (by decide)
    · have hl0 := hs.line0 e
      rw [e] at hlt
      simp only [phPos] at hlt
      simp only [NES.line0, hl0] at h2
      revert hlt hsk h2
      generalize x.fpos = f; generalize x.skipped = k
      bv_decide (config := { enums := false })
    · rw [e] at hlt
      simp only [phPos] at hlt
      revert hlt h2
      generalize x.fpos = f; generalize NES.line0 x + x.line * 341 = q
      bv_decide (config := { enums := false })
    · exact absurd e he
    · have := hs.line240 (Or.inl e); rw [this] at h1; exact absurd h1 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, ite_self]
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.fpos, ite_self]
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.nextEv, ite_self]
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.skipped, ite_self]
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.flen, ite_self]
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.line, ite_self]
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.hitPos, ite_self]
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.overflowPos, ite_self]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact absurd hc.1.1.1.2 (hline hc.1.1.1.1.2)
    · rfl
  · unfold ppuRegWrite
    simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.dead, ite_self]
  · intro hv
    have : (ppuRegWrite x a b).vbl = x.vbl := by
      unfold ppuRegWrite
      simp only [hr, r0, r1, hed, he5, he6, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he5, he6, apply_ite NES.vbl, ite_self]
    rw [← this]; exact hv
  · intro hu
    exact reg1_unm x a b hu

theorem sch_of_six {x y : NES} (hs : SchS x) (he : x.evIdx = 6) (h5 : y.evIdx = 5) (f1 : y.fpos = x.fpos) (f2 : y.line = x.line) (f3 : y.skipped = x.skipped)
    (f4 : y.flen = x.flen) (f5 : y.vbl = x.vbl) (f6 : y.dead = x.dead) : Sch (sched y) := by
  have hle := hs.le
  have hlt := hs.lt
  have hv : y.vbl ≠ true := fun hv' => by
    rw [f5] at hv'
    have := hs.vbl1 hv'
    rw [he] at this
    exact absurd this (by decide)
  have hp : phPos { y with evIdx := 6 } 6 = phPos x x.evIdx := by
    rw [he]; simp only [phPos, NES.line0, f2, f3]
  have pre : Pre { y with evIdx := 6 } :=
    { idx := by simp
      le := by simp only []; rw [hp, f1]; exact hle
      skip := by show y.skipped ≤ 1; rw [f3]; exact hs.skip
      flen := fun _ => by show y.flen = 262 * 341 - y.skipped; rw [f4, f3]; exact hs.flen (Or.inr (Or.inl he))
      lineL := fun _ => by show y.line < 240; rw [f2]; exact hs.lineL (Or.inr he)
      line240 := by simp
      line0 := by simp
      none := by simp
      vbl1 := fun hv' => absurd hv' hv
      dead := by show y.dead = 0; rw [f6]; exact hs.dead }
  rw [sched_five y h5 pre]
  have hw := sch_sched _ pre
  refine Or.inr { toSchW := hw, lt := ?_ }
  rw [sched_eq _ pre]
  show y.fpos < phPos { y with evIdx := 6 } 6
  rw [hp, f1]
  exact hlt

/-- `$2001` in a visible line's sprite phase: the hit is rescheduled. -/
theorem sch_reg1_six (x : NES) (a : UInt16) (b : UInt8) (hr : a &&& 7 = 1) (hs : SchS x) (he : x.evIdx = 6) : Sch (ppuRegWrite x a b) := by
  have hed : (x.dead != 0) = false := by simp [hs.dead]
  have r0 : ((1 : UInt16) == 0) = false := by decide
  have r1 : ((1 : UInt16) == 1) = true := by decide
  have h66 : ((6 : UInt8) == 5 || (6 : UInt8) == 6) = true := by decide
  unfold ppuRegWrite
  simp only [hr, r0, r1, hed, Bool.false_and, Bool.or_self, Bool.false_eq_true, if_false, if_true, apply_ite NES.evIdx, he, h66, ite_self]
  split
  · exact sch_of_six hs he rfl rfl rfl rfl rfl rfl rfl
  · exact sch_of_six hs he rfl rfl rfl rfl rfl rfl rfl

theorem sch_regWrite (x : NES) (a : UInt16) (b : UInt8) (h : Sch x) : Sch (ppuRegWrite x a b) := by
  by_cases hr : a &&& 7 = 1
  · rcases h with hu | hs
    · exact Or.inl (reg1_unm x a b hu)
    · by_cases he : x.evIdx = 6
      · exact sch_reg1_six x a b hr hs he
      · exact Sch.of_sv (Or.inr hs) (sv_reg1 x a b hr hs he)
  · exact Sch.of_sv h (sv_regWrite x a b (by simpa using hr))

theorem sch_beginCycle (s : NES) (h : Sch s) : Sch (beginCycle s) := by
  unfold beginCycle
  dsimp only
  apply sch_adv
  split
  · exact Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  · exact Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩

theorem sch_endCycle (s : NES) (h : Sch s) : Sch (endCycle s) := by
  unfold endCycle
  dsimp only
  apply sch_adv
  exact Sch.of_sv (sch_adv s h) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩

theorem sch_tick (s : NES) (h : Sch s) : Sch (tickS s) := sch_endCycle _ (sch_beginCycle _ h)

theorem sv_readMid (x : NES) (a : UInt16) : SV x (readMid x a).2 := by
  unfold readMid
  repeat' split
  · exact sv_refl x
  · exact sv_regRead x a
  all_goals first
    | exact sv_refl x
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, by intro h; simp [h]⟩

theorem sv_readFin (r : UInt8) (x : NES) (a : UInt16) : SV x (readFin r x a).2 := by
  unfold readFin
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  · exact sv_refl x

theorem sch_readCycle (s : NES) (a : UInt16) (h : Sch s) : Sch (readCycle s a).2 := by
  rw [readCycle_eq]
  have h1 := sch_beginCycle s h
  have h2 := Sch.of_sv h1 (sv_readMid (beginCycle s) a)
  have h3 : Sch { (readMid (beginCycle s) a).2 with bus := (readMid (beginCycle s) a).1, padRead := if a == 0x4016 then 1 else if a == 0x4017 then 2 else 0 } :=
    Sch.of_sv h2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  exact Sch.of_sv (sch_endCycle _ h3) (sv_readFin _ _ _)

theorem sch_wrMid (x : NES) (a : UInt16) (b : UInt8) (h : Sch x) : Sch (wrMid x a b) := by
  unfold wrMid
  split
  · exact Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  split
  · exact sch_regWrite x a b h
  split
  · exact Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  split
  · exact Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  split
  · exact Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, by intro _; rfl⟩
  · exact h

theorem sch_wrS (s : NES) (a : UInt16) (b : UInt8) (h : Sch s) : Sch (wrS s a b) := by
  rw [wrS_eq]
  apply sch_endCycle
  apply sch_wrMid
  exact Sch.of_sv (sch_beginCycle s h) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩

theorem sch_oamDma_go (n : Nat) (i : UInt16) (s : NES) (h : Sch s) : Sch (oamDma.go n i s) := by
  induction n generalizing i s with
  | zero => exact h
  | succ n ih =>
    simp only [oamDma.go]
    apply ih
    apply sch_endCycle
    have h1 := sch_readCycle s ((s.dmaPage.toUInt16 <<< 8) ||| i) h
    exact Sch.of_sv (sch_regWrite _ 0x2004 _ (sch_beginCycle _ h1)) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩

theorem sch_oamDma (s : NES) (a : UInt16) (h : Sch s) : Sch (oamDma s a) := by
  unfold oamDma
  apply sch_oamDma_go
  have h0 : Sch { s with dmaPending := false, unmodelled := s.unmodelled || rendering s } :=
    Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, by intro hu; simp [hu]⟩
  have h1 := sch_readCycle _ a h0
  split
  · exact sch_readCycle _ a h1
  · exact h1

theorem sch_rdS (s : NES) (a : UInt16) (h : Sch s) : Sch (rdS s a).2 := by
  unfold rdS
  apply sch_readCycle
  split
  · exact sch_oamDma s a h
  · exact h

end Smb.NES

namespace Smb

/-- A program keeps the schedule and the ROM. -/
def Pres {α : Type} (m : StateM NES α) : Prop := ∀ s, (NES.Sch s → NES.Sch (m.run s).2) ∧ (m.run s).2.prg = s.prg

namespace Pres
open CPU

theorem pure {α : Type} (a : α) : Pres (Pure.pure a : StateM NES α) := fun _ => ⟨id, rfl⟩

theorem bind {α β : Type} {m : StateM NES α} {f : α → StateM NES β} (hm : Pres m) (hf : ∀ a, Pres (f a)) : Pres (m >>= f) := by
  intro s
  rw [Sim.run_bind]
  exact ⟨fun h => (hf _ _).1 ((hm s).1 h), (hf _ _).2.trans (hm s).2⟩

theorem ite {α : Type} {c : Prop} [Decidable c] {a b : StateM NES α} (ha : c → Pres a) (hb : ¬c → Pres b) : Pres (if c then a else b) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

theorem getRegs : Pres (getRegs (σ := NES)) := fun _ => ⟨id, rfl⟩
theorem modRegs (f : Regs → Regs) : Pres (modRegs (σ := NES) f) :=
  fun s => ⟨fun h => NES.Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, rfl⟩
theorem rd (a : UInt16) : Pres (rd (σ := NES) a) := fun s => ⟨NES.sch_rdS s a, by
  have hv := NES.BusStable.rdS_view s a
  simp only [NES.BusStable.view, Prod.mk.injEq] at hv
  exact hv.2⟩
theorem wr (a : UInt16) (b : UInt8) : Pres (wr (σ := NES) a b) := fun s => ⟨NES.sch_wrS s a b, by
  have hv := NES.BusStable.wrS_view s a b
  simp only [NES.BusStable.view, Prod.mk.injEq] at hv
  exact hv.2⟩
theorem idle : Pres (idle (σ := NES)) := fun s => ⟨NES.sch_tick s, by
  have hv := NES.BusStable.tickS_view s
  simp only [NES.BusStable.view, Prod.mk.injEq] at hv
  exact hv.2⟩
theorem unsupported : Pres (unsupported (σ := NES)) := fun s => ⟨fun _ => Or.inl rfl, rfl⟩
theorem nmiPending : Pres (nmiPending (σ := NES)) := fun _ => ⟨id, rfl⟩
theorem clearNmiPending : Pres (clearNmiPending (σ := NES)) :=
  fun s => ⟨fun h => NES.Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, rfl⟩
theorem nmiPolled : Pres (nmiPolled (σ := NES)) := fun _ => ⟨id, rfl⟩
theorem setNmiPolled (b : Bool) : Pres (setNmiPolled (σ := NES) b) :=
  fun s => ⟨fun h => NES.Sch.of_sv h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, rfl⟩

syntax "pres_tac" : tactic
macro_rules
  | `(tactic| pres_tac) => `(tactic| (
      sim_unfold
      repeat' (first
        | with_reducible exact Pres.getRegs | with_reducible exact Pres.modRegs _
        | with_reducible exact Pres.rd _ | with_reducible exact Pres.wr _ _
        | with_reducible exact Pres.idle | with_reducible exact Pres.unsupported
        | with_reducible exact Pres.clearNmiPending | with_reducible exact Pres.pure _
        | with_reducible exact Pres.setNmiPolled _ | with_reducible exact Pres.nmiPending | with_reducible exact Pres.nmiPolled
        | with_reducible refine Pres.bind ?_ (fun _ => ?_)
        | with_reducible refine Pres.ite (fun _ => ?_) (fun _ => ?_)
        | split
        | dsimp only
        | simp only [Bool.or_self, Bool.false_or, Bool.or_false])))

end Pres
end Smb
