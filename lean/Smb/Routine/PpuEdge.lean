import Smb.Routine.PpuSchedExec

/-!
# Vblank's rising edge

When vblank rises, the frame position is exactly 342, and nothing else happens until dot 7162. So an NMI that the rise triggers is taken with the position known.
-/
set_option maxRecDepth 20000
namespace Smb.NES

theorem go_fields (n : Nat) (y : NES) : (sched.go n y).vbl = y.vbl ∧ (sched.go n y).fpos = y.fpos := by
  induction n generalizing y with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [sched.go]
    split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · exact ih _

theorem sched_fields (y : NES) : (sched y).vbl = y.vbl ∧ (sched y).fpos = y.fpos := by
  simp only [sched]
  exact go_fields 9 y

/-- A due event raises vblank only at dot 342. -/
theorem handleEv_vbl (x : NES) (h : SchW x) (hdue : x.nextEv ≤ x.fpos) (hv : x.vbl = false) (hr : (handleEv x).vbl = true) :
    x.fpos = 342 ∧ (handleEv x).fpos = 342 := by
  by_cases hn1 : (x.hitPos == x.nextEv) = true
  · exfalso
    unfold handleEv at hr
    rw [if_pos hn1, (sched_fields _).1] at hr
    rw [show x.vbl = _ from hv] at hr
    simp at hr
  by_cases hn2 : (x.overflowPos == x.nextEv) = true
  · exfalso
    unfold handleEv at hr
    rw [if_neg hn1, if_pos hn2, (sched_fields _).1] at hr
    rw [show x.vbl = _ from hv] at hr
    simp at hr
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
  rcases h.idx with e | e | e | e | e | e | e
  · rw [e] at hfp
    simp only [phPos] at hfp
    unfold handleEv
    rw [if_neg hn1, if_neg hn2]
    simp only [e]
    exact ⟨hfp, by rw [(sched_fields _).2]; exact hfp⟩
  all_goals exfalso
  · unfold handleEv at hr
    rw [if_neg hn1, if_neg hn2] at hr
    simp only [e] at hr
    rw [(sched_fields _).1] at hr
    simp at hr
  · unfold handleEv at hr
    rw [if_neg hn1, if_neg hn2] at hr
    simp only [e] at hr
    rw [(sched_fields _).1] at hr
    rw [show x.vbl = _ from hv] at hr
    simp at hr
  · unfold handleEv at hr
    rw [if_neg hn1, if_neg hn2] at hr
    simp only [e] at hr
    rw [(sched_fields _).1] at hr
    rw [show x.vbl = _ from hv] at hr
    simp at hr
  · unfold handleEv at hr
    rw [if_neg hn1, if_neg hn2] at hr
    simp only [e] at hr
    rw [(sched_fields _).1] at hr
    rw [show x.vbl = _ from hv] at hr
    simp at hr
  · rw [handle_six x e hn1 hn2] at hr
    dsimp only at hr
    obtain ⟨_, _, _, _, _, m6, _⟩ := lineEndMid_sch x
    split at hr
    · rw [(sched_fields _).1] at hr
      show False
      have : (lineEndMid x).vbl = true := hr
      rw [m6, hv] at this
      simp at this
    · rw [(sched_fields _).1] at hr
      have : (lineEndMid x).vbl = true := hr
      rw [m6, hv] at this
      simp at this
  · unfold handleEv at hr
    rw [if_neg hn1, if_neg hn2] at hr
    simp only [e] at hr
    rw [(sched_fields _).1] at hr
    rw [show x.vbl = _ from hv] at hr
    simp at hr

/-- Over one dot, vblank rises only at position 342. -/
theorem events_rise (n : Nat) (x : NES) (h : SchW x) (hq : x.vbl = true → x.fpos = 342) (hu : (ppuEvents.go n x).unmodelled = false)
    (hr : (ppuEvents.go n x).vbl = true) : (ppuEvents.go n x).fpos = 342 := by
  induction n generalizing x with
  | zero => simp [ppuEvents.go] at hu
  | succ n ih =>
    simp only [ppuEvents.go] at hu hr ⊢
    split at hu
    · rename_i hdue
      rw [if_pos hdue] at hr ⊢
      have hdue' : x.nextEv ≤ x.fpos := hdue
      refine ih _ (sch_handleEv x h hdue') ?_ hu hr
      intro hv
      cases hx : x.vbl with
      | false => exact (handleEv_vbl x h hdue' hx hv).2
      | true =>
        exfalso
        have e1 := h.vbl1 hx
        have hf := hq hx
        have hn := h.none (Or.inr e1)
        have hnle := h.nle
        have hc := h.ncase
        rw [e1] at hnle hc
        simp only [phPos] at hnle hc
        rw [hf] at hdue'
        rcases hc with c | c | c
        · rw [c] at hdue'; exact absurd hdue' (by decide)
        · rw [c, hn.1] at hdue'; exact absurd hdue' (by decide)
        · rw [c, hn.2] at hdue'; exact absurd hdue' (by decide)
    · rename_i hdue
      rw [if_neg hdue] at hr ⊢
      exact hq hr

theorem go_line (n : Nat) (y : NES) : (sched.go n y).nmiLine = y.nmiLine := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    simp only [sched.go]
    split
    · rfl
    · split
      · rfl
      · rw [ih]

theorem sched_line (y : NES) : (sched y).nmiLine = y.nmiLine := by
  simp only [sched]
  exact go_line 9 y

theorem fetchSprite0_line (x : NES) : (fetchSprite0 x).nmiLine = x.nmiLine := by
  unfold fetchSprite0; dsimp only
  repeat' split
  all_goals rfl

theorem handleEv_line (x : NES) : (handleEv x).nmiLine = x.nmiLine := by
  unfold handleEv
  split
  · rw [sched_line]
  split
  · rw [sched_line]
  split
  · rw [sched_line]
  · rw [sched_line]
  · rw [sched_line]
  · rw [sched_line]
  · rw [sched_line]
  · dsimp only
    repeat' split
    all_goals rw [sched_line]
    all_goals simp [fetchSprite0_line]
  · rw [sched_line]
  · rfl

theorem events_line (n : Nat) (x : NES) : (ppuEvents.go n x).nmiLine = x.nmiLine := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [ppuEvents.go]
    split
    · rw [ih, handleEv_line]
    · rfl

theorem events_mono (n : Nat) (x : NES) (h : x.unmodelled = true) : (ppuEvents.go n x).unmodelled = true := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [ppuEvents.go]
    split
    · exact ih _ (handleEv_mono x h)
    · exact h

/-- What one dot does, once the schedule is known. -/
structure Dot (x r : NES) : Prop where
  sch : SchS r
  core : core r = core x
  line : r.nmiLine = x.nmiLine
  rise : x.vbl = false → r.vbl = true → r.fpos = 342
  stay : x.vbl = true → x.fpos.toNat + 1 < 7162 → r.vbl = true ∧ r.fpos.toNat = x.fpos.toNat + 1

theorem nextEv_of_vbl {x : NES} (hs : SchW x) (hv : x.vbl = true) : x.evIdx = 1 ∧ x.nextEv = 7162 := by
  have e1 := hs.vbl1 hv
  have hn := hs.none (Or.inr e1)
  have hnle := hs.nle
  have hc := hs.ncase
  rw [e1] at hnle hc
  simp only [phPos] at hnle hc
  refine ⟨e1, ?_⟩
  rcases hc with c | c | c
  · rw [c]; rfl
  · rw [c, hn.1] at hnle; exact absurd hnle (by decide)
  · rw [c, hn.2] at hnle; exact absurd hnle (by decide)

theorem dot (x : NES) (hs : SchS x) (hu : (advancePpu x 1).unmodelled = false) : Dot x (advancePpu x 1) := by
  have hsc := sch_adv x (Or.inr hs)
  have hs' : SchS (advancePpu x 1) := by
    rcases hsc with h | h
    · rw [hu] at h; cases h
    · exact h
  refine ⟨hs', ?_, ?_, ?_, ?_⟩
  · exact core_advancePpu x 1
  · simp only [advancePpu, ppuEvents]
    split
    · rw [events_line]
    · rfl
  · intro hv hr
    simp only [advancePpu, ppuEvents] at hr hu ⊢
    split at hr
    · rename_i hdue
      rw [if_pos hdue] at hu ⊢
      refine events_rise 64 _ ?_ ?_ hu hr
      · refine { idx := hs.idx, le := ?_, nle := hs.nle, ncase := hs.ncase, skip := hs.skip, flen := hs.flen, lineL := hs.lineL, line240 := hs.line240, line0 := hs.line0, none := hs.none, vbl1 := hs.vbl1, dead := hs.dead }
        have hlt := hs.lt
        show x.fpos + 1 ≤ phPos { x with fpos := x.fpos + 1 } x.evIdx
        have e : phPos { x with fpos := x.fpos + 1 } x.evIdx = phPos x x.evIdx := rfl
        rw [e]
        revert hlt
        generalize x.fpos = f; generalize phPos x x.evIdx = r
        bv_decide (config := { enums := false })
      · intro hv2
        rw [show x.vbl = _ from hv] at hv2
        cases hv2
    · exfalso
      rw [show x.vbl = _ from hv] at hr
      cases hr
  · intro hv hn
    have hN := (nextEv_of_vbl hs.toSchW hv).2
    have hplus : (x.fpos + 1).toNat = x.fpos.toNat + 1 := by
      rw [UInt32.toNat_add]
      have : (1 : UInt32).toNat = 1 := rfl
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have hlt : ¬ (x.fpos + 1 ≥ x.nextEv) := by
      rw [hN]
      intro h
      have h' : (7162 : UInt32).toNat ≤ (x.fpos + 1).toNat := h
      rw [hplus] at h'
      have : (7162 : UInt32).toNat = 7162 := rfl
      omega
    simp only [advancePpu, hlt, if_false]
    exact ⟨hv, hplus⟩

theorem adv_mono (x : NES) (h : x.unmodelled = true) : (advancePpu x 1).unmodelled = true := by
  simp only [advancePpu, ppuEvents]
  split
  · exact events_mono 64 _ h
  · exact h

theorem cf {s t : NES} (h : core s = core t) :
    s.pc = t.pc ∧ s.a = t.a ∧ s.x = t.x ∧ s.y = t.y ∧ s.s = t.s ∧ s.p = t.p ∧ s.ram = t.ram ∧ s.prg = t.prg ∧
    s.ctrl = t.ctrl ∧ s.dmaPending = t.dmaPending ∧ s.nmiPending = t.nmiPending ∧ s.nmiPolled = t.nmiPolled ∧
    s.cyc = t.cyc := by
  simpa only [core, Core.mk.injEq] using h

theorem SchS.of_sv {x y : NES} (hs : SchS x) (h : SV x y) : SchS y := by
  have hp := phPos_of_sv h
  exact {
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

/-- What a cycle's start does. -/
theorem begin_cycle (x : NES) (hs : SchS x) (hu : (beginCycle x).unmodelled = false) :
    SchS (beginCycle x) ∧ (beginCycle x).nmiLine = x.nmiLine ∧ (beginCycle x).nmiPending = x.nmiPending ∧ (beginCycle x).nmiPolled = x.nmiPolled ∧
    (beginCycle x).ctrl = x.ctrl ∧ (beginCycle x).dmaPending = x.dmaPending ∧
    (x.vbl = false → (beginCycle x).vbl = true → (beginCycle x).fpos = 342) ∧
    (x.vbl = true → x.fpos.toNat + 1 < 7162 → (beginCycle x).vbl = true ∧ (beginCycle x).fpos.toNat = x.fpos.toNat + 1) := by
  have key : ∀ x' : NES, SchS x' → x'.nmiLine = x.nmiLine → x'.nmiPending = x.nmiPending → x'.nmiPolled = x.nmiPolled → x'.ctrl = x.ctrl →
      x'.dmaPending = x.dmaPending → x'.vbl = x.vbl → x'.fpos = x.fpos → (advancePpu x' 1).unmodelled = false →
      SchS (advancePpu x' 1) ∧ (advancePpu x' 1).nmiLine = x.nmiLine ∧ (advancePpu x' 1).nmiPending = x.nmiPending ∧ (advancePpu x' 1).nmiPolled = x.nmiPolled ∧
      (advancePpu x' 1).ctrl = x.ctrl ∧ (advancePpu x' 1).dmaPending = x.dmaPending ∧
      (x.vbl = false → (advancePpu x' 1).vbl = true → (advancePpu x' 1).fpos = 342) ∧
      (x.vbl = true → x.fpos.toNat + 1 < 7162 → (advancePpu x' 1).vbl = true ∧ (advancePpu x' 1).fpos.toNat = x.fpos.toNat + 1) := by
    intro x' h1 h2 h3 h4 h5 h6 h7 h8 hu'
    have d := dot x' h1 hu'
    have c := cf d.core
    refine ⟨d.sch, d.line.trans h2, c.2.2.2.2.2.2.2.2.2.2.1.trans h3, c.2.2.2.2.2.2.2.2.2.2.2.1.trans h4, c.2.2.2.2.2.2.2.2.1.trans h5, c.2.2.2.2.2.2.2.2.2.1.trans h6, ?_, ?_⟩
    · intro hv hr; exact d.rise (h7.trans hv) hr
    · intro hv hn
      have := d.stay (h7.trans hv) (by rw [h8]; exact hn)
      rw [h8] at this
      exact this
  unfold beginCycle at hu ⊢
  dsimp only at hu ⊢
  split at hu
  · rw [if_pos (by assumption)]
    exact key _ (SchS.of_sv hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩) rfl rfl rfl rfl rfl rfl rfl hu
  · rw [if_neg (by assumption)]
    exact key _ (SchS.of_sv hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩) rfl rfl rfl rfl rfl rfl rfl hu

/-- What a cycle's end does, for a state on the bus side `y`. `A` is the frame position just before the line is sampled. -/
theorem end_cycle (y : NES) (hs : SchS y) (hu : (endCycle y).unmodelled = false) :
    ∃ av : Bool, SchS (endCycle y) ∧ (endCycle y).nmiLine = (av && y.ctrl &&& 0x80 != 0) ∧ (endCycle y).nmiPolled = y.nmiPending ∧
      (endCycle y).nmiPending = (y.nmiPending || ((av && y.ctrl &&& 0x80 != 0) && !y.nmiLine)) ∧
      (endCycle y).ctrl = y.ctrl ∧ (endCycle y).dmaPending = y.dmaPending ∧
      (y.vbl = true → y.fpos.toNat + 2 < 7162 → av = true ∧ (endCycle y).vbl = true ∧ (endCycle y).fpos.toNat = y.fpos.toNat + 2) ∧
      (y.vbl = false → (av = true → (endCycle y).vbl = true ∧ (endCycle y).fpos.toNat ≤ 343) ∧ (av = false → (endCycle y).vbl = true → (endCycle y).fpos = 342)) := by
  obtain ⟨A, hA⟩ : ∃ A, A = advancePpu y 1 := ⟨_, rfl⟩
  have hE : endCycle y = advancePpu { A with nmiPolled := A.nmiPending, nmiPending := A.nmiPending || ((A.vbl && A.ctrl &&& 0x80 != 0) && !A.nmiLine), nmiLine := A.vbl && A.ctrl &&& 0x80 != 0 } 1 := by rw [hA]; rfl
  rw [hE] at hu ⊢
  obtain ⟨B, hB⟩ : ∃ B, B = { A with nmiPolled := A.nmiPending, nmiPending := A.nmiPending || ((A.vbl && A.ctrl &&& 0x80 != 0) && !A.nmiLine), nmiLine := A.vbl && A.ctrl &&& 0x80 != 0 } := ⟨_, rfl⟩
  rw [← hB] at hu ⊢
  have hBu : B.unmodelled = false := by
    cases h : B.unmodelled with
    | false => rfl
    | true => rw [adv_mono B h] at hu; cases hu
  have hAu : A.unmodelled = false := by rw [hB] at hBu; exact hBu
  have dA := dot y hs (by rw [← hA]; exact hAu)
  rw [← hA] at dA
  have cA := cf dA.core
  have hSB : SchS B := by
    rw [hB]
    exact SchS.of_sv dA.sch ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  have dB := dot B hSB hu
  have cB := cf dB.core
  have hctrl : A.ctrl = y.ctrl := cA.2.2.2.2.2.2.2.2.1
  have hpen : A.nmiPending = y.nmiPending := cA.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨A.vbl, dB.sch, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dB.line, hB]; simp only [hctrl]
  · rw [cB.2.2.2.2.2.2.2.2.2.2.2.1, hB]; exact hpen
  · rw [cB.2.2.2.2.2.2.2.2.2.2.1, hB]; simp only [hpen, hctrl, dA.line]
  · rw [cB.2.2.2.2.2.2.2.2.1, hB]; exact hctrl
  · rw [cB.2.2.2.2.2.2.2.2.2.1, hB]; exact cA.2.2.2.2.2.2.2.2.2.1
  · intro hv hn
    obtain ⟨a1, a2⟩ := dA.stay hv (by omega)
    have hBv : B.vbl = true := by rw [hB]; exact a1
    have hBf : B.fpos = A.fpos := by rw [hB]
    obtain ⟨b1, b2⟩ := dB.stay hBv (by rw [hBf, a2]; omega)
    exact ⟨a1, b1, by rw [b2, hBf, a2]⟩
  · intro hv
    constructor
    · intro hav
      have hf := dA.rise hv hav
      have hBv : B.vbl = true := by rw [hB]; exact hav
      have hBf : B.fpos = A.fpos := by rw [hB]
      have hn : B.fpos.toNat + 1 < 7162 := by rw [hBf, hf]; decide
      obtain ⟨b1, b2⟩ := dB.stay hBv hn
      refine ⟨b1, ?_⟩
      rw [b2, hBf, hf]
      decide
    · intro hav hr
      have hBv : B.vbl = false := by rw [hB]; exact hav
      exact dB.rise hBv hr

theorem end_mono (y : NES) (h : y.unmodelled = true) : (endCycle y).unmodelled = true := by
  unfold endCycle
  exact adv_mono _ (adv_mono y h)

/-- The bus side of a cycle, between its start and end. -/
structure MidOK (b y : NES) : Prop where
  sv : SV b y
  line : y.nmiLine = b.nmiLine
  pend : y.nmiPending = b.nmiPending
  ctrl : y.ctrl = b.ctrl
  dma : y.dmaPending = b.dmaPending

/-- With NMI generation off: nothing latches, and a vblank that is set started recently. -/
def Off (x : NES) (F : Nat) : Prop := x.nmiLine = false ∧ x.nmiPending = false ∧ (x.vbl = true → x.fpos.toNat ≤ F)

theorem off_cycle {x y : NES} {F : Nat} (hs : SchS x) (hc : x.ctrl &&& 0x80 = 0) (hO : Off x F) (hF : 344 ≤ F) (hF2 : F ≤ 6000)
    (hm : MidOK (beginCycle x) y) (hu : (endCycle y).unmodelled = false) :
    SchS (endCycle y) ∧ (endCycle y).ctrl = x.ctrl ∧ (endCycle y).dmaPending = x.dmaPending ∧ Off (endCycle y) (F + 3) ∧ (endCycle y).nmiPolled = false := by
  have hyu : y.unmodelled = false := by
    cases h : y.unmodelled with
    | false => rfl
    | true => rw [end_mono y h] at hu; cases hu
  have hbu : (beginCycle x).unmodelled = false := by
    cases h : (beginCycle x).unmodelled with
    | false => rfl
    | true => rw [hm.sv.unm h] at hyu; cases hyu
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := begin_cycle x hs hbu
  have hSy := SchS.of_sv b1 hm.sv
  obtain ⟨av, e1, e2, e3, e4, e5, e6, e7, e8⟩ := end_cycle y hSy hu
  have hcy : (y.ctrl &&& 0x80 != 0) = false := by rw [hm.ctrl, b5, hc]; decide
  have hly : y.nmiLine = false := by rw [hm.line, b2]; exact hO.1
  have hpy : y.nmiPending = false := by rw [hm.pend, b3]; exact hO.2.1
  refine ⟨e1, by rw [e5, hm.ctrl, b5], by rw [e6, hm.dma, b6], ⟨?_, ?_, ?_⟩, by rw [e3, hpy]⟩
  · rw [e2, hcy]; simp
  · rw [e4, hpy, hcy]; simp
  · intro hv
    cases hyv : y.vbl with
    | true =>
      have hbv : (beginCycle x).vbl = true := hm.sv.vbl hyv
      have hfy : y.fpos.toNat ≤ F + 1 := by
        rw [hm.sv.fpos]
        cases hxv : x.vbl with
        | true =>
          have hb := hO.2.2 hxv
          rw [(b8 hxv (by omega)).2]; omega
        | false =>
          rw [b7 hxv hbv]
          have : (342 : UInt32).toNat = 342 := rfl
          omega
      have := (e7 hyv (by omega)).2.2
      omega
    | false =>
      obtain ⟨g1, g2⟩ := e8 hyv
      cases hav : av with
      | true =>
        have := (g1 hav).2
        omega
      | false =>
        have := g2 hav hv
        rw [this]
        have : (342 : UInt32).toNat = 342 := rfl
        omega

/-- With NMI generation on: quiet; vblank risen and not yet seen; or seen, with an NMI pending. -/
def St0 (x : NES) : Prop := x.vbl = false ∧ x.nmiLine = false ∧ x.nmiPending = false
def St1 (x : NES) (F : Nat) : Prop := x.vbl = true ∧ x.fpos.toNat ≤ F ∧ x.nmiLine = false ∧ x.nmiPending = false
def St2 (x : NES) (F : Nat) : Prop := x.vbl = true ∧ x.fpos.toNat ≤ F ∧ x.nmiLine = true ∧ x.nmiPending = true

/-- The common part of a cycle with NMI generation on, ending from a state whose line and pending bits are known. -/
theorem on_end {y : NES} (hSy : SchS y) (hc : y.ctrl &&& 0x80 ≠ 0) (hu : (endCycle y).unmodelled = false) :
    let r := endCycle y
    SchS r ∧ r.ctrl = y.ctrl ∧ r.dmaPending = y.dmaPending ∧ r.nmiPolled = y.nmiPending ∧
    (y.vbl = true → y.fpos.toNat + 2 < 7162 → r.vbl = true ∧ r.fpos.toNat = y.fpos.toNat + 2 ∧ r.nmiLine = true ∧ r.nmiPending = (y.nmiPending || !y.nmiLine)) ∧
    (y.vbl = false → y.nmiLine = false → y.nmiPending = false → St0 r ∨ St1 r 342 ∨ St2 r 343) := by
  obtain ⟨av, e1, e2, e3, e4, e5, e6, e7, e8⟩ := end_cycle y hSy hu
  have hcy : (y.ctrl &&& 0x80 != 0) = true := by simpa using hc
  refine ⟨e1, e5, e6, e3, ?_, ?_⟩
  · intro hv hn
    obtain ⟨a1, a2, a3⟩ := e7 hv hn
    refine ⟨a2, a3, ?_, ?_⟩
    · rw [e2, a1, hcy]; rfl
    · rw [e4, a1, hcy]; simp
  · intro hv hl hp
    obtain ⟨g1, g2⟩ := e8 hv
    cases hav : av with
    | true =>
      obtain ⟨v1, v2⟩ := g1 hav
      refine Or.inr (Or.inr ⟨v1, v2, ?_, ?_⟩)
      · rw [e2, hav, hcy]; rfl
      · rw [e4, hav, hcy, hl, hp]; simp
    | false =>
      have hline : (endCycle y).nmiLine = false := by rw [e2, hav]; simp
      have hpend : (endCycle y).nmiPending = false := by rw [e4, hav, hp]; simp
      cases hvr : (endCycle y).vbl with
      | false => exact Or.inl ⟨hvr, hline, hpend⟩
      | true =>
        have hf := g2 hav hvr
        refine Or.inr (Or.inl ⟨hvr, ?_, hline, hpend⟩)
        rw [hf]
        exact Nat.le_refl _

/-- A cycle with NMI generation on, as the stages move. -/
structure OnCyc (x y : NES) : Prop where
  hs : SchS x
  hc : x.ctrl &&& 0x80 ≠ 0
  hm : MidOK (beginCycle x) y
  vbl : y.vbl = (beginCycle x).vbl
  hu : (endCycle y).unmodelled = false

theorem OnCyc.base {x y : NES} (h : OnCyc x y) :
    SchS (beginCycle x) ∧ SchS y ∧ y.ctrl &&& 0x80 ≠ 0 ∧ y.ctrl = x.ctrl ∧ y.dmaPending = x.dmaPending ∧ y.nmiLine = x.nmiLine ∧ y.nmiPending = x.nmiPending ∧
    (x.vbl = false → y.vbl = true → y.fpos = 342) ∧ (x.vbl = true → x.fpos.toNat + 1 < 7162 → y.vbl = true ∧ y.fpos.toNat = x.fpos.toNat + 1) := by
  have hyu : y.unmodelled = false := by
    cases hh : y.unmodelled with
    | false => rfl
    | true => have := h.hu; rw [end_mono y hh] at this; cases this
  have hbu : (beginCycle x).unmodelled = false := by
    cases hh : (beginCycle x).unmodelled with
    | false => rfl
    | true => rw [h.hm.sv.unm hh] at hyu; cases hyu
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := begin_cycle x h.hs hbu
  have hS := SchS.of_sv b1 h.hm.sv
  refine ⟨b1, hS, by rw [h.hm.ctrl, b5]; exact h.hc, by rw [h.hm.ctrl, b5], by rw [h.hm.dma, b6], by rw [h.hm.line, b2], by rw [h.hm.pend, b3], ?_, ?_⟩
  · intro hv hr
    rw [h.vbl] at hr
    rw [h.hm.sv.fpos]
    exact b7 hv hr
  · intro hv hn
    obtain ⟨c1, c2⟩ := b8 hv hn
    refine ⟨by rw [h.vbl]; exact c1, by rw [h.hm.sv.fpos]; exact c2⟩

/-- Quiet: it stays quiet, or vblank rises. -/
theorem on0 {x y : NES} (h : OnCyc x y) (hq : St0 x) :
    SchS (endCycle y) ∧ (endCycle y).ctrl = x.ctrl ∧ (endCycle y).dmaPending = x.dmaPending ∧ (endCycle y).nmiPolled = false ∧
    (St0 (endCycle y) ∨ St1 (endCycle y) 344 ∨ St2 (endCycle y) 344) := by
  obtain ⟨_, s1, s2, s3, s4, s5, s6, s7, _⟩ := h.base
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := on_end s1 s2 h.hu
  have hl : y.nmiLine = false := s5.trans hq.2.1
  have hp : y.nmiPending = false := s6.trans hq.2.2
  refine ⟨r1, r2.trans s3, r3.trans s4, r4.trans hp, ?_⟩
  cases hyv : y.vbl with
  | true =>
    have hf := s7 hq.1 hyv
    have hn : y.fpos.toNat + 2 < 7162 := by rw [hf]; decide
    obtain ⟨a1, a2, a3, a4⟩ := r5 hyv hn
    refine Or.inr (Or.inr ⟨a1, ?_, a3, ?_⟩)
    · rw [a2, hf]; decide
    · rw [a4, hp, hl]; rfl
  | false =>
    rcases r6 hyv hl hp with g | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
    · exact Or.inl g
    · exact Or.inr (Or.inl ⟨a, by omega, c, d⟩)
    · exact Or.inr (Or.inr ⟨a, by omega, c, d⟩)

/-- Risen: the line is seen, and an NMI goes pending. -/
theorem on1 {x y : NES} {F : Nat} (h : OnCyc x y) (hq : St1 x F) (hF : F ≤ 6000) :
    SchS (endCycle y) ∧ (endCycle y).ctrl = x.ctrl ∧ (endCycle y).dmaPending = x.dmaPending ∧ (endCycle y).nmiPolled = false ∧ St2 (endCycle y) (F + 3) := by
  obtain ⟨_, s1, s2, s3, s4, s5, s6, _, s8⟩ := h.base
  obtain ⟨r1, r2, r3, r4, r5, _⟩ := on_end s1 s2 h.hu
  obtain ⟨hv, hb, hl0, hp0⟩ := hq
  obtain ⟨y1, y2⟩ := s8 hv (by omega)
  obtain ⟨a1, a2, a3, a4⟩ := r5 y1 (by omega)
  refine ⟨r1, r2.trans s3, r3.trans s4, by rw [r4, s6, hp0], a1, by omega, a3, ?_⟩
  rw [a4, s6, s5, hp0, hl0]; rfl

/-- Pending: the poll sees it. -/
theorem on2 {x y : NES} {F : Nat} (h : OnCyc x y) (hq : St2 x F) (hF : F ≤ 6000) :
    SchS (endCycle y) ∧ (endCycle y).ctrl = x.ctrl ∧ (endCycle y).dmaPending = x.dmaPending ∧ (endCycle y).nmiPolled = true ∧ St2 (endCycle y) (F + 3) := by
  obtain ⟨_, s1, s2, s3, s4, s5, s6, _, s8⟩ := h.base
  obtain ⟨r1, r2, r3, r4, r5, _⟩ := on_end s1 s2 h.hu
  obtain ⟨hv, hb, hl0, hp0⟩ := hq
  obtain ⟨y1, y2⟩ := s8 hv (by omega)
  obtain ⟨a1, a2, a3, a4⟩ := r5 y1 (by omega)
  refine ⟨r1, r2.trans s3, r3.trans s4, by rw [r4, s6, hp0], a1, by omega, a3, ?_⟩
  rw [a4, s6, hp0]; rfl

theorem begin_mono (x : NES) (h : x.unmodelled = true) : (beginCycle x).unmodelled = true := by
  unfold beginCycle
  dsimp only
  apply adv_mono
  split <;> exact h

theorem read_mono (x : NES) (a : UInt16) (h : x.unmodelled = true) : (readCycle x a).2.unmodelled = true := by
  rw [readCycle_eq]
  apply (sv_readFin _ _ _).unm
  apply end_mono
  exact (sv_readMid _ a).unm (begin_mono x h)

/-- The read side of a cycle at RAM or ROM. -/
theorem read_mid (x : NES) (a : UInt16) (ha : a < 0x2000 ∨ 0x8000 ≤ a) :
    ∃ y, MidOK (beginCycle x) y ∧ y.vbl = (beginCycle x).vbl ∧ (readCycle x a).2 = endCycle y := by
  have hmid : (readMid (beginCycle x) a).2 = beginCycle x := by
    rcases ha with ha | ha
    · simp [readMid, ha]
    · obtain ⟨g1, g2, g3, g4⟩ := lt_of_ge_8000 ha
      simp [readMid, g1, g2, g3, g4, ha]
  have hfin : ∀ r (y : NES), (readFin r y a).2 = y := by
    intro r y
    unfold readFin
    have : ¬ ((decide (a ≥ 0x2000) && decide (a < 0x4000) && a &&& 7 == 2) = true) := by
      intro h'
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
      obtain ⟨⟨h1, h2⟩, _⟩ := h'
      revert ha h1 h2
      bv_decide (config := { enums := false })
    rw [if_neg this]
  refine ⟨{ beginCycle x with bus := (readMid (beginCycle x) a).1, padRead := if a == 0x4016 then 1 else if a == 0x4017 then 2 else 0 }, ?_, rfl, ?_⟩
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, rfl, rfl, rfl, rfl⟩
  · rw [readCycle_eq, hfin, hmid]

theorem write_mid (x : NES) (a : UInt16) (b : UInt8) (ha : a < 0x2000) :
    ∃ y, MidOK (beginCycle x) y ∧ y.vbl = (beginCycle x).vbl ∧ wrS x a b = endCycle y := by
  have hm : wrMid { beginCycle x with bus := b, padRead := 0 } a b = setRam { beginCycle x with bus := b, padRead := 0 } (a &&& 0x7FF).toNat b := by
    simp [wrMid, ha]
  refine ⟨setRam { beginCycle x with bus := b, padRead := 0 } (a &&& 0x7FF).toNat b, ?_, rfl, ?_⟩
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, rfl, rfl, rfl, rfl⟩
  · rw [wrS_eq, hm]

theorem off_weak {x y : NES} (hs : SchS x) (hc : x.ctrl &&& 0x80 = 0) (hp : x.nmiPending = false)
    (hm : MidOK (beginCycle x) y) (hu : (endCycle y).unmodelled = false) :
    SchS (endCycle y) ∧ (endCycle y).ctrl = x.ctrl ∧ (endCycle y).dmaPending = x.dmaPending ∧ (endCycle y).nmiLine = false ∧ (endCycle y).nmiPending = false ∧ (endCycle y).nmiPolled = false := by
  have hyu : y.unmodelled = false := by
    cases h : y.unmodelled with
    | false => rfl
    | true => rw [end_mono y h] at hu; cases hu
  have hbu : (beginCycle x).unmodelled = false := by
    cases h : (beginCycle x).unmodelled with
    | false => rfl
    | true => rw [hm.sv.unm h] at hyu; cases hyu
  obtain ⟨b1, b2, b3, b4, b5, b6, _, _⟩ := begin_cycle x hs hbu
  have hSy := SchS.of_sv b1 hm.sv
  obtain ⟨av, e1, e2, e3, e4, e5, e6, _, _⟩ := end_cycle y hSy hu
  have hcy : (y.ctrl &&& 0x80 != 0) = false := by rw [hm.ctrl, b5, hc]; decide
  have hpy : y.nmiPending = false := by rw [hm.pend, b3]; exact hp
  refine ⟨e1, by rw [e5, hm.ctrl, b5], by rw [e6, hm.dma, b6], ?_, ?_, by rw [e3, hpy]⟩
  · rw [e2, hcy]; simp
  · rw [e4, hpy, hcy]; simp

/-- `lda $2002`'s read cycle clears vblank: if it is set after that, it has just started. -/
theorem read2002 {x : NES} (hs : SchS x) (hc : x.ctrl &&& 0x80 = 0) (hp : x.nmiPending = false) (hu : (readCycle x 0x2002).2.unmodelled = false) :
    SchS (readCycle x 0x2002).2 ∧ (readCycle x 0x2002).2.ctrl = x.ctrl ∧ (readCycle x 0x2002).2.dmaPending = x.dmaPending ∧ Off (readCycle x 0x2002).2 344 ∧ (readCycle x 0x2002).2.nmiPolled = false := by
  have hyu0 := hu
  rw [readCycle_eq] at hu ⊢
  have hmidv : readMid (beginCycle x) 0x2002 = ppuRegRead (beginCycle x) 0x2002 := by simp [readMid]
  rw [hmidv] at hu ⊢
  obtain ⟨R, hR⟩ : ∃ R, R = ppuRegRead (beginCycle x) 0x2002 := ⟨_, rfl⟩
  rw [← hR] at hu ⊢
  have hRv : R.2.vbl = false := by
    have h7 : ((0x2002 : UInt16) &&& 7) = 2 := by decide
    rw [hR]
    unfold ppuRegRead
    simp only [h7]
  have hRline : R.2.nmiLine = (beginCycle x).nmiLine := by
    rw [hR]
    unfold ppuRegRead
    dsimp only
    repeat' first | rfl | split
  have hRsv : SV (beginCycle x) R.2 := by rw [hR]; exact sv_regRead _ _
  have hRc := cf (show core R.2 = core (beginCycle x) by rw [hR]; exact core_ppuRegRead _ _)
  obtain ⟨y, hy⟩ : ∃ y, y = { R.2 with bus := R.1, padRead := if (0x2002 : UInt16) == 0x4016 then 1 else if (0x2002 : UInt16) == 0x4017 then 2 else 0 } := ⟨_, rfl⟩
  rw [← hy] at hu ⊢
  have hm : MidOK (beginCycle x) y := by
    rw [hy]
    exact ⟨⟨hRsv.idx, hRsv.fpos, hRsv.next, hRsv.skip, hRsv.flen, hRsv.line, hRsv.hit, hRsv.ovf, hRsv.dead, hRsv.vbl, hRsv.unm⟩, hRline, hRc.2.2.2.2.2.2.2.2.2.2.1, hRc.2.2.2.2.2.2.2.2.1, hRc.2.2.2.2.2.2.2.2.2.1⟩
  have hyv : y.vbl = false := by rw [hy]; exact hRv
  have hfinsv : ∀ r, SV (endCycle y) (readFin r (endCycle y) 0x2002).2 := fun r => sv_readFin r _ _
  have hfin : ∀ r, ∃ q, (readFin r (endCycle y) 0x2002).2 = { endCycle y with bus := q, iolatch := q } := by
    intro r
    unfold readFin
    have : (decide ((0x2002 : UInt16) ≥ 0x2000) && decide ((0x2002 : UInt16) < 0x4000) && (0x2002 : UInt16) &&& 7 == 2) = true := by decide
    rw [if_pos this]
    exact ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hfin R.1
  rw [hq] at hu ⊢
  have hEu : (endCycle y).unmodelled = false := hu
  have hyu : y.unmodelled = false := by
    cases h : y.unmodelled with
    | false => rfl
    | true => rw [end_mono y h] at hEu; cases hEu
  have hbu : (beginCycle x).unmodelled = false := by
    cases h : (beginCycle x).unmodelled with
    | false => rfl
    | true => rw [hm.sv.unm h] at hyu; cases hyu
  obtain ⟨b1, b2, b3, b4, b5, b6, _, _⟩ := begin_cycle x hs hbu
  have hSy := SchS.of_sv b1 hm.sv
  obtain ⟨av, e1, e2, e3, e4, e5, e6, _, e8⟩ := end_cycle y hSy hEu
  have hcy : (y.ctrl &&& 0x80 != 0) = false := by rw [hm.ctrl, b5, hc]; decide
  have hpy : y.nmiPending = false := by rw [hm.pend, b3]; exact hp
  obtain ⟨g1, g2⟩ := e8 hyv
  refine ⟨SchS.of_sv e1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, by show (endCycle y).ctrl = x.ctrl; rw [e5, hm.ctrl, b5],
    by show (endCycle y).dmaPending = x.dmaPending; rw [e6, hm.dma, b6], ⟨?_, ?_, ?_⟩, by show (endCycle y).nmiPolled = false; rw [e3, hpy]⟩
  · show (endCycle y).nmiLine = false
    rw [e2, hcy]; simp
  · show (endCycle y).nmiPending = false
    rw [e4, hpy, hcy]; simp
  · intro hv
    have hv' : (endCycle y).vbl = true := hv
    show (endCycle y).fpos.toNat ≤ 344
    cases hav : av with
    | true =>
      have := (g1 hav).2
      omega
    | false =>
      rw [g2 hav hv']
      decide

end Smb.NES
