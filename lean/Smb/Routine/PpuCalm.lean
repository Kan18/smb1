import Smb.Routine.AbsBridge
import Smb.Game

/-!
# The PPU during the handler's first instructions

Just after vblank starts, the next PPU event is far off. Until then the PPU's position only advances, so the NMI line stays high and no new
edge can arrive. This is what `Guard` asks for, given that the handler was entered soon after vblank started.
-/
set_option maxRecDepth 20000
namespace Smb.Routine.PpuCalm
open Smb NES

/-- Vblank has started, the NMI line is high with nothing pending, and the next event is at least `k` dots off. -/
structure Calm (k : Nat) (s : NES) : Prop where
  vbl : s.vbl = true
  line : s.nmiLine = true
  pending : s.nmiPending = false
  next : s.nextEv = 7162
  near : s.fpos.toNat + k < 7162
  on : s.ctrl &&& 0x80 ≠ 0
  dead : s.dead = 0
  dma : s.dmaPending = false

/-- `r` is `s` as far as `Calm` looks, `d` dots later. -/
structure Same (s r : NES) (d : UInt32) : Prop where
  vbl : r.vbl = s.vbl
  line : r.nmiLine = s.nmiLine
  pending : r.nmiPending = s.nmiPending
  next : r.nextEv = s.nextEv
  on : r.ctrl = s.ctrl
  dead : r.dead = s.dead
  dma : r.dmaPending = s.dmaPending
  fpos : r.fpos = s.fpos + d

theorem adv_eq {s : NES} {d : UInt32} (h : (s.fpos + d) < s.nextEv) :
    advancePpu s d = { s with fpos := s.fpos + d } := by
  have : ¬ (s.fpos + d ≥ s.nextEv) := by
    intro h'; exact absurd h (UInt32.not_lt.mpr h')
  simp only [advancePpu, this, if_false]

theorem near_lt {s : NES} {k : Nat} {d : UInt32} (hn : s.nextEv = 7162) (h : s.fpos.toNat + k < 7162) (hd : d.toNat ≤ k) :
    s.fpos + d < s.nextEv := by
  rw [hn, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]
  have : (7162 : UInt32).toNat = 7162 := rfl
  rw [this]
  have h2 : (s.fpos.toNat + d.toNat) % 2 ^ 32 = s.fpos.toNat + d.toNat := Nat.mod_eq_of_lt (by omega)
  rw [h2]
  omega

theorem same_begin {s : NES} (h : s.fpos + 1 < s.nextEv) : Same s (beginCycle s) 1 := by
  unfold beginCycle
  dsimp only
  split
  · rw [adv_eq (by simpa using h)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [adv_eq (by simpa using h)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_end {x : NES} (hv : x.vbl = true) (hl : x.nmiLine = true) (hc : x.ctrl &&& 0x80 ≠ 0)
    (h1 : x.fpos + 1 < x.nextEv) (h2 : x.fpos + 1 + 1 < x.nextEv) :
    Same x (endCycle x) 2 ∧ (endCycle x).nmiPolled = x.nmiPending := by
  have hc' : (x.ctrl &&& 0x80 != 0) = true := by simpa using hc
  unfold endCycle
  dsimp only
  rw [adv_eq h1]
  rw [adv_eq (s := { x with fpos := x.fpos + 1, nmiPolled := x.nmiPending, nmiPending := _, nmiLine := _ }) (by simpa using h2)]
  refine ⟨⟨by simp [hv], by simp [hl, hv, hc'], by simp [hl, hv, hc'], by simp, by simp, by simp, by simp, ?_⟩, by simp⟩
  show x.fpos + 1 + 1 = x.fpos + 2
  rw [UInt32.add_assoc]
  rfl

theorem Same.trans {a b c : NES} {d e : UInt32} (h1 : Same a b d) (h2 : Same b c e) : Same a c (d + e) :=
  ⟨h2.vbl.trans h1.vbl, h2.line.trans h1.line, h2.pending.trans h1.pending, h2.next.trans h1.next, h2.on.trans h1.on, h2.dead.trans h1.dead,
   h2.dma.trans h1.dma, by rw [h2.fpos, h1.fpos, UInt32.add_assoc]⟩

/-- A cycle from a calm state, given what the bus did in the middle. -/
theorem calm_cycle {k : Nat} {s y : NES} (h : Calm (k + 3) s) (hy : Same s y 1) :
    Same s (endCycle y) 3 ∧ (endCycle y).nmiPolled = false := by
  have hn := h.near
  have hN : y.nextEv = 7162 := hy.next.trans h.next
  have hf : y.fpos.toNat = s.fpos.toNat + 1 := by
    rw [hy.fpos, UInt32.toNat_add]
    have : (1 : UInt32).toNat = 1 := rfl
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hn2 : y.fpos.toNat + 2 < 7162 := by omega
  have h1 : y.fpos + 1 < y.nextEv := near_lt hN hn2 (by simp)
  have h2 : y.fpos + 1 + 1 < y.nextEv := by
    rw [UInt32.add_assoc]
    exact near_lt hN hn2 (by simp)
  obtain ⟨he, hp⟩ := same_end (by rw [hy.vbl]; exact h.vbl) (by rw [hy.line]; exact h.line) (by rw [hy.on]; exact h.on) h1 h2
  refine ⟨hy.trans he, ?_⟩
  rw [hp, hy.pending]; exact h.pending

theorem Calm.weak {k j : Nat} {s : NES} (h : Calm k s) (hj : j ≤ k) : Calm j s :=
  ⟨h.vbl, h.line, h.pending, h.next, by have := h.near; omega, h.on, h.dead, h.dma⟩

/-- A state `Same` as a calm one, three dots on, is calm. -/
theorem Calm.of_same {k : Nat} {s r : NES} (h : Calm (k + 3) s) (hr : Same s r 3) : Calm k r := by
  refine ⟨by rw [hr.vbl]; exact h.vbl, by rw [hr.line]; exact h.line, by rw [hr.pending]; exact h.pending, by rw [hr.next]; exact h.next, ?_,
    by rw [hr.on]; exact h.on, by rw [hr.dead]; exact h.dead, by rw [hr.dma]; exact h.dma⟩
  rw [hr.fpos, UInt32.toNat_add]
  have hn := h.near
  have : (3 : UInt32).toNat = 3 := rfl
  rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

theorem fpos_steps {s : NES} {k : Nat} (h : Calm (k + 3) s) :
    s.fpos + 1 < s.nextEv ∧ s.fpos + 2 < s.nextEv ∧ s.fpos + 3 < s.nextEv :=
  ⟨near_lt h.next h.near (by simp), near_lt h.next h.near (by simp), near_lt h.next h.near (by simp)⟩

/-- A read of RAM or ROM in a calm state. -/
theorem calm_read {k : Nat} {s : NES} (h : Calm (k + 3) s) (a : UInt16) (ha : a < 0x2000 ∨ 0x8000 ≤ a) :
    Calm k (readCycle s a).2 ∧ (readCycle s a).2.nmiPolled = false := by
  obtain ⟨h1, h2, h3⟩ := fpos_steps h
  have hb := same_begin h1
  have hmid : (readMid (beginCycle s) a).2 = beginCycle s := by
    rcases ha with ha | ha
    · simp [readMid, ha]
    · obtain ⟨g1, g2, g3, g4⟩ := lt_of_ge_8000 ha
      simp [readMid, g1, g2, g3, g4, ha]
  rw [readCycle_eq]
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
  rw [hfin, hmid]
  have hy : Same s { beginCycle s with bus := (readMid (beginCycle s) a).1, padRead := if a == 0x4016 then 1 else if a == 0x4017 then 2 else 0 } 1 :=
    ⟨hb.vbl, hb.line, hb.pending, hb.next, hb.on, hb.dead, hb.dma, hb.fpos⟩
  obtain ⟨hs, hp⟩ := calm_cycle h hy
  exact ⟨h.of_same hs, hp⟩

/-- A write to RAM in a calm state. -/
theorem calm_write {k : Nat} {s : NES} (h : Calm (k + 3) s) (a : UInt16) (b : UInt8) (ha : a < 0x2000) :
    Calm k (wrS s a b) ∧ (wrS s a b).nmiPolled = false := by
  obtain ⟨h1, h2, h3⟩ := fpos_steps h
  have hb := same_begin h1
  have hm : wrMid { beginCycle s with bus := b, padRead := 0 } a b = setRam { beginCycle s with bus := b, padRead := 0 } (a &&& 0x7FF).toNat b := by
    simp [wrMid, ha]
  rw [wrS_eq, hm]
  have hy : Same s (setRam { beginCycle s with bus := b, padRead := 0 } (a &&& 0x7FF).toNat b) 1 :=
    ⟨hb.vbl, hb.line, hb.pending, hb.next, hb.on, hb.dead, hb.dma, hb.fpos⟩
  obtain ⟨hs, hp⟩ := calm_cycle h hy
  exact ⟨h.of_same hs, hp⟩

theorem reg0 (Y : NES) (b : UInt8) (hd : Y.dead = 0) :
    (ppuRegWrite Y 0x2000 b).ctrl = b ∧ (ppuRegWrite Y 0x2000 b).nmiPending = Y.nmiPending ∧ (ppuRegWrite Y 0x2000 b).vbl = Y.vbl ∧
    (ppuRegWrite Y 0x2000 b).nextEv = Y.nextEv ∧ (ppuRegWrite Y 0x2000 b).fpos = Y.fpos ∧ (ppuRegWrite Y 0x2000 b).nmiLine = Y.nmiLine := by
  have h7 : ((0x2000 : UInt16) &&& 7 == 0) = true := by decide
  have hd' : (Y.dead != 0) = false := by simp [hd]
  unfold ppuRegWrite
  simp only [hd', Bool.false_and, Bool.false_eq_true, if_false, h7, if_true]
  simp

/-- `sta $2000` with bit 7 clear in a calm state, the PPU past its power-on state: NMI generation goes off with nothing pending. -/
theorem calm_sta2000 {k : Nat} {s : NES} (h : Calm (k + 3) s) (b : UInt8) :
    (wrS s 0x2000 b).ctrl = b ∧ (wrS s 0x2000 b).nmiPending = false ∧ (wrS s 0x2000 b).nmiPolled = false := by
  obtain ⟨h1, h2, h3⟩ := fpos_steps h
  have hb := same_begin h1
  obtain ⟨Y, hY⟩ : ∃ Y, Y = { beginCycle s with bus := b, padRead := 0 } := ⟨_, rfl⟩
  have hYs : Same s Y 1 := by
    rw [hY]; exact ⟨hb.vbl, hb.line, hb.pending, hb.next, hb.on, hb.dead, hb.dma, hb.fpos⟩
  have hm : wrMid Y 0x2000 b = ppuRegWrite Y 0x2000 b := by simp [wrMid]
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := reg0 Y b (hYs.dead.trans h.dead)
  rw [wrS_eq, ← hY, hm]
  generalize ppuRegWrite Y 0x2000 b = X at r1 r2 r3 r4 r5 r6
  have hn := h.near
  have hpen : X.nmiPending = false := r2.trans (hYs.pending.trans h.pending)
  have hN : X.nextEv = 7162 := r4.trans (hYs.next.trans h.next)
  have hf : X.fpos.toNat = s.fpos.toNat + 1 := by
    rw [r5, hYs.fpos, UInt32.toNat_add]
    have : (1 : UInt32).toNat = 1 := rfl
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hn2 : X.fpos.toNat + 2 < 7162 := by omega
  have g1 : X.fpos + 1 < X.nextEv := near_lt hN hn2 (by simp)
  have g2 : X.fpos + 1 + 1 < X.nextEv := by
    rw [UInt32.add_assoc]
    exact near_lt hN hn2 (by simp)
  have hl : X.nmiLine = true := r6.trans (hYs.line.trans h.line)
  unfold endCycle
  dsimp only
  rw [adv_eq g1]
  rw [adv_eq (s := { X with fpos := X.fpos + 1, nmiPolled := X.nmiPending, nmiPending := _, nmiLine := _ }) (by simpa using g2)]
  simp [r1, hpen, hl]

theorem calm_regs {k : Nat} {s : NES} (h : Calm k s) (f : Regs → Regs) : Calm k (CPU.modRegs f |>.run s).2 :=
  ⟨h.vbl, h.line, h.pending, h.next, h.near, h.on, h.dead, h.dma⟩

theorem calm_rd {k : Nat} {s : NES} (h : Calm (k + 3) s) (a : UInt16) (ha : a < 0x2000 ∨ 0x8000 ≤ a) :
    Calm k (rdS s a).2 ∧ (rdS s a).2.nmiPolled = false := by
  simp only [rdS, h.dma, Bool.false_eq_true, if_false]
  exact calm_read h a ha

/-- A fetch in a calm state. -/
theorem calm_fetch {k : Nat} {s : NES} (h : Calm (k + 3) s) (hpc : 0x8000 ≤ s.pc) :
    Calm k (CPU.fetch.run s).2 ∧ (CPU.fetch.run s).2.prg = s.prg ∧ (CPU.fetch.run s).2.pc = s.pc + 1 ∧
    (CPU.fetch.run s).1 = s.prg.get! (s.pc &&& 0x7FFF).toNat ∧ (CPU.fetch.run s).2.nmiPolled = false := by
  have hd : ({ s with pc := s.pc + 1 } : NES).dmaPending = false := h.dma
  have e : CPU.fetch.run s = readCycle { s with pc := s.pc + 1 } s.pc := by
    show rdS { s with pc := s.pc + 1 } s.pc = _
    simp only [rdS, h.dma, Bool.false_eq_true, if_false]
  have hs : Calm (k + 3) { s with pc := s.pc + 1 } := ⟨h.vbl, h.line, h.pending, h.next, h.near, h.on, h.dead, h.dma⟩
  rw [e]
  have hv := BusStable.readCycle_view { s with pc := s.pc + 1 } s.pc
  simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
  exact ⟨(calm_read hs _ (Or.inr hpc)).1, hv.2, hv.1.1, readCycle_rom' _ _ hpc, (calm_read hs _ (Or.inr hpc)).2⟩

theorem fetch16_eq (s : NES) : CPU.fetch16.run s =
    (Abs.base (CPU.fetch.run s).1 (CPU.fetch.run (CPU.fetch.run s).2).1, (CPU.fetch.run (CPU.fetch.run s).2).2) := rfl

theorem ad_eq (u : NES) : ((CPU.exec (σ := NES) 0xAD).run u).2 =
    ((CPU.setA (rdS (CPU.fetch16.run u).2 (CPU.fetch16.run u).1).1).run (rdS (CPU.fetch16.run u).2 (CPU.fetch16.run u).1).2).2 := rfl
theorem and_eq (u : NES) : ((CPU.exec (σ := NES) 0x29).run u).2 =
    ((CPU.setA ((Bus.regs (CPU.fetch.run u).2).a &&& (CPU.fetch.run u).1)).run (CPU.fetch.run u).2).2 := rfl

theorem calm_setA {k : Nat} {s : NES} (h : Calm k s) (v : UInt8) : Calm k ((CPU.setA v).run s).2 :=
  ⟨h.vbl, h.line, h.pending, h.next, h.near, h.on, h.dead, h.dma⟩

theorem pc1_ok' (pc : UInt16) (h8 : 0x8000 ≤ pc) (h9 : pc ≤ 0xFFF0) : 0x8000 ≤ pc + 1 := by bv_decide (config := { enums := false })

/-- A two-byte operand fetch. -/
theorem calm_fetch16 {k : Nat} {s : NES} (h : Calm (k + 6) s) (hpc : 0x8000 ≤ s.pc) (hpc2 : s.pc ≤ 0xFFF0) :
    Calm k (CPU.fetch16.run s).2 ∧ (CPU.fetch16.run s).2.prg = s.prg ∧ (CPU.fetch16.run s).2.pc = s.pc + 1 + 1 ∧
    (CPU.fetch16.run s).1 = Abs.base (s.prg.get! (s.pc &&& 0x7FFF).toNat) (s.prg.get! (s.pc + 1 &&& 0x7FFF).toNat) := by
  obtain ⟨c1, p1, q1, v1, -⟩ := calm_fetch (k := k + 3) h hpc
  have hpc' : 0x8000 ≤ (CPU.fetch.run s).2.pc := by rw [q1]; exact pc1_ok' s.pc hpc hpc2
  obtain ⟨c2, p2, q2, v2, -⟩ := calm_fetch c1 hpc'
  rw [fetch16_eq]
  refine ⟨c2, p2.trans p1, by simp only [q2, q1], ?_⟩
  simp only [v1, v2, q1, p1]

theorem b0 : Smb.prg.get! ((0x8082 : UInt16) &&& 0x7FFF).toNat = 0xAD ∧ Smb.prg.get! ((0x8083 : UInt16) &&& 0x7FFF).toNat = 0x78 ∧ Smb.prg.get! ((0x8084 : UInt16) &&& 0x7FFF).toNat = 0x07 := by native_decide
theorem b1 : Smb.prg.get! ((0x8085 : UInt16) &&& 0x7FFF).toNat = 0x29 := by native_decide
theorem b2 : Smb.prg.get! ((0x8087 : UInt16) &&& 0x7FFF).toNat = 0x8D ∧ Smb.prg.get! ((0x8088 : UInt16) &&& 0x7FFF).toNat = 0x78 ∧ Smb.prg.get! ((0x8089 : UInt16) &&& 0x7FFF).toNat = 0x07 := by native_decide
theorem b3 : Smb.prg.get! ((0x808A : UInt16) &&& 0x7FFF).toNat = 0x29 := by native_decide
theorem b4 : Smb.prg.get! ((0x808C : UInt16) &&& 0x7FFF).toNat = 0x8D ∧ Smb.prg.get! ((0x808D : UInt16) &&& 0x7FFF).toNat = 0x00 ∧ Smb.prg.get! ((0x808E : UInt16) &&& 0x7FFF).toNat = 0x20 := by native_decide

/-- A calm state in the handler's first instructions, with the budget each one still needs. -/
def PreCalm (s : NES) : Prop :=
  s.prg = Smb.prg ∧ ((s.pc = 0x8082 ∧ Calm 48 s) ∨ (s.pc = 0x8085 ∧ Calm 36 s) ∨ (s.pc = 0x8087 ∧ Calm 30 s) ∨ (s.pc = 0x808A ∧ Calm 18 s) ∨ (s.pc = 0x808C ∧ Calm 12 s))

theorem rd_view (x : NES) (a : UInt16) : (rdS x a).2.prg = x.prg ∧ (rdS x a).2.pc = x.pc := by
  have hv := BusStable.rdS_view x a
  simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
  exact ⟨hv.2, hv.1.1⟩

theorem wr_view (x : NES) (a : UInt16) (b : UInt8) : (wrS x a b).prg = x.prg ∧ (wrS x a b).pc = x.pc := by
  have hv := BusStable.wrS_view x a b
  simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
  exact ⟨hv.2, hv.1.1⟩

theorem stage0 {s : NES} (h : Calm 48 s) (hp : s.prg = Smb.prg) (hpc : s.pc = 0x8082) :
    Calm 36 (Abs.preChecks s) ∧ (Abs.preChecks s).nmiPolled = false ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = 0x8085 := by
  obtain ⟨c1, p1, q1, v1, -⟩ := calm_fetch (k := 45) h (by rw [hpc]; decide)
  rw [hp, hpc, b0.1] at v1
  rw [hpc] at q1
  obtain ⟨c2, p2, q2, v2⟩ := calm_fetch16 (k := 39) c1 (by rw [q1]; decide) (by rw [q1]; decide)
  rw [p1, hp, q1] at v2
  rw [Abs.preChecks, v1, ad_eq, v2]
  rw [show ((0x8082 : UInt16) + 1 &&& 0x7FFF) = ((0x8083 : UInt16) &&& 0x7FFF) from by decide, b0.2.1,
      show ((0x8082 : UInt16) + 1 + 1 &&& 0x7FFF) = ((0x8084 : UInt16) &&& 0x7FFF) from by decide, b0.2.2]
  have hA : Abs.base 0x78 0x07 < 0x2000 := by decide
  obtain ⟨c3, pol⟩ := calm_rd (k := 36) c2 _ (Or.inl hA)
  have hrv := rd_view (CPU.fetch16.run (CPU.fetch.run s).2).2 (Abs.base 0x78 0x07)
  generalize rdS (CPU.fetch16.run (CPU.fetch.run s).2).2 (Abs.base 0x78 0x07) = R at *
  refine ⟨calm_setA c3 _, pol, ?_, ?_⟩
  · show R.2.prg = _
    rw [hrv.1, p2, p1, hp]
  · show R.2.pc = _
    rw [hrv.2, q2, q1]; decide

theorem pc1_ok (pc : UInt16) (h8 : 0x8000 ≤ pc) (h9 : pc ≤ 0xFFF0) : 0x8000 ≤ pc + 1 := by bv_decide (config := { enums := false })

theorem setA_fields (x : NES) (v : UInt8) : ((CPU.setA v).run x).2.nmiPolled = x.nmiPolled ∧ ((CPU.setA v).run x).2.prg = x.prg ∧ ((CPU.setA v).run x).2.pc = x.pc :=
  ⟨rfl, rfl, rfl⟩

theorem stage1 {s : NES} (k : Nat) (h : Calm (k + 6) s) (hp : s.prg = Smb.prg) (pc : UInt16) (hpc : s.pc = pc) (h8 : 0x8000 ≤ pc) (h9 : pc ≤ 0xFFF0)
    (hb : Smb.prg.get! (pc &&& 0x7FFF).toNat = 0x29) :
    Calm k (Abs.preChecks s) ∧ (Abs.preChecks s).nmiPolled = false ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = pc + 1 + 1 := by
  obtain ⟨c1, p1, q1, v1, -⟩ := calm_fetch (k := k + 3) h (by rw [hpc]; exact h8)
  rw [hp, hpc, hb] at v1
  rw [hpc] at q1
  obtain ⟨c2, p2, q2, -, pol⟩ := calm_fetch (k := k) c1 (by rw [q1]; exact pc1_ok pc h8 h9)
  rw [Abs.preChecks, v1, and_eq]
  obtain ⟨f1, f2, f3⟩ := setA_fields (CPU.fetch.run (CPU.fetch.run s).2).2 ((Bus.regs (CPU.fetch.run (CPU.fetch.run s).2).2).a &&& (CPU.fetch.run (CPU.fetch.run s).2).1)
  refine ⟨calm_setA c2 _, f1.trans pol, f2.trans (p2.trans (p1.trans hp)), f3.trans ?_⟩
  rw [q2, q1]

theorem stage2 {s : NES} (h : Calm 30 s) (hp : s.prg = Smb.prg) (hpc : s.pc = 0x8087) :
    Calm 18 (Abs.preChecks s) ∧ (Abs.preChecks s).nmiPolled = false ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = 0x808A := by
  obtain ⟨c1, p1, q1, v1, -⟩ := calm_fetch (k := 27) h (by rw [hpc]; decide)
  rw [hp, hpc, b2.1] at v1
  rw [hpc] at q1
  obtain ⟨c2, p2, q2, v2⟩ := calm_fetch16 (k := 21) c1 (by rw [q1]; decide) (by rw [q1]; decide)
  rw [p1, hp, q1] at v2
  rw [Abs.preChecks, v1, Abs.exec8d_eq, v2]
  rw [show ((0x8087 : UInt16) + 1 &&& 0x7FFF) = ((0x8088 : UInt16) &&& 0x7FFF) from by decide, b2.2.1,
      show ((0x8087 : UInt16) + 1 + 1 &&& 0x7FFF) = ((0x8089 : UInt16) &&& 0x7FFF) from by decide, b2.2.2]
  have hA : Abs.base 0x78 0x07 < 0x2000 := by decide
  generalize hy : (Bus.regs (CPU.fetch16.run (CPU.fetch.run s).2).2).a = v
  obtain ⟨c3, pol⟩ := calm_write (k := 18) c2 _ v hA
  have hw := wr_view (CPU.fetch16.run (CPU.fetch.run s).2).2 (Abs.base 0x78 0x07) v
  refine ⟨c3, pol, ?_, ?_⟩
  · rw [hw.1, p2, p1, hp]
  · rw [hw.2, q2, q1]; decide

theorem fetch_a (s : NES) : (CPU.fetch.run s).2.a = s.a := by
  have hv := BusStable.rdS_view { s with pc := s.pc + 1 } s.pc
  simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
  exact hv.1.2.1

theorem regs_a (x : NES) : (Bus.regs x).a = x.a := rfl

theorem stage4 {s : NES} (h : Calm 12 s) (hp : s.prg = Smb.prg) (hpc : s.pc = 0x808C) :
    (Abs.preChecks s).nmiPolled = false ∧ (Abs.preChecks s).nmiPending = false ∧ (Abs.preChecks s).ctrl = s.a ∧ (Abs.preChecks s).pc = 0x808F := by
  obtain ⟨c1, p1, q1, v1, -⟩ := calm_fetch (k := 9) h (by rw [hpc]; decide)
  rw [hp, hpc, b4.1] at v1
  rw [hpc] at q1
  obtain ⟨c2, p2, q2, v2⟩ := calm_fetch16 (k := 3) c1 (by rw [q1]; decide) (by rw [q1]; decide)
  rw [p1, hp, q1] at v2
  have hA : Abs.base (Smb.prg.get! (0x808C + 1 &&& 0x7FFF : UInt16).toNat) (Smb.prg.get! (0x808C + 1 + 1 &&& 0x7FFF : UInt16).toNat) = 0x2000 := by
    rw [show ((0x808C : UInt16) + 1 &&& 0x7FFF) = ((0x808D : UInt16) &&& 0x7FFF) from by decide, b4.2.1,
      show ((0x808C : UInt16) + 1 + 1 &&& 0x7FFF) = ((0x808E : UInt16) &&& 0x7FFF) from by decide, b4.2.2]
    decide
  rw [hA] at v2
  have ha : (Bus.regs (CPU.fetch16.run (CPU.fetch.run s).2).2).a = s.a := by
    have e := congrArg Prod.snd (fetch16_eq (CPU.fetch.run s).2)
    have e2 : (CPU.fetch16.run (CPU.fetch.run s).2).2 = (CPU.fetch.run (CPU.fetch.run (CPU.fetch.run s).2).2).2 := e
    rw [regs_a, e2, fetch_a, fetch_a, fetch_a]
  rw [Abs.preChecks, v1, Abs.exec8d_eq, v2, ha]
  obtain ⟨r1, r2, r3⟩ := calm_sta2000 (k := 0) c2 s.a
  refine ⟨r3, r2, r1, ?_⟩
  rw [(wr_view _ _ _).2, q2, q1]
  decide

/-- The handler's first instructions, from a calm state: `Guard` holds. -/
theorem guard_of_preCalm {s : NES} (h : PreCalm s) : Abs.Guard s := by
  intro _
  obtain ⟨hp, h0 | h1 | h2 | h3 | h4⟩ := h
  · obtain ⟨hpc, hc⟩ := h0
    obtain ⟨c, pol, -, -⟩ := stage0 hc hp hpc
    exact ⟨pol, c.pending, fun e => by rw [hpc] at e; cases e⟩
  · obtain ⟨hpc, hc⟩ := h1
    obtain ⟨c, pol, -, -⟩ := stage1 30 hc hp _ hpc (by decide) (by decide) b1
    exact ⟨pol, c.pending, fun e => by rw [hpc] at e; cases e⟩
  · obtain ⟨hpc, hc⟩ := h2
    obtain ⟨c, pol, -, -⟩ := stage2 hc hp hpc
    exact ⟨pol, c.pending, fun e => by rw [hpc] at e; cases e⟩
  · obtain ⟨hpc, hc⟩ := h3
    obtain ⟨c, pol, -, -⟩ := stage1 12 hc hp _ hpc (by decide) (by decide) b3
    exact ⟨pol, c.pending, fun e => by rw [hpc] at e; cases e⟩
  · obtain ⟨hpc, hc⟩ := h4
    obtain ⟨a, b, c, -⟩ := stage4 hc hp hpc
    exact ⟨a, b, fun _ => c⟩


end Smb.Routine.PpuCalm
