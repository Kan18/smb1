import Smb.RefineRun
import Smb.Routine.NesBusRam
import Smb.Routine.NesBusStable
import Smb.Abs.CheckIO
import Smb.Routine.AbsCheck

/-!
# Hardware instructions on the full NES

`check` and `inv_step` concern the plain machine, which has no PPU, APU or controllers. Here `NInv` lifts the invariant to the
full NES: a state's CPU view is some plain state of the table. `ninv_step` proves that a table `checkN` accepted keeps it, over
each instruction, for every value a hardware register returns. The proof needs only these facts, for any address, with NMI
generation off: a read cycle changes no CPU register or RAM (`core_readCycle`); OAM DMA, whenever it runs, changes neither
(`core_oamDma`); and a write outside RAM changes neither, nor turns NMI generation on, unless it is a store to `$2000` with
bit 7 set (`core_wrS_io`), which the table treats as an exit.

Since nothing here depends on the PPU's position, the invariant holds at each instruction boundary for any timing. That covers
lag: a frame's work running long changes when it ends and not which states it passes through.
-/
set_option maxRecDepth 20000
namespace Smb.NES

theorem core_ppuRegRead (s : NES) (a : UInt16) : core (ppuRegRead s a).2 = core s := by
  unfold ppuRegRead
  dsimp only
  repeat' first | rfl | split

theorem core_ppuMemWrite (s : NES) (a : UInt16) (b : UInt8) : core (ppuMemWrite s a b) = core s := by
  unfold ppuMemWrite
  dsimp only
  repeat' first | rfl | split

private theorem cf {s t : NES} (h : core s = core t) :
    s.pc = t.pc ∧ s.a = t.a ∧ s.x = t.x ∧ s.y = t.y ∧ s.s = t.s ∧ s.p = t.p ∧ s.ram = t.ram ∧ s.prg = t.prg ∧
    s.ctrl = t.ctrl ∧ s.dmaPending = t.dmaPending ∧ s.nmiPending = t.nmiPending ∧ s.nmiPolled = t.nmiPolled ∧
    s.cyc = t.cyc := by
  simpa only [core, Core.mk.injEq] using h

theorem core_ppuRegWrite (s : NES) (a : UInt16) (b : UInt8) :
    core (ppuRegWrite s a b) = core { s with ctrl := (ppuRegWrite s a b).ctrl } ∧
    ((ppuRegWrite s a b).ctrl = s.ctrl ∨ (a &&& 7 = 0 ∧ (ppuRegWrite s a b).ctrl = b)) := by
  have hs := fun s => cf (core_sched s)
  have hm := fun s a b => cf (core_ppuMemWrite s a b)
  have hv := BusStable.ppuRegWrite_view s a b
  simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h8⟩ := hv
  have h7 := BusRam.ppuRegWrite_ram s a b
  refine ⟨?_, ?_⟩
  · simp only [core, Core.mk.injEq, h1, h2, h3, h4, h5, h6, h7, h8, true_and, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold ppuRegWrite <;>
      simp only [apply_ite NES.dmaPending, apply_ite NES.nmiPending, apply_ite NES.nmiPolled, apply_ite NES.cyc, hs, hm, setOam, ite_self]
  · unfold ppuRegWrite
    simp only [apply_ite NES.ctrl, hs, hm, setOam, ite_self]
    by_cases h0 : (a &&& 7) = 0
    · simp only [h0]
      split
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp, by simp⟩
    · left
      have : (a &&& 7 == 0) = false := by simpa using h0
      simp [this]


/-- The middle of `readCycle`: the value, and the state's device side. -/
def readMid (s : NES) (a : UInt16) : UInt8 × NES :=
    if a < 0x2000 then (s.ram.get! (a &&& 0x7FF).toNat, s)
    else if a < 0x4000 then ppuRegRead s a
    else if a == 0x4016 || a == 0x4017 then
      let port : UInt8 := if a == 0x4016 then 1 else 2
      let pad := if port == 1 then s.pad0 else s.pad1
      let sh := if port == 1 then s.sh0 else s.sh1
      let bit := if s.strobe then pad &&& 1 else if s.padRead == port then s.padBit else sh &&& 1
      let shift := !s.strobe && s.padRead != port
      (s.bus &&& 0xE0 ||| bit, { s with
        padBit := bit, sh0 := if shift && port == 1 then (sh >>> 1) ||| 0x80 else s.sh0,
        sh1 := if shift && port == 2 then (sh >>> 1) ||| 0x80 else s.sh1 })
    else if a ≥ 0x8000 then (s.prgAt a, s)
    else (s.bus, { s with unmodelled := s.unmodelled || a == 0x4015 })

theorem core_readMid (s : NES) (a : UInt16) : core (readMid s a).2 = core s := by
  unfold readMid
  repeat' split
  · rfl
  · exact core_ppuRegRead s a
  all_goals rfl

/-- The end of `readCycle`. -/
def readFin (r : UInt8) (s : NES) (a : UInt16) : UInt8 × NES :=
  if a ≥ 0x2000 && a < 0x4000 && a &&& 7 == 2 then
    let r := (r &&& 0x9F) ||| (if s.spr0 then 0x40 else 0) ||| (if s.ovf then 0x20 else 0)
    (r, { s with bus := r, iolatch := r })
  else (r, s)

theorem core_readFin (r : UInt8) (s : NES) (a : UInt16) : core (readFin r s a).2 = core s := by
  unfold readFin
  split <;> rfl

theorem readCycle_eq (s : NES) (a : UInt16) :
    readCycle s a = readFin (readMid (beginCycle s) a).1
      (endCycle { (readMid (beginCycle s) a).2 with bus := (readMid (beginCycle s) a).1, padRead := if a == 0x4016 then 1 else if a == 0x4017 then 2 else 0 }) a := rfl

/-- With NMI generation off, a read cycle at any address only ticks the core. -/
theorem core_readCycle (s : NES) (a : UInt16) (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    core (readCycle s a).2 = core { s with cyc := s.cyc + 1, nmiPolled := false } := by
  have hb := cf (core_beginCycle s)
  have hm := cf (core_readMid (beginCycle s) a)
  rw [readCycle_eq, core_readFin, core_endCycle _ (by simp [hm, hb, hp]) (by simp [hm, hb, hc])]
  simp [core, hm, hb]

/-- A cycle's end, with NMI generation possibly on: only the NMI latches change. -/
theorem core_endCycle_any (s : NES) :
    core (endCycle s) = core { s with nmiPolled := s.nmiPending, nmiPending := (endCycle s).nmiPending } := by
  have h1 := cf (core_advancePpu s 1)
  have h2 := fun x => cf (core_advancePpu x 1)
  unfold endCycle
  dsimp only
  simp only [core, Core.mk.injEq]
  simp [h2, h1]

/-- A read cycle at any address, with NMI generation possibly on: it ticks the core and only the NMI latches change. -/
theorem core_readCycle_any (s : NES) (a : UInt16) :
    ∃ pol pen, core (readCycle s a).2 = core { s with cyc := s.cyc + 1, nmiPolled := pol, nmiPending := pen } := by
  have hb := cf (core_beginCycle s)
  have hm := cf (core_readMid (beginCycle s) a)
  obtain ⟨X, hX⟩ : ∃ X, X = { (readMid (beginCycle s) a).2 with bus := (readMid (beginCycle s) a).1, padRead := if a == 0x4016 then 1 else if a == 0x4017 then 2 else 0 } := ⟨_, rfl⟩
  have hX' := cf (show core X = core (readMid (beginCycle s) a).2 by rw [hX]; rfl)
  rw [readCycle_eq, core_readFin, ← hX, core_endCycle_any]
  refine ⟨X.nmiPending, (endCycle X).nmiPending, ?_⟩
  simp only [core, Core.mk.injEq]
  simp [hX', hm, hb]

theorem readFin_val (r : UInt8) (s : NES) (a : UInt16) (h : a < 0x2000 ∨ 0x8000 ≤ a) : (readFin r s a).1 = r := by
  have : ¬ ((decide (a ≥ 0x2000) && decide (a < 0x4000) && a &&& 7 == 2) = true) := by
    intro h'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
    obtain ⟨⟨h1, h2⟩, _⟩ := h'
    revert h h1 h2
    bv_decide (config := { enums := false })
  unfold readFin
  rw [if_neg this]

/-- What a read returns outside the hardware. -/
theorem readCycle_ram' (s : NES) (a : UInt16) (ha : a < 0x2000) : (readCycle s a).1 = s.ram.get! (a &&& 0x7FF).toNat := by
  have hb := cf (core_beginCycle s)
  rw [readCycle_eq, readFin_val _ _ _ (Or.inl ha)]
  simp only [readMid, ha, if_true]
  rw [hb.2.2.2.2.2.2.1]

theorem readCycle_rom' (s : NES) (a : UInt16) (ha : 0x8000 ≤ a) : (readCycle s a).1 = s.prg.get! (a &&& 0x7FFF).toNat := by
  have hb := cf (core_beginCycle s)
  rw [readCycle_eq, readFin_val _ _ _ (Or.inr ha)]
  obtain ⟨h1, h2, h3, h4⟩ := lt_of_ge_8000 ha
  have h5 : (a == 0x4016 || a == 0x4017) = false := by simp [h3, h4]
  simp only [readMid, h1, h2, h5, ha, if_false, if_true, Bool.false_eq_true, ge_iff_le]
  simp only [prgAt]
  rw [hb.2.2.2.2.2.2.2.1]

theorem core_oamDma_go (n : Nat) (i : UInt16) (s : NES) (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0)
    (hpol : s.nmiPolled = false) :
    ∃ c, core (oamDma.go n i s) = core { s with cyc := c } := by
  induction n generalizing i s with
  | zero => exact ⟨_, rfl⟩
  | succ n ih =>
    simp only [oamDma.go]
    have h1 := cf (core_readCycle s ((s.dmaPage.toUInt16 <<< 8) ||| i) hp hc)
    generalize readCycle s ((s.dmaPage.toUInt16 <<< 8) ||| i) = x at h1 ⊢
    have h2 := cf (core_beginCycle x.2)
    have h3 := (core_ppuRegWrite (beginCycle x.2) 0x2004 x.1)
    have h3c := h3.2
    have hne : ((0x2004 : UInt16) &&& 7 = 0) = False := by first | (simp; done) | (simp; decide)
    simp only [hne, false_and, or_false] at h3c
    have h4 := cf h3.1
    generalize ppuRegWrite (beginCycle x.2) 0x2004 x.1 = y at h3c h4 ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -, a10, a11, a12, a13⟩ := h4
    have hcy : y.ctrl = s.ctrl := by simp [h3c, h2, h1]
    have hpy : y.nmiPending = false := by simp [a11, h2, h1, hp]
    have h5 := cf (core_endCycle { y with bus := x.1, padRead := 0 } hpy (by simp [hcy, hc]))
    generalize endCycle { y with bus := x.1, padRead := 0 } = z at h5 ⊢
    obtain ⟨c, hc'⟩ := ih (i + 1) z (by simp [h5, hpy]) (by simp [h5, hcy, hc]) (by simp [h5])
    refine ⟨c, hc'.trans ?_⟩
    simp only [core, Core.mk.injEq]
    simp [h5, a1, a2, a3, a4, a5, a6, a7, a8, a10, a11, a12, a13, h2, h1, hcy, hpol]

private def oamDmaAfter (x : NES) : NES :=
  oamDma.go 256 0 (if x.cyc &&& 1 != 0 then (readCycle x x.pc).2 else x)

theorem core_oamDma (s : NES) (a : UInt16) (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    ∃ c, core (oamDma s a) = core { s with dmaPending := false, nmiPolled := false, cyc := c } := by
  have h0 : ∃ s0, s0 = { s with dmaPending := false, unmodelled := s.unmodelled || rendering s } := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ := h0
  have hs := cf (show core s0 = core { s with dmaPending := false } by rw [hs0]; rfl)
  have h1 := cf (core_readCycle s0 a (by simp [hs, hp]) (by simp [hs, hc]))
  have he : oamDma s a = (let s := (readCycle s0 a).2
      let s := if s.cyc &&& 1 != 0 then (readCycle s a).2 else s
      oamDma.go 256 0 s) := by rw [hs0]; rfl
  rw [he]
  generalize (readCycle s0 a).2 = x at h1 ⊢
  have h2 := cf (core_readCycle x a (by simp [h1, hs, hp]) (by simp [h1, hs, hc]))
  dsimp only
  split
  · generalize (readCycle x a).2 = y at h2
    obtain ⟨c, h3⟩ := core_oamDma_go 256 0 y (by simp [h2, h1, hs, hp]) (by simp [h2, h1, hs, hc]) (by simp [h2])
    exact ⟨c, h3.trans (by simp only [core, Core.mk.injEq]; simp [h2, h1, hs])⟩
  · obtain ⟨c, h3⟩ := core_oamDma_go 256 0 x (by simp [h1, hs, hp]) (by simp [h1, hs, hc]) (by simp [h1])
    exact ⟨c, h3.trans (by simp only [core, Core.mk.injEq]; simp [h1, hs])⟩

def wrMid (s : NES) (a : UInt16) (b : UInt8) : NES :=
    if a < 0x2000 then s.setRam (a &&& 0x7FF).toNat b
    else if a < 0x4000 then ppuRegWrite s a b
    else if a == 0x4014 then { s with dmaPending := true, dmaPage := b }
    else if a == 0x4016 then
      let on := b &&& 1 != 0
      { s with strobe := on, polls := s.polls + (if s.strobe && !on then 1 else 0) }
    else if a == 0x4015 && b &&& 0x10 != 0 then { s with unmodelled := true }
    else s

theorem wrS_eq (s : NES) (a : UInt16) (b : UInt8) :
    wrS s a b = endCycle (wrMid { beginCycle s with bus := b, padRead := 0 } a b) := rfl

private theorem core_wrMid (s : NES) (a : UInt16) (b : UInt8) (ha : ¬ a < 0x2000) (hc : s.ctrl &&& 0x80 = 0)
    (hw : 0x4000 ≤ a ∨ a &&& 7 ≠ 0 ∨ b &&& 0x80 = 0) :
    ∃ c d, core (wrMid s a b) = core { s with ctrl := c, dmaPending := d } ∧ c &&& 0x80 = 0 := by
  unfold wrMid
  simp only [ha, if_false]
  by_cases h4 : a < 0x4000
  · simp only [h4, if_true]
    obtain ⟨h1, h2⟩ := core_ppuRegWrite s a b
    refine ⟨_, s.dmaPending, h1, ?_⟩
    rcases h2 with h2 | ⟨h2, h3⟩
    · rw [h2]; exact hc
    · rw [h3]
      rcases hw with h | h | h
      · exact absurd h4 (by intro h'; revert h h'; bv_decide (config := { enums := false }))
      · exact absurd h2 h
      · exact h
  · simp only [h4, if_false]
    repeat' split
    all_goals first
      | exact ⟨s.ctrl, _, rfl, hc⟩

/-- A write outside RAM: RAM and registers are kept; only `ctrl` and the DMA latch can change. -/
theorem core_wrS_io (s : NES) (a : UInt16) (b : UInt8) (ha : ¬ a < 0x2000)
    (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0)
    (hw : 0x4000 ≤ a ∨ a &&& 7 ≠ 0 ∨ b &&& 0x80 = 0) :
    ∃ c d, core (wrS s a b) = core { s with ctrl := c, dmaPending := d, cyc := s.cyc + 1, nmiPolled := false } ∧
      c &&& 0x80 = 0 := by
  have hb := cf (core_beginCycle s)
  obtain ⟨c, d, h1, h2⟩ := core_wrMid { beginCycle s with bus := b, padRead := 0 } a b ha (by simp [hb, hc]) hw
  have h1' := cf h1
  rw [wrS_eq]
  generalize wrMid { beginCycle s with bus := b, padRead := 0 } a b = x at h1'
  refine ⟨c, d, ?_, h2⟩
  rw [core_endCycle _ (by simp [h1', hb, hp]) (by simp [h1', h2])]
  simp only [core, Core.mk.injEq]
  simp [h1', hb]

/-- A RAM write, with NMI generation possibly on. -/
theorem core_wrS_ram_any (s : NES) (a : UInt16) (b : UInt8) (ha : a < 0x2000) :
    ∃ pol pen, core (wrS s a b) = core { s with ram := s.ram.set! (a &&& 0x7FF).toNat b, cyc := s.cyc + 1, nmiPolled := pol, nmiPending := pen } := by
  have hb := cf (core_beginCycle s)
  obtain ⟨X, hX⟩ : ∃ X, X = wrMid { beginCycle s with bus := b, padRead := 0 } a b := ⟨_, rfl⟩
  have hX' : X = setRam { beginCycle s with bus := b, padRead := 0 } (a &&& 0x7FF).toNat b := by
    rw [hX]; simp only [wrMid, ha, if_true]
  have hf := cf (show core X = core { beginCycle s with bus := b, padRead := 0, ram := (beginCycle s).ram.set! (a &&& 0x7FF).toNat b } by rw [hX']; rfl)
  rw [wrS_eq, ← hX, core_endCycle_any]
  refine ⟨X.nmiPending, (endCycle X).nmiPending, ?_⟩
  simp only [core, Core.mk.injEq]
  simp [hf, hb]

/-- `sta $2000`: `ctrl` takes the value; the previous poll's input is what the instruction's last poll sees. -/
theorem core_wrS_2000 (s : NES) (b : UInt8) :
    ∃ c pen, core (wrS s 0x2000 b) = core { s with ctrl := c, cyc := s.cyc + 1, nmiPolled := s.nmiPending, nmiPending := pen } ∧
      (c = s.ctrl ∨ c = b) := by
  have hb := cf (core_beginCycle s)
  have hs := show ({ beginCycle s with bus := b, padRead := 0 }).nmiPending = s.nmiPending by simp [hb]
  obtain ⟨X, hX⟩ : ∃ X, X = wrMid { beginCycle s with bus := b, padRead := 0 } 0x2000 b := ⟨_, rfl⟩
  have hX' : X = ppuRegWrite { beginCycle s with bus := b, padRead := 0 } 0x2000 b := by
    rw [hX]; simp [wrMid]
  have hw := core_ppuRegWrite { beginCycle s with bus := b, padRead := 0 } 0x2000 b
  rw [← hX'] at hw
  have hf := hw.1
  have hc := hw.2
  have hf' := cf hf
  rw [wrS_eq, ← hX, core_endCycle_any]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -, a10, a11, a12, a13⟩ := hf'
  refine ⟨X.ctrl, (endCycle X).nmiPending, ?_, ?_⟩
  · simp only [core, Core.mk.injEq]
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a10, a11, a13, hb]
  · rcases hc with h | ⟨_, h⟩
    · left; rw [h]; simp [hb]
    · right; exact h

end Smb.NES

namespace Smb
open CPU

/-- `Rel` without the cycle count and the DMA latch, which an I/O instruction may set and which do not bear on
what the plain machine's registers and RAM are. -/
structure RelD (s : NES) (t : Plain) : Prop where
  regs : (⟨s.pc, s.a, s.x, s.y, s.s, s.p⟩ : Regs) = t.regs
  ram : ∀ i : UInt16, s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF)
  size : s.ram.size = 0x800
  prg : ∀ a : UInt16, s.prg.get! (a &&& 0x7FFF).toNat = t.prg (a &&& 0x7FFF)
  ctrl : s.ctrl &&& 0x80 = 0
  nmiPending : s.nmiPending = false
  nmiPolled : s.nmiPolled = false

namespace RelD

private theorem cf' {s t : NES} (h : core s = core t) : s.dmaPending = t.dmaPending :=
  congrArg Core.dmaPending h

theorem of_rel {s : NES} {t : Plain} (h : Rel s t) : RelD s t :=
  ⟨h.regs, h.ram, h.size, h.prg, h.ctrl, h.nmiPending, h.nmiPolled⟩

/-- A `RelD` state with no DMA latched is `Rel` to the plain state at its cycle count. -/
theorem rel {s : NES} {t : Plain} (h : RelD s t) (hd : s.dmaPending = false) : Rel s { t with cyc := s.cyc } :=
  { regs := h.regs, ram := h.ram, size := h.size, prg := h.prg, cyc := rfl, ctrl := h.ctrl,
    nmiPending := h.nmiPending, nmiPolled := h.nmiPolled, dma := hd }

/-- A core-level change of only the cycle, poll and latch. -/
theorem of_core {s s' : NES} {t : Plain} (h : RelD s t) {c d y p}
    (hc : core s' = core { s with ctrl := c, dmaPending := d, cyc := y, nmiPolled := p }) (hk : c &&& 0x80 = 0)
    (hp : p = false) : RelD s' t := by
  simp only [core, Core.mk.injEq] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
  exact { regs := by rw [h1, h2, h3, h4, h5, h6]; exact h.regs
          ram := by rw [h7]; exact h.ram
          size := by rw [h7]; exact h.size
          prg := by rw [h8]; exact h.prg
          ctrl := by rw [h9]; exact hk
          nmiPending := by rw [h11]; exact h.nmiPending
          nmiPolled := by rw [h12]; exact hp }

theorem read {s : NES} {t : Plain} (h : RelD s t) (a : UInt16) : RelD (NES.rdS s a).2 t := by
  unfold NES.rdS
  split
  · obtain ⟨c, hc⟩ := NES.core_oamDma s a h.nmiPending h.ctrl
    have h' : RelD (NES.oamDma s a) t := h.of_core (c := s.ctrl) (d := false) (y := c) (p := false) hc h.ctrl rfl
    exact h'.of_core (c := (NES.oamDma s a).ctrl) (d := (NES.oamDma s a).dmaPending) (y := (NES.oamDma s a).cyc + 1) (p := false)
      (NES.core_readCycle _ a h'.nmiPending h'.ctrl) h'.ctrl rfl
  · exact h.of_core (c := s.ctrl) (d := s.dmaPending) (y := s.cyc + 1) (p := false)
      (NES.core_readCycle _ a h.nmiPending h.ctrl) h.ctrl rfl

theorem write {s : NES} {t : Plain} (h : RelD s t) (a : UInt16) (b : UInt8) (ha : ¬ a < 0x2000)
    (hw : 0x4000 ≤ a ∨ a &&& 7 ≠ 0 ∨ b &&& 0x80 = 0) : RelD (NES.wrS s a b) t := by
  obtain ⟨c, d, h1, h2⟩ := NES.core_wrS_io s a b ha h.nmiPending h.ctrl hw
  exact h.of_core h1 h2 rfl

theorem modRegs {s : NES} {t : Plain} (h : RelD s t) (f : Regs → Regs) :
    RelD (CPU.modRegs f |>.run s).2 { t with regs := f t.regs } := by
  have hr := h.regs
  exact { regs := by
            show (⟨_, _, _, _, _, _⟩ : Regs) = f t.regs
            rw [← hr]
            rfl
          ram := h.ram, size := h.size, prg := h.prg, ctrl := h.ctrl, nmiPending := h.nmiPending, nmiPolled := h.nmiPolled }

/-- A fetch reads the ROM and clears any latched DMA. -/
theorem fetch {s : NES} {t : Plain} (h : RelD s t) (h0 : 0x8000 ≤ t.regs.pc) :
    (CPU.fetch.run s).1 = t.prg (t.regs.pc &&& 0x7FFF) ∧ (CPU.fetch.run s).2.dmaPending = false ∧
    RelD (CPU.fetch.run s).2 { t with regs := { t.regs with pc := t.regs.pc + 1 } } := by
  have hpc : s.pc = t.regs.pc := congrArg Regs.pc h.regs
  have h1 := h.modRegs (fun r => { r with pc := s.pc + 1 })
  have hr : (CPU.fetch.run s) = NES.rdS (CPU.modRegs (σ := NES) (fun r => { r with pc := s.pc + 1 }) |>.run s).2 s.pc := rfl
  rw [hr, hpc] at *
  generalize (CPU.modRegs (σ := NES) (fun r => { r with pc := t.regs.pc + 1 }) |>.run s).2 = s' at h1
  have key : ∃ x, NES.rdS s' t.regs.pc = NES.readCycle x t.regs.pc ∧ RelD x { t with regs := { t.regs with pc := t.regs.pc + 1 } } ∧
      x.dmaPending = false := by
    by_cases hd : s'.dmaPending = true
    · obtain ⟨c, hc⟩ := NES.core_oamDma s' t.regs.pc h1.nmiPending h1.ctrl
      refine ⟨NES.oamDma s' t.regs.pc, by simp [NES.rdS, hd], h1.of_core (c := s'.ctrl) (d := false) (y := c) (p := false) hc h1.ctrl rfl, ?_⟩
      have := cf' hc
      simpa using this
    · exact ⟨s', by simp [NES.rdS, hd], h1, by simpa using hd⟩
  obtain ⟨x, he, hx, hxd⟩ := key
  rw [he]
  obtain ⟨hv, hc⟩ := NES.readCycle_rom x t.regs.pc h0 hx.nmiPending hx.ctrl
  refine ⟨?_, ?_, hx.of_core (c := x.ctrl) (d := x.dmaPending) (y := x.cyc + 1) (p := false) hc hx.ctrl rfl⟩
  · rw [hv]; exact hx.prg _
  · have := cf' hc
    simpa [hxd] using this

theorem dummy {s : NES} {t : Plain} (h : RelD s t) (c : Bool) (a : UInt16) : RelD (CPU.dummyRdIf c a |>.run s).2 t := by
  unfold CPU.dummyRdIf
  cases c
  · exact h
  · exact h.read a

theorem congr {s : NES} {t t' : Plain} (h : RelD s t) (hr : t.regs = t'.regs) (hram : t.ram = t'.ram) (hprg : t.prg = t'.prg) :
    RelD s t' :=
  { regs := h.regs.trans hr, ram := by rw [← hram]; exact h.ram, size := h.size, prg := by rw [← hprg]; exact h.prg,
    ctrl := h.ctrl, nmiPending := h.nmiPending, nmiPolled := h.nmiPolled }

end RelD

/-- What `stepTail` does after the instruction. -/
def checks {σ : Type} [Bus σ] : StateM σ Unit := do
  if (← getRegs).p &&& FI == 0 then unsupported
  if (← nmiPolled) then nmi

theorem checks_id {s : NES} {t : Plain} (h : RelD s t) (hi : t.regs.p &&& 4 ≠ 0) : (checks.run s).2 = s := by
  have hp : s.p = t.regs.p := congrArg Regs.p h.regs
  have hn := h.nmiPolled
  have : (s.p &&& FI == 0) = false := by
    rw [hp]; simpa [FI] using hi
  simp [checks, bind, StateT.bind, getRegs, nmiPolled, Bus.nmiPolled, Bus.regs, hn, this, pure, StateT.pure, StateT.run]

theorem stepTail_eq {σ : Type} [Bus σ] (op : UInt8) : CPU.stepTail (σ := σ) op = (do exec op; checks) := rfl

namespace RelD

theorem fetch16 {s : NES} {t : Plain} (h : RelD s t) (h0 : 0x8000 ≤ t.regs.pc) (h2 : t.regs.pc ≤ 0xFFF1) :
    (CPU.fetch16.run s).1 = Abs.base (t.prg (t.regs.pc &&& 0x7FFF)) (t.prg (t.regs.pc + 1 &&& 0x7FFF)) ∧
    RelD (CPU.fetch16.run s).2 { t with regs := { t.regs with pc := t.regs.pc + 2 } } := by
  have hf := h.fetch h0
  have hf2 := hf.2.2.fetch (by dsimp only; revert h0 h2; bv_decide (config := { enums := false }))
  refine ⟨?_, hf2.2.2.congr ?_ rfl rfl⟩
  · show (CPU.fetch.run s).1.toUInt16 ||| ((CPU.fetch.run (CPU.fetch.run s).2).1.toUInt16 <<< 8) = _
    rw [hf.1, hf2.1]; rfl
  · have : t.regs.pc + 1 + 1 = t.regs.pc + 2 := by bv_decide (config := { enums := false })
    simp [this]

theorem setA {s : NES} {t : Plain} (h : RelD s t) (v : UInt8) :
    RelD ((CPU.setA v).run s).2 { t with regs := { t.regs with a := v, p := Abs.nz t.regs.p v } } :=
  (((h.modRegs (fun r => { r with a := v })).modRegs (fun r => { r with p := (r.p &&& ~~~(FN ||| FZ)) ||| (v &&& FN) ||| (if v == 0 then FZ else 0) }))).congr rfl rfl rfl

theorem setX {s : NES} {t : Plain} (h : RelD s t) (v : UInt8) :
    RelD ((CPU.setX v).run s).2 { t with regs := { t.regs with x := v, p := Abs.nz t.regs.p v } } :=
  (((h.modRegs (fun r => { r with x := v })).modRegs (fun r => { r with p := (r.p &&& ~~~(FN ||| FZ)) ||| (v &&& FN) ||| (if v == 0 then FZ else 0) }))).congr rfl rfl rfl

theorem setY {s : NES} {t : Plain} (h : RelD s t) (v : UInt8) :
    RelD ((CPU.setY v).run s).2 { t with regs := { t.regs with y := v, p := Abs.nz t.regs.p v } } :=
  (((h.modRegs (fun r => { r with y := v })).modRegs (fun r => { r with p := (r.p &&& ~~~(FN ||| FZ)) ||| (v &&& FN) ||| (if v == 0 then FZ else 0) }))).congr rfl rfl rfl

end RelD

theorem step_split (s : NES) : (CPU.step.run s).2 = ((CPU.stepTail (CPU.fetch.run s).1).run (CPU.fetch.run s).2).2 := rfl

/-- An addressing mode's run on the NES: two operand bytes, and an address depending only on them and the registers. -/
def AddrOk (A : NES → UInt16 × NES) (ea : UInt8 → UInt8 → Regs → UInt16) : Prop :=
  ∀ s t, RelD s t → 0x8000 ≤ t.regs.pc → t.regs.pc ≤ 0xFFF1 →
    (A s).1 = ea (t.prg (t.regs.pc &&& 0x7FFF)) (t.prg (t.regs.pc + 1 &&& 0x7FFF)) t.regs ∧
    RelD (A s).2 { t with regs := { t.regs with pc := t.regs.pc + 2 } }

theorem addr_abs : AddrOk CPU.fetch16.run (fun b1 b2 _ => Abs.base b1 b2) :=
  fun _ _ h h0 h2 => h.fetch16 h0 h2

theorem addr_absx (w : Bool) : AddrOk (CPU.aAbsX w).run (fun b1 b2 r => Abs.base b1 b2 + r.x.toUInt16) := by
  intro s t h h0 h2
  have hf := h.fetch16 h0 h2
  have hx : (Bus.regs s).x = t.regs.x := congrArg Regs.x h.regs
  have he : (CPU.aAbsX w).run s = (let a := (CPU.fetch16.run s).1 + (Bus.regs s).x.toUInt16
      (a, (CPU.dummyRdIf (w || (a ^^^ (CPU.fetch16.run s).1) &&& 0xFF00 != 0) (((CPU.fetch16.run s).1 &&& 0xFF00) ||| (a &&& 0xFF))).run (CPU.fetch16.run s).2 |>.2)) := rfl
  rw [he, hx]
  dsimp only
  rw [hf.1]
  exact ⟨rfl, by rw [← hf.1]; exact hf.2.dummy _ _⟩

theorem addr_absy (w : Bool) : AddrOk (CPU.aAbsY w).run (fun b1 b2 r => Abs.base b1 b2 + r.y.toUInt16) := by
  intro s t h h0 h2
  have hf := h.fetch16 h0 h2
  have hx : (Bus.regs s).y = t.regs.y := congrArg Regs.y h.regs
  have he : (CPU.aAbsY w).run s = (let a := (CPU.fetch16.run s).1 + (Bus.regs s).y.toUInt16
      (a, (CPU.dummyRdIf (w || (a ^^^ (CPU.fetch16.run s).1) &&& 0xFF00 != 0) (((CPU.fetch16.run s).1 &&& 0xFF00) ||| (a &&& 0xFF))).run (CPU.fetch16.run s).2 |>.2)) := rfl
  rw [he, hx]
  dsimp only
  rw [hf.1]
  exact ⟨rfl, by rw [← hf.1]; exact hf.2.dummy _ _⟩

/-- A load's addressing mode: it consumes `sz` bytes and whatever address it computes is read. -/
def AddrAny (A : NES → UInt16 × NES) (sz : UInt16) : Prop :=
  ∀ s t, RelD s t → 0x8000 ≤ t.regs.pc → t.regs.pc ≤ 0xFFF1 → RelD (A s).2 { t with regs := { t.regs with pc := t.regs.pc + sz } }

theorem any_abs : AddrAny CPU.fetch16.run 2 := fun s t h h0 h2 => (h.fetch16 h0 h2).2
theorem any_absx (w : Bool) : AddrAny (CPU.aAbsX w).run 2 := fun s t h h0 h2 => (addr_absx w s t h h0 h2).2
theorem any_absy (w : Bool) : AddrAny (CPU.aAbsY w).run 2 := fun s t h h0 h2 => (addr_absy w s t h h0 h2).2

theorem any_indy : AddrAny (CPU.aIndY false).run 1 := by
  intro s t h h0 h2
  have hf := h.fetch h0
  have he : (CPU.aIndY false).run s = (let f := CPU.fetch.run s
      let l := NES.rdS f.2 f.1.toUInt16
      let u := NES.rdS l.2 (f.1 + 1).toUInt16
      let b := l.1.toUInt16 ||| (u.1.toUInt16 <<< 8)
      let a := b + (Bus.regs u.2).y.toUInt16
      (a, (CPU.dummyRdIf (false || (a ^^^ b) &&& 0xFF00 != 0) ((b &&& 0xFF00) ||| (a &&& 0xFF))).run u.2 |>.2)) := rfl
  rw [he]
  exact ((hf.2.2.read _).read _).dummy _ _

theorem step_load {s : NES} {t : Plain} {op : UInt8} {A} {sz : UInt16} {set : UInt8 → StateM NES Unit} {f : Regs → UInt8 → Regs}
    (hA : AddrAny A sz)
    (htail : ∀ s, ((CPU.stepTail op).run s).2 =
      (checks.run ((set (NES.rdS (A s).2 (A s).1).1).run (NES.rdS (A s).2 (A s).1).2).2).2)
    (hset : ∀ x y v, RelD x y → RelD ((set v).run x).2 { y with regs := f y.regs v })
    (h : RelD s t) (h0 : 0x8000 ≤ t.regs.pc) (h2 : t.regs.pc ≤ 0xFFF0) (hop : t.prg (t.regs.pc &&& 0x7FFF) = op)
    (hi : ∀ v, (f { t.regs with pc := t.regs.pc + (1 + sz) } v).p &&& 4 ≠ 0) :
    ∃ v, RelD (CPU.step.run s).2 { t with regs := f { t.regs with pc := t.regs.pc + (1 + sz) } v } := by
  have hf := h.fetch h0
  rw [step_split, hf.1, hop, htail]
  generalize (CPU.fetch.run s).2 = s1 at hf
  have hA1 := hA s1 _ hf.2.2 (by dsimp only; revert h0 h2; bv_decide (config := { enums := false })) (by dsimp only; revert h0 h2; bv_decide (config := { enums := false }))
  have hr := hA1.read (A s1).1
  refine ⟨(NES.rdS (A s1).2 (A s1).1).1, ?_⟩
  generalize NES.rdS (A s1).2 (A s1).1 = q at hr
  have hset' := hset _ _ q.1 hr
  have e : t.regs.pc + 1 + sz = t.regs.pc + (1 + sz) := by bv_decide (config := { enums := false })
  simp only [e] at hset'
  rw [checks_id hset' (hi q.1)]
  exact hset'

theorem step_store {s : NES} {t : Plain} {op : UInt8} {A} {ea} {sel : Regs → UInt8}
    (hA : AddrOk A ea)
    (htail : ∀ s, ((CPU.stepTail op).run s).2 = (checks.run (NES.wrS (A s).2 (A s).1 (sel (Bus.regs (A s).2)))).2)
    (hsel : ∀ r : Regs, sel { r with pc := r.pc + 3 } = sel r)
    (h : RelD s t) (h0 : 0x8000 ≤ t.regs.pc) (h2 : t.regs.pc ≤ 0xFFF0) (hop : t.prg (t.regs.pc &&& 0x7FFF) = op)
    (hi : t.regs.p &&& 4 ≠ 0)
    (ha : ¬ ea (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 2 &&& 0x7FFF)) { t.regs with pc := t.regs.pc + 1 } < 0x2000)
    (hw : 0x4000 ≤ ea (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 2 &&& 0x7FFF)) { t.regs with pc := t.regs.pc + 1 } ∨
      ea (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 2 &&& 0x7FFF)) { t.regs with pc := t.regs.pc + 1 } &&& 7 ≠ 0 ∨
      sel t.regs &&& 0x80 = 0) :
    RelD (CPU.step.run s).2 { t with regs := { t.regs with pc := t.regs.pc + 3 } } := by
  have hf := h.fetch h0
  rw [step_split, hf.1, hop, htail]
  generalize (CPU.fetch.run s).2 = s1 at hf
  have hA1 := hA s1 _ hf.2.2 (by dsimp only; revert h0 h2; bv_decide (config := { enums := false })) (by dsimp only; revert h0 h2; bv_decide (config := { enums := false }))
  have e : t.regs.pc + 1 + 2 = t.regs.pc + 3 := by bv_decide (config := { enums := false })
  have e1 : t.regs.pc + 1 + 1 = t.regs.pc + 2 := by bv_decide (config := { enums := false })
  simp only [e, e1] at hA1
  have hreg : Bus.regs (A s1).2 = { t.regs with pc := t.regs.pc + 3 } := hA1.2.regs
  rw [hA1.1, hreg, hsel]
  have hw' := hA1.2.write _ _ ha hw
  rw [checks_id hw' hi]
  exact hw'

section tails
theorem tail_ad (s : NES) : ((CPU.stepTail 0xAD).run s).2 =
    (checks.run ((CPU.setA (NES.rdS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1).1).run (NES.rdS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1).2).2).2 := rfl
theorem tail_ae (s : NES) : ((CPU.stepTail 0xAE).run s).2 =
    (checks.run ((CPU.setX (NES.rdS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1).1).run (NES.rdS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1).2).2).2 := rfl
theorem tail_ac (s : NES) : ((CPU.stepTail 0xAC).run s).2 =
    (checks.run ((CPU.setY (NES.rdS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1).1).run (NES.rdS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1).2).2).2 := rfl
theorem tail_bd (s : NES) : ((CPU.stepTail 0xBD).run s).2 =
    (checks.run ((CPU.setA (NES.rdS ((CPU.aAbsX false).run s).2 ((CPU.aAbsX false).run s).1).1).run (NES.rdS ((CPU.aAbsX false).run s).2 ((CPU.aAbsX false).run s).1).2).2).2 := rfl
theorem tail_b9 (s : NES) : ((CPU.stepTail 0xB9).run s).2 =
    (checks.run ((CPU.setA (NES.rdS ((CPU.aAbsY false).run s).2 ((CPU.aAbsY false).run s).1).1).run (NES.rdS ((CPU.aAbsY false).run s).2 ((CPU.aAbsY false).run s).1).2).2).2 := rfl
theorem tail_be (s : NES) : ((CPU.stepTail 0xBE).run s).2 =
    (checks.run ((CPU.setX (NES.rdS ((CPU.aAbsY false).run s).2 ((CPU.aAbsY false).run s).1).1).run (NES.rdS ((CPU.aAbsY false).run s).2 ((CPU.aAbsY false).run s).1).2).2).2 := rfl
theorem tail_bc (s : NES) : ((CPU.stepTail 0xBC).run s).2 =
    (checks.run ((CPU.setY (NES.rdS ((CPU.aAbsX false).run s).2 ((CPU.aAbsX false).run s).1).1).run (NES.rdS ((CPU.aAbsX false).run s).2 ((CPU.aAbsX false).run s).1).2).2).2 := rfl
theorem tail_8d (s : NES) : ((CPU.stepTail 0x8D).run s).2 =
    (checks.run (NES.wrS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1 (Bus.regs (CPU.fetch16.run s).2).a)).2 := rfl
theorem tail_8e (s : NES) : ((CPU.stepTail 0x8E).run s).2 =
    (checks.run (NES.wrS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1 (Bus.regs (CPU.fetch16.run s).2).x)).2 := rfl
theorem tail_8c (s : NES) : ((CPU.stepTail 0x8C).run s).2 =
    (checks.run (NES.wrS (CPU.fetch16.run s).2 (CPU.fetch16.run s).1 (Bus.regs (CPU.fetch16.run s).2).y)).2 := rfl
theorem tail_9d (s : NES) : ((CPU.stepTail 0x9D).run s).2 =
    (checks.run (NES.wrS ((CPU.aAbsX true).run s).2 ((CPU.aAbsX true).run s).1 (Bus.regs ((CPU.aAbsX true).run s).2).a)).2 := rfl
end tails

private theorem hw_of {A : UInt16} {v : UInt8} (h : (decide (16384 ≤ A) = true ∨ ¬A &&& 7 = 0) ∨ v &&& 128 = 0) :
    0x4000 ≤ A ∨ A &&& 7 ≠ 0 ∨ v &&& 0x80 = 0 := by
  simpa [or_assoc] using h

attribute [local irreducible] CPU.aIndY in
theorem tail_b1 (s : NES) : ((CPU.stepTail 0xB1).run s).2 =
    (checks.run ((CPU.setA (NES.rdS ((CPU.aIndY false).run s).2 ((CPU.aIndY false).run s).1).1).run (NES.rdS ((CPU.aIndY false).run s).2 ((CPU.aIndY false).run s).1).2).2).2 := rfl

open Smb.Abs in
theorem io_ops (op : UInt8) (h : ioKind (decode op) = true) : op = 0x8D ∨ op = 0x8E ∨ op = 0x8C ∨ op = 0x9D := by
  have key : ∀ n : Fin 256, ioKind (decode (UInt8.ofNat n.val)) = true →
      (UInt8.ofNat n.val = 0x8D ∨ UInt8.ofNat n.val = 0x8E ∨ UInt8.ofNat n.val = 0x8C ∨ UInt8.ofNat n.val = 0x9D) := by decide
  have := key ⟨op.toNat, op.toNat_lt⟩
  simpa using this (by simpa using h)

open Smb.Abs in
theorem load_ops (op : UInt8) (h : anyLoad (decode op) = true) :
    op = 0xAD ∨ op = 0xAE ∨ op = 0xAC ∨ op = 0xBD ∨ op = 0xB1 ∨ op = 0xB9 ∨ op = 0xBE ∨ op = 0xBC := by
  have key : ∀ n : Fin 256, anyLoad (decode (UInt8.ofNat n.val)) = true →
      (UInt8.ofNat n.val = 0xAD ∨ UInt8.ofNat n.val = 0xAE ∨ UInt8.ofNat n.val = 0xAC ∨ UInt8.ofNat n.val = 0xBD ∨ UInt8.ofNat n.val = 0xB1 ∨
       UInt8.ofNat n.val = 0xB9 ∨ UInt8.ofNat n.val = 0xBE ∨ UInt8.ofNat n.val = 0xBC) := by decide
  have := key ⟨op.toNat, op.toNat_lt⟩
  simpa using this (by simpa using h)

open Smb.Abs in
/-- One hardware store on the full NES. RAM is kept, and the registers go as `eval` says. -/
theorem io_step {s : NES} {t : Plain} (h : RelD s t) (h0 : 0x8000 ≤ t.regs.pc) (h2 : t.regs.pc ≤ 0xFFF0)
    (hk : ioKind (decode (t.prg (t.regs.pc &&& 0x7FFF))) = true)
    (hok : ioAddrOk (decode (t.prg (t.regs.pc &&& 0x7FFF))) (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 2 &&& 0x7FFF)) t.regs = true)
    (hi : t.regs.p &&& 4 ≠ 0) :
    RelD (CPU.step.run s).2
      { t with regs := (eval (decode (t.prg (t.regs.pc &&& 0x7FFF))) (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 2 &&& 0x7FFF)) t.regs 0 0 0).regs } := by
  generalize hop : t.prg (t.regs.pc &&& 0x7FFF) = op at *
  generalize hb1 : t.prg (t.regs.pc + 1 &&& 0x7FFF) = b1 at *
  generalize hb2 : t.prg (t.regs.pc + 2 &&& 0x7FFF) = b2 at *
  rcases io_ops op hk with rfl | rfl | rfl | rfl
  · have hd : decode 0x8D = .store .a .abs := by decide
    simp only [hd] at hok ⊢
    simp only [ioAddrOk, operandAddr, ea, regOf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq, ne_eq] at hok
    have ha : ¬ base b1 b2 < 0x2000 := by have := hok.1.1; revert this; bv_decide (config := { enums := false })
    have hv := step_store (sel := Regs.a) addr_abs tail_8d (fun _ => rfl) h h0 h2 hop hi
      (by rw [hb1, hb2]; exact ha) (by rw [hb1, hb2]; exact hw_of hok.2)
    exact hb1 ▸ hb2 ▸ hv.congr rfl rfl rfl
  · have hd : decode 0x8E = .store .x .abs := by decide
    simp only [hd] at hok ⊢
    simp only [ioAddrOk, operandAddr, ea, regOf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq, ne_eq] at hok
    have ha : ¬ base b1 b2 < 0x2000 := by have := hok.1.1; revert this; bv_decide (config := { enums := false })
    have hv := step_store (sel := Regs.x) addr_abs tail_8e (fun _ => rfl) h h0 h2 hop hi
      (by rw [hb1, hb2]; exact ha) (by rw [hb1, hb2]; exact hw_of hok.2)
    exact hb1 ▸ hb2 ▸ hv.congr rfl rfl rfl
  · have hd : decode 0x8C = .store .y .abs := by decide
    simp only [hd] at hok ⊢
    simp only [ioAddrOk, operandAddr, ea, regOf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq, ne_eq] at hok
    have ha : ¬ base b1 b2 < 0x2000 := by have := hok.1.1; revert this; bv_decide (config := { enums := false })
    have hv := step_store (sel := Regs.y) addr_abs tail_8c (fun _ => rfl) h h0 h2 hop hi
      (by rw [hb1, hb2]; exact ha) (by rw [hb1, hb2]; exact hw_of hok.2)
    exact hb1 ▸ hb2 ▸ hv.congr rfl rfl rfl
  · have hd : decode 0x9D = .store .a .absx := by decide
    simp only [hd] at hok ⊢
    simp only [ioAddrOk, operandAddr, ea, regOf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq, ne_eq] at hok
    have ha : ¬ base b1 b2 + t.regs.x.toUInt16 < 0x2000 := by have := hok.1.1; revert this; bv_decide (config := { enums := false })
    have hv := step_store (sel := Regs.a) (addr_absx true) tail_9d (fun _ => rfl) h h0 h2 hop hi
      (by rw [hb1, hb2]; exact ha) (by rw [hb1, hb2]; exact hw_of hok.2)
    exact hb1 ▸ hb2 ▸ hv.congr rfl rfl rfl

open Smb.Abs in
/-- A load that may read anywhere on the full NES: some value was read, the registers go as `eval` says, and RAM is kept. -/
theorem load_step {s : NES} {t : Plain} (h : RelD s t) (h0 : 0x8000 ≤ t.regs.pc) (h2 : t.regs.pc ≤ 0xFFF0)
    (hk : anyLoad (decode (t.prg (t.regs.pc &&& 0x7FFF))) = true)
    (hi : ∀ v : UInt8, nz t.regs.p v &&& 4 ≠ 0) :
    ∃ v, RelD (CPU.step.run s).2
      { t with regs := (eval (decode (t.prg (t.regs.pc &&& 0x7FFF))) 0 0 t.regs 0 0 v).regs } := by
  generalize hop : t.prg (t.regs.pc &&& 0x7FFF) = op at *
  rcases load_ops op hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd : decode 0xAD = .load .a .abs := by decide
    simp only [hd]
    obtain ⟨v, hv⟩ := step_load (f := fun r v => { r with a := v, p := nz r.p v }) any_abs tail_ad
      (fun _ _ v h => h.setA v) h h0 h2 hop (fun v => hi v)
    exact ⟨v, hv.congr rfl rfl rfl⟩
  · have hd : decode 0xAE = .load .x .abs := by decide
    simp only [hd]
    obtain ⟨v, hv⟩ := step_load (f := fun r v => { r with x := v, p := nz r.p v }) any_abs tail_ae
      (fun _ _ v h => h.setX v) h h0 h2 hop (fun v => hi v)
    exact ⟨v, hv.congr rfl rfl rfl⟩
  · have hd : decode 0xAC = .load .y .abs := by decide
    simp only [hd]
    obtain ⟨v, hv⟩ := step_load (f := fun r v => { r with y := v, p := nz r.p v }) any_abs tail_ac
      (fun _ _ v h => h.setY v) h h0 h2 hop (fun v => hi v)
    exact ⟨v, hv.congr rfl rfl rfl⟩
  · have hd : decode 0xBD = .load .a .absx := by decide
    simp only [hd]
    obtain ⟨v, hv⟩ := step_load (f := fun r v => { r with a := v, p := nz r.p v }) (any_absx false) tail_bd
      (fun _ _ v h => h.setA v) h h0 h2 hop (fun v => hi v)
    exact ⟨v, hv.congr rfl rfl rfl⟩
  · have hd : decode 0xB1 = .load .a .indy := by decide
    simp only [hd]
    obtain ⟨v, hv⟩ := step_load (f := fun r v => { r with a := v, p := nz r.p v }) any_indy tail_b1
      (fun _ _ v h => h.setA v) h h0 h2 hop (fun v => hi v)
    exact ⟨v, hv.congr rfl rfl rfl⟩
  · have hd : decode 0xB9 = .load .a .absy := by decide
    simp only [hd]
    obtain ⟨v, hv⟩ := step_load (f := fun r v => { r with a := v, p := nz r.p v }) (any_absy false) tail_b9
      (fun _ _ v h => h.setA v) h h0 h2 hop (fun v => hi v)
    exact ⟨v, hv.congr rfl rfl rfl⟩
  · have hd : decode 0xBE = .load .x .absy := by decide
    simp only [hd]
    obtain ⟨v, hv⟩ := step_load (f := fun r v => { r with x := v, p := nz r.p v }) (any_absy false) tail_be
      (fun _ _ v h => h.setX v) h h0 h2 hop (fun v => hi v)
    exact ⟨v, hv.congr rfl rfl rfl⟩
  · have hd : decode 0xBC = .load .y .absx := by decide
    simp only [hd]
    obtain ⟨v, hv⟩ := step_load (f := fun r v => { r with y := v, p := nz r.p v }) (any_absx false) tail_bc
      (fun _ _ v h => h.setY v) h h0 h2 hop (fun v => hi v)
    exact ⟨v, hv.congr rfl rfl rfl⟩

/-! ## The invariant on the full NES -/

namespace Abs

theorem Holds.cyc {prot g ram0 b} {t : Plain} (h : Holds prot g ram0 b t) (c : UInt64) : Holds prot g ram0 b { t with cyc := c } :=
  { pc := h.pc, sp := h.sp, a := h.a, x := h.x, y := h.y, p := h.p, i := h.i, bad := h.bad, cells := h.cells, glob := h.glob, frame := h.frame }

/-- A full NES state whose CPU view is some plain state in the table. Nothing is said about the PPU, the cycle count or a
latched DMA: the invariant holds at every instruction boundary, with whatever timing, including lag. -/
def NInv (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (ram0 : UInt16 → UInt8) (T : Table) (s : NES) : Prop :=
  ∃ t, RelD s t ∧ Code rom t ∧ Inv prot g ram0 T t

theorem ioAddrOk_agree {k : Kind} (hk : ioKind k = true) (b1 b2 : UInt8) (pc : UInt16) (a x y sp p : UInt8) :
    ioAddrOk k b1 b2 ⟨pc, if readsA k then a else 0, if readsX k then x else 0, if readsY k then y else 0, sp, p⟩ =
      ioAddrOk k b1 b2 ⟨pc, a, x, y, sp, p⟩ := by
  cases k with
  | store r m => cases r <;> cases m <;> simp [ioKind] at hk <;> simp [ioAddrOk, operandAddr, ea, regOf, readsA, readsX, readsY, Mode.usesX, Mode.usesY] <;> rfl
  | _ => simp [ioKind] at hk

theorem hreg {r w : Bool} {t u : VS} {e0 e v : UInt8} (h1 : (if r || w then u.mem e0 else t.sub u) = true)
    (h2 : if r || w then e0 = e else e = v) (h3 : t.mem v = true) : u.mem e = true := by
  by_cases hr : (r || w) = true
  · simp only [hr, if_true] at h1 h2
    rw [← h2]; exact h1
  · simp only [hr, if_false] at h1 h2
    rw [h2]; exact VS.sub_sound h1 h3

/-- The next state of a box of hardware stores: the registers go as `eval` says, RAM is kept. -/
theorem io_box_next {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {t : Plain} {b : Box} (hc : Code rom t) (hb : Holds prot g ram0 b t) (hbox : ioBox rom g T b = true) :
    0x8000 ≤ t.regs.pc ∧ t.regs.pc ≤ 0xFFF0 ∧ ioKind (decode (t.prg (t.regs.pc &&& 0x7FFF))) = true ∧
    ioAddrOk (decode (t.prg (t.regs.pc &&& 0x7FFF))) (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 2 &&& 0x7FFF)) t.regs = true ∧
    Inv prot g ram0 T { t with regs := (eval (decode (t.prg (t.regs.pc &&& 0x7FFF))) (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 2 &&& 0x7FFF)) t.regs 0 0 0).regs } := by
  have hpcb := hb.pc
  unfold ioBox at hbox
  simp only [← hpcb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true, bne_iff_ne, ne_eq] at hbox
  obtain ⟨⟨⟨h0, h2⟩, hk⟩, hall⟩ := hbox
  have hprg : t.prg (t.regs.pc &&& 0x7FFF) = rom t.regs.pc := hc _ h0
  have hb1 : t.prg (t.regs.pc + 1 &&& 0x7FFF) = rom (t.regs.pc + 1) := hc _ (by revert h0 h2; bv_decide (config := { enums := false }))
  have hb2 : t.prg (t.regs.pc + 2 &&& 0x7FFF) = rom (t.regs.pc + 2) := hc _ (by revert h0 h2; bv_decide (config := { enums := false }))
  rw [hprg, hb1, hb2]
  generalize decode (rom t.regs.pc) = k at hk hall ⊢
  generalize rom (t.regs.pc + 1) = b1 at hall ⊢
  generalize rom (t.regs.pc + 2) = b2 at hall ⊢
  have hsp : b.s = t.regs.s := hb.sp.symm
  rw [hsp] at hall
  have hl := hall (if readsA k then t.regs.a else 0) (regList_mem hb.a) (if readsX k then t.regs.x else 0) (regList_mem hb.x)
    (if readsY k then t.regs.y else 0) (regList_mem hb.y) t.regs.p (VS.mem_elems hb.p)
  obtain ⟨⟨hok, hI⟩, cand, hcm, hcov⟩ := hl
  rw [ioAddrOk_agree hk] at hok
  have ha := eval_agree k b1 b2 t.regs.pc t.regs.a t.regs.x t.regs.y t.regs.s t.regs.p 0 0 0
  simp only [ite_self] at ha
  obtain ⟨_, _, _, _, gpc, gs, gp, ga, gx, gy⟩ := ha
  rw [gp] at hI
  rw [gpc] at hcm
  simp only [covers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcov
  obtain ⟨⟨⟨⟨⟨⟨hcpc, hcs⟩, hcp⟩, hca⟩, hcx⟩, hcy⟩, hcc⟩ := hcov
  rw [gpc] at hcpc
  rw [gs] at hcs
  rw [gp] at hcp
  refine ⟨h0, h2, hk, hok, cand, hcm, ?_⟩
  exact {
    pc := hcpc.symm
    sp := hcs.symm
    a := hreg hca ga hb.a
    x := hreg hcx gx hb.x
    y := hreg hcy gy hb.y
    p := hcp
    i := hI
    bad := hb.bad
    cells := by
      intro c hcin
      have hcc' := hcc c hcin
      simp only [cellCoveredR, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, reduceCtorEq, false_and, or_false] at hcc'
      simpa [applyW] using cellCovered_sound hb hcc'
    glob := hb.glob
    frame := hb.frame }

theorem io_box_sound {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} {t : Plain} {b : Box} (h : RelD s t) (hc : Code rom t) (hb : Holds prot g ram0 b t)
    (hbox : ioBox rom g T b = true) :
    NInv rom prot g ram0 T (CPU.step.run s).2 := by
  obtain ⟨h0, h2, hk, hok, hinv⟩ := io_box_next hc hb hbox
  exact ⟨_, io_step h h0 h2 hk hok hb.i, fun a' ha' => hc a' ha', hinv⟩

private theorem nz_cases (p v : UInt8) : nz p v = nz p 0 ∨ nz p v = nz p 1 ∨ nz p v = nz p 0x80 := by
  simp only [nz, CPU.FN, CPU.FZ]
  bv_decide (config := { enums := false })

private theorem nz_i (p v : UInt8) (h : p &&& 4 ≠ 0) : nz p v &&& 4 ≠ 0 := by
  simp only [nz, CPU.FN, CPU.FZ]
  revert h
  bv_decide (config := { enums := false })

private theorem load_reg {w : Bool} {t u : VS} {e v : UInt8}
    (h : (if w then (match u with | .top => true | _ => false) else t.sub u) = true)
    (he : w = false → e = v) (hv : t.mem v = true) : u.mem e = true := by
  cases w with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    rw [he rfl]; exact VS.sub_sound h hv
  | true =>
    simp only [if_true] at h
    cases u with
    | top => rfl
    | set l => simp at h

theorem load_holds {prot : UInt16 → Bool} {g : Global} {ram0 : UInt16 → UInt8} {t : Plain} {b cand : Box} {k : Kind} {next : UInt16}
    (hcov : loadCovers g b k next cand = true) (hb : Holds prot g ram0 b t) {e : Regs} {v : UInt8}
    (hpc : e.pc = next) (hs : e.s = t.regs.s) (hp : e.p = nz t.regs.p v)
    (ha : writesA k = false → e.a = t.regs.a) (hx : writesX k = false → e.x = t.regs.x) (hy : writesY k = false → e.y = t.regs.y) :
    Holds prot g ram0 cand { t with regs := e } := by
  simp only [loadCovers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcov
  obtain ⟨⟨⟨⟨⟨⟨hcpc, hcs⟩, hca⟩, hcx⟩, hcy⟩, hcp⟩, hcc⟩ := hcov
  have hpm := hcp t.regs.p (VS.mem_elems hb.p)
  exact {
    pc := hpc.trans hcpc.symm
    sp := by rw [hcs]; exact hs.trans hb.sp
    a := load_reg hca ha hb.a
    x := load_reg hcx hx hb.x
    y := load_reg hcy hy hb.y
    p := by
      show cand.p.mem e.p = true
      rw [hp]
      rcases nz_cases t.regs.p v with h | h | h <;> rw [h]
      · exact hpm.1.1
      · exact hpm.1.2
      · exact hpm.2
    i := by
      show e.p &&& 4 ≠ 0
      rw [hp]; exact nz_i _ _ hb.i
    bad := hb.bad
    cells := by
      intro c hcin
      simpa [applyW] using cellCovered_sound hb (hcc c hcin)
    glob := hb.glob
    frame := hb.frame }

theorem load_box_sound {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} {t : Plain} {b : Box} (h : RelD s t) (hc : Code rom t) (hb : Holds prot g ram0 b t)
    (hbox : loadBox rom g T b = true) :
    NInv rom prot g ram0 T (CPU.step.run s).2 := by
  have hpcb := hb.pc
  unfold loadBox at hbox
  simp only [← hpcb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true, bne_iff_ne, ne_eq] at hbox
  obtain ⟨⟨⟨⟨h0, h2⟩, hk⟩, _⟩, cand, hcm, hcov⟩ := hbox
  have hprg : t.prg (t.regs.pc &&& 0x7FFF) = rom t.regs.pc := hc _ h0
  obtain ⟨v, hv⟩ := load_step h h0 h2 (by rw [hprg]; exact hk) (fun v => nz_i _ v hb.i)
  rw [hprg] at hv
  generalize hkk : decode (rom t.regs.pc) = k at *
  have hnext : (eval k 0 0 t.regs 0 0 v).regs.pc = (match (generalizing := false) k with | .load _ m => t.regs.pc + m.size | _ => t.regs.pc) := by
    cases k with
    | load r m => cases r <;> cases m <;> simp [anyLoad] at hk <;> rfl
    | _ => simp [anyLoad] at hk
  refine ⟨_, hv, fun a' ha' => hc a' ha', cand, ?_, ?_⟩
  · show cand ∈ T.at (eval k 0 0 t.regs 0 0 v).regs.pc
    rw [hnext]; exact hcm
  · refine load_holds (v := v) hcov hb hnext ?_ ?_ ?_ ?_ ?_ <;>
      (cases k with
       | load r m => cases r <;> cases m <;> simp [anyLoad] at hk <;> first | rfl | (intro h; first | rfl | simp [writesA, writesX, writesY] at h)
       | _ => simp [anyLoad] at hk)

/-- The run's hypothesis at a state: the assumed cells are within their bounds. It holds for free where those are unconstrained. -/
def Clean (g : Global) (s : NES) : Prop :=
  (gAt g 0x300).mem (s.ram.get! 0x300) = true ∧ (gAt g 0x340).mem (s.ram.get! 0x340) = true

theorem clean_of_top {g : Global} (h : gAt g 0x300 = .top) (h2 : gAt g 0x340 = .top) (s : NES) : Clean g s := by
  unfold Clean; rw [h, h2]; exact ⟨rfl, rfl⟩

theorem Clean.plain {g : Global} {s : NES} {f : UInt16 → UInt8} (h : Clean g s)
    (hram : ∀ i : UInt16, s.ram.get! (i &&& 0x7FF).toNat = f (i &&& 0x7FF)) : AssumedOk g f := by
  intro i hi
  have hc : i = 0x300 ∨ i = 0x340 := by simpa [assumedCell] using hi
  rcases hc with rfl | rfl
  · have e := hram 0x300
    have e1 : (0x300 : UInt16) &&& 0x7FF = 0x300 := by decide
    rw [e1] at e
    rw [← e]
    exact h.1
  · have e := hram 0x340
    have e1 : (0x340 : UInt16) &&& 0x7FF = 0x340 := by decide
    rw [e1] at e
    rw [← e]
    exact h.2

/-- The cells `prot` holds to `ram0`, off the stack page, are as they should be. An instruction's check shows this whatever it does to the assumed cells, so `Clean` can depend on it. -/
def ProtKept (prot : UInt16 → Bool) (ram0 : UInt16 → UInt8) (s : NES) : Prop :=
  ∀ i : UInt16, prot (i &&& 0x7FF) = true → 0x200 ≤ i &&& 0x7FF → s.ram.get! (i &&& 0x7FF).toNat = ram0 (i &&& 0x7FF)

/-- A box of the plain-machine checker, on the full NES. A DMA latched by the instruction before runs at the first read and
leaves the CPU view alone. -/
theorem plain_box_sound {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} {t : Plain} {b : Box} (h : RelD s t) (hc : Code rom t) (hb : Holds prot g ram0 b t)
    (hck : checkBox rom prot g T b = true) (hA : ProtKept prot ram0 (CPU.step.run s).2 → Clean g (CPU.step.run s).2) :
    NInv rom prot g ram0 T (CPU.step.run s).2 := by
  have h0 : 0x8000 ≤ t.regs.pc := by
    have := hck
    unfold checkBox at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    rw [hb.pc]
    exact this.1.1.1
  have hf := h.fetch h0
  rw [step_split, hf.1] at hA ⊢
  generalize (CPU.fetch.run s).2 = s1 at hf hA
  have hr := hf.2.2.rel hf.2.1
  let t0 : Plain := { t with cyc := s1.cyc - 1 }
  have hrd : Plain.readable t.regs.pc = true := by simp [Plain.readable, h0]
  have ht1 : (CPU.fetch.run t0).2 = { { t with regs := { t.regs with pc := t.regs.pc + 1 } } with cyc := s1.cyc } := by
    change Plain.mk { t.regs with pc := t.regs.pc + 1 } t.ram t.prg (s1.cyc - 1 + 1) (t.bad || !Plain.readable t.regs.pc) = _
    rw [hrd, hb.bad]
    simp
  have hv1 : (CPU.fetch.run t0).1 = t.prg (t.regs.pc &&& 0x7FFF) := by
    change Plain.memRead t.ram t.prg t.regs.pc = _
    have hn : Plain.inRam t.regs.pc = false := by
      simp only [Plain.inRam, decide_eq_false_iff_not]; revert h0; bv_decide (config := { enums := false })
    simp [Plain.memRead, hn]
  have hbox := inv_step_box (s := t0) hck hc (hb.cyc _)
  obtain ⟨hcode, c, hcm, hcb⟩ := hbox
  have hstep : (CPU.step.run t0).2 = ((CPU.stepTail (t.prg (t.regs.pc &&& 0x7FFF))).run { { t with regs := { t.regs with pc := t.regs.pc + 1 } } with cyc := s1.cyc }).2 := by
    rw [← hv1, ← ht1]; rfl
  have hsim := (Sim.stepTail (t.prg (t.regs.pc &&& 0x7FFF))).2 s1 _ hr (by rw [← hstep]; exact hcb.bad)
  rw [← hstep] at hsim
  exact ⟨_, RelD.of_rel hsim.2, hcode, c, hcm, hcb.holds ((hA (fun i hp _ => (hsim.2.ram i).trans (hcb.frame _ hp))).plain hsim.2.ram)⟩

/-- A box `checkBox` accepts: the full machine's step is the plain machine's, at some cycle count, and leaves no DMA latched. -/
theorem plain_box_rel {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} {t : Plain} {b : Box} (h : RelD s t) (hc : Code rom t) (hb : Holds prot g ram0 b t)
    (hck : checkBox rom prot g T b = true) :
    ∃ c, Rel (CPU.step.run s).2 (CPU.step.run ({ t with cyc := c } : Plain)).2 := by
  have h0 : 0x8000 ≤ t.regs.pc := by
    have := hck
    unfold checkBox at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    rw [hb.pc]
    exact this.1.1.1
  have hf := h.fetch h0
  rw [step_split, hf.1]
  generalize (CPU.fetch.run s).2 = s1 at hf
  have hr := hf.2.2.rel hf.2.1
  let t0 : Plain := { t with cyc := s1.cyc - 1 }
  have hrd : Plain.readable t.regs.pc = true := by simp [Plain.readable, h0]
  have ht1 : (CPU.fetch.run t0).2 = { { t with regs := { t.regs with pc := t.regs.pc + 1 } } with cyc := s1.cyc } := by
    change Plain.mk { t.regs with pc := t.regs.pc + 1 } t.ram t.prg (s1.cyc - 1 + 1) (t.bad || !Plain.readable t.regs.pc) = _
    rw [hrd, hb.bad]
    simp
  have hv1 : (CPU.fetch.run t0).1 = t.prg (t.regs.pc &&& 0x7FFF) := by
    change Plain.memRead t.ram t.prg t.regs.pc = _
    have hn : Plain.inRam t.regs.pc = false := by
      simp only [Plain.inRam, decide_eq_false_iff_not]; revert h0; bv_decide (config := { enums := false })
    simp [Plain.memRead, hn]
  have hbox := inv_step_box (s := t0) hck hc (hb.cyc _)
  obtain ⟨_, _, _, hcb⟩ := hbox
  have hstep : (CPU.step.run t0).2 = ((CPU.stepTail (t.prg (t.regs.pc &&& 0x7FFF))).run { { t with regs := { t.regs with pc := t.regs.pc + 1 } } with cyc := s1.cyc }).2 := by
    rw [← hv1, ← ht1]; rfl
  have hsim := (Sim.stepTail (t.prg (t.regs.pc &&& 0x7FFF))).2 s1 _ hr (by rw [← hstep]; exact hcb.bad)
  rw [← hstep] at hsim
  exact ⟨_, hsim.2⟩

/-- One instruction on the full NES: a table `checkN` accepted keeps the invariant, unless the state sits at an exit. -/
theorem ninv_step {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} (hchk : checkN rom exit prot g T = true) (h : NInv rom prot g ram0 T s) (hx : exit s.pc = false)
    (hA : Clean g (CPU.step.run s).2) :
    NInv rom prot g ram0 T (CPU.step.run s).2 := by
  obtain ⟨t, hr, hc, b, hbm, hb⟩ := h
  have hpc : s.pc = t.regs.pc := congrArg Regs.pc hr.regs
  have hbox := by
    simp only [checkN, checkAny, List.all_eq_true, List.mem_range] at hchk
    exact hchk _ (table_at_lt t.regs.pc) b hbm
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq] at hbox
  obtain ⟨_, hstep⟩ := hbox
  rw [← hb.pc, ← hpc] at hstep
  rcases hstep with h1 | ((h1 | h1) | h1)
  · rw [hx] at h1; simp at h1
  · exact plain_box_sound hr hc hb h1 (fun _ => hA)
  · exact io_box_sound hr hc hb h1
  · exact load_box_sound hr hc hb h1

/-- The invariant holds along any bounded run to the table's one exit. -/
theorem ninv_runTo {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    (hchk : checkN rom exit prot g T = true) (htop : gAt g 0x300 = .top) (htop2 : gAt g 0x340 = .top) (stop : UInt16) (hexit : ∀ a, exit a = true → a = stop)
    (n : Nat) (s : NES) (h : NInv rom prot g ram0 T s) :
    NInv rom prot g ram0 T ((CPU.runTo (σ := NES) stop n).run s).2 := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    have hregs : (Bus.regs s).pc = s.pc := rfl
    by_cases hx : s.pc = stop
    · simpa only [CPU.runTo, CPU.getRegs, hregs, hx, ↓reduceIte, bind, StateT.bind, pure, StateT.pure, StateT.run] using h
    · have hx' : exit s.pc = false := by
        cases he : exit s.pc with
        | false => rfl
        | true => exact absurd (hexit _ he) hx
      have hs := ninv_step hchk h hx' (clean_of_top htop htop2 _)
      have hn := ih (CPU.step.run s).2 hs
      simp only [CPU.runTo, CPU.getRegs, hregs, hx, ↓reduceIte, bind, StateT.bind, StateT.run]
      cases he : CPU.step s with
      | mk u t => simpa only [StateT.run, he] using hn

end Abs
end Smb
