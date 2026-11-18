import Smb.Goal.PlayCycleFacts
import Smb.Routine.PpuBoot

/-! # The normal-play invariant holds on the TAS

`CycleInv` is the invariant `normal_play_run` carries, and every result about normal play assumes it at some start.
If no real state satisfied it, those results would be empty. `cycleB` tests a frame's end, waiting in `EndlessLoop` at
`$8057`: its box in the closing region's table, its saved parser tuple and the PPU stage the region needs.
`cycleInv_of_cycleB` shows that's enough, and `tas_in_cycle` that the TAS passes on 656 frame ends. This is evidence
the invariant is satisfiable on real play, not that every run reaches it. -/
namespace Smb.Goal.OneOne
open Smb Smb.NES Smb.Abs Smb.Routine Smb.Routine.PlayCycle Smb.Routine.FrameGuard Smb.Routine.PpuFrame
  Smb.Routine.PlaySavedHandoffs

/-- An NES state seen as the checker's machine. -/
def plainOf (s : NES) : Plain :=
  ⟨⟨s.pc, s.a, s.x, s.y, s.s, s.p⟩, (fun i => s.ram.get! (i &&& 0x7FF).toNat),
    (fun a => s.prg.get! (a &&& 0x7FFF).toNat), s.cyc, false⟩

/-- Every field of `Holds` but the protected-memory frame, which holds outright when `ram0` is the state's own RAM. -/
def holdsB (g : Global) (b : Box) (t : Plain) : Bool :=
  t.regs.pc == b.pc && t.regs.s == b.s && b.a.mem t.regs.a && b.x.mem t.regs.x && b.y.mem t.regs.y &&
    b.p.mem t.regs.p && (t.regs.p &&& 4 != 0) && !t.bad && b.cells.all (fun c => c.2.mem (t.ram c.1)) &&
    (List.range 65536).all (fun n => (gAt g n.toUInt16).mem (t.ram n.toUInt16))

theorem holds_of_holdsB {prot : UInt16 → Bool} {g : Global} {b : Box} {t : Plain} (h : holdsB g b t = true) :
    Holds prot g t.ram b t := by
  simp only [holdsB, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
    List.all_eq_true, and_assoc] at h
  obtain ⟨hpc, hs, ha, hx, hy, hp, hi, hb, hc, hg⟩ := h
  refine ⟨hpc, hs, ha, hx, hy, hp, hi, hb, hc, fun i => ?_, fun _ _ => rfl⟩
  have := hg i.toNat (List.mem_range.mpr i.toNat_lt)
  simpa using this

theorem and7ff (i : UInt16) : (i &&& 0x7FF) &&& 0x7FF = i &&& 0x7FF := by bv_decide
theorem and7fff (i : UInt16) : (i &&& 0x7FFF) &&& 0x7FFF = i &&& 0x7FFF := by bv_decide

theorem relOn_plainOf {s : NES} (hsz : s.ram.size = 0x800) (hd : s.dmaPending = false) : RelOn s (plainOf s) :=
  ⟨rfl, fun i => by simp only [plainOf, and7ff], hsz, fun a => by simp only [plainOf, and7fff], hd⟩

theorem code_plainOf {s : NES} (hp : s.prg = Smb.prg) : Code (romOf Smb.prg) (plainOf s) := by
  intro a _
  simp only [plainOf, romOf, and7fff, hp]

/-- `AF 600`, run as a test. -/
def af600B (x : NES) : Bool :=
  !x.nmiPolled && ((!x.vbl && !x.nmiLine && !x.nmiPending) ||
    (x.vbl && decide (x.fpos.toNat ≤ 600) && !x.nmiLine && !x.nmiPending) ||
    (x.vbl && decide (x.fpos.toNat ≤ 600) && x.nmiLine && x.nmiPending))

theorem af600_of {x : NES} (h : af600B x = true) : AF 600 x := by
  unfold af600B at h
  unfold AF A0 A1 A2 St0 St1 St2
  cases hp : x.nmiPolled <;> cases hv : x.vbl <;> cases hl : x.nmiLine <;> cases hn : x.nmiPending <;>
    simp_all

/-- What `CycleInv` asks of a frame's end in `EndlessLoop`, as a test: its box in the closing table, its saved
parser tuple and its PPU stage. -/
def cycleB (s : NES) : Bool :=
  s.pc == 0x8057 && decide (s.prg.data = Smb.prg.data) && !s.unmodelled && s.ram.size == 0x800 && !s.dmaPending && (s.ctrl &&& 0x80 != 0) &&
    ((reg PlayFrame.Z).T.at 0x8057).any (fun b => holdsB PlayParser.G b (plainOf s)) &&
    PlayParser.entryTuples.any (fun e => e.cells.all fun k =>
      !(PlayParser.chainCells.contains k.1) || k.2.mem ((plainOf s).ram k.1)) &&
    af600B s

/-- A state two or more frames from power-on that passes `cycleB` is in the normal-play invariant. -/
theorem cycleInv_of_cycleB (p q : UInt8) (l : List UInt8) (h : cycleB (NES.runFrames (p :: q :: l) initial) = true) :
    CycleInv (NES.runFrames (p :: q :: l) initial) := by
  generalize hw : NES.runFrames (p :: q :: l) initial = w at h
  have hsch : SchS w := by
    have := Smb.Routine.PpuBoot.sch_run p q l
    rw [hw] at this
    rcases this with hu | hs
    · simp only [cycleB, hu, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true] at h
    · exact hs
  simp only [cycleB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq, and_assoc] at h
  obtain ⟨hpc, hd, _, hsz, hdma, hctrl, hbox, hsaved, haf⟩ := h
  have hprg : w.prg = Smb.prg := by
    have hd : w.prg.data = Smb.prg.data := by simpa using hd
    cases h1 : w.prg; cases h2 : Smb.prg; simp_all
  obtain ⟨b, hb, hh⟩ := List.any_eq_true.mp hbox
  obtain ⟨e, he, hes⟩ := List.any_eq_true.mp hsaved
  have hon : onPC 0x8057 = true := by native_decide
  have hz : reg PlayFrame.Z ∈ regions :=
    List.mem_map.mpr ⟨PlayFrame.Z, List.mem_append_left _ (by simp [normalConfigs]), rfl⟩
  refine ⟨Or.inr hsch, hprg, reg PlayFrame.Z, hz, (plainOf w).ram,
    ⟨plainOf w, code_plainOf hprg, ⟨b, (by simpa [plainOf, hpc] using hb), holds_of_holdsB hh⟩,
      Or.inr ⟨(by simpa [plainOf, hpc] using hon), relOn_plainOf hsz hdma⟩⟩, ?_, fun _ => Or.inl ?_⟩
  · refine Or.inl ⟨PlayFrame.Z, by simp [normalConfigs], rfl, e, he, fun k hk hc => ?_⟩
    have := List.all_eq_true.mp hes k hk
    have hm : k.1 ∈ PlayParser.chainCells := by simpa using hc
    simpa [hm] using this
  · exact ⟨hprg, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpc, ⟨hsch, hctrl, hdma⟩, af600_of haf⟩)))))⟩

theorem at_succ' (inputs : List UInt8) (f : Nat) (hf : f < inputs.length) :
    at' inputs (f + 1) = NES.frame (inputs.getD f 0) 0 (at' inputs f) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hf, Option.getD_some]
  simp only [at', NES.runFrames, List.take_add_one, List.getElem?_eq_getElem hf, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `cycleInv_of_cycleB` for a frame of any input list, past the first two. -/
theorem cycleInv_at (inputs : List UInt8) (f : Nat) (h2 : 2 ≤ f) (hl : f ≤ inputs.length)
    (h : cycleB (at' inputs f) = true) : CycleInv (at' inputs f) := by
  have ht : (inputs.take f).length = f := by rw [List.length_take]; omega
  unfold at' at h ⊢
  match hm : inputs.take f, ht with
  | p :: q :: l, _ => exact cycleInv_of_cycleB p q l (hm ▸ h)
  | [], ht | [_], ht => simp at ht; omega

/-- `cycleB` on `n` consecutive frame ends from `s`, frame `f`, running each frame once. -/
def cycleRun (inputs : List UInt8) (s : NES) (f : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => cycleB s && decide (f < inputs.length) && cycleRun inputs (NES.frame (inputs.getD f 0) 0 s) (f + 1) n

theorem cycleRun_spec (inputs : List UInt8) (n f : Nat) (h : cycleRun inputs (at' inputs f) f n = true) :
    ∀ k, k < n → cycleB (at' inputs (f + k)) = true := by
  induction n generalizing f with
  | zero => intro k hk; omega
  | succ n ih =>
    simp only [cycleRun, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, hf⟩, hr⟩ := h
    rw [← at_succ' inputs f hf] at hr
    intro k hk
    cases k with
    | zero => simpa using hb
    | succ k =>
      have := ih (f + 1) hr k (by omega)
      rwa [show f + 1 + k = f + (k + 1) by omega] at this

/-- Every frame end of the TAS in normal play on the surface is in the invariant: from first control, through the pipe
entry (frame 562) and the pipe-down animation, to 610, where the area change starts (`$0772` = 0); and from the
surface pipe exit, through the flag-loaded frames, to 1,286. The bonus room is another area, outside these tables.
Frame 1,286 is the flag grab, which leaves `$0E` = 5 and `$1D` = 3, outside the cycle's bounds. -/
theorem tas_run1 : cycleRun tasInputs (at' tasInputs 195) 195 416 = true := by native_decide
theorem tas_run2 : cycleRun tasInputs (at' tasInputs 1047) 1047 240 = true := by native_decide
theorem tas_len : 1286 ≤ tasInputs.length := by native_decide

theorem tas_in_cycle (f : Nat) (hf : (195 ≤ f ∧ f ≤ 610) ∨ (1047 ≤ f ∧ f ≤ 1286)) : CycleInv (at' tasInputs f) := by
  have h1 := tas_run1
  have h2 := tas_run2
  have hb : cycleB (at' tasInputs f) = true := by
    rcases hf with hf | hf
    · have := cycleRun_spec _ _ _ h1 (f - 195) (by omega)
      rwa [show 195 + (f - 195) = f by omega] at this
    · have := cycleRun_spec _ _ _ h2 (f - 1047) (by omega)
      rwa [show 1047 + (f - 1047) = f by omega] at this
  have hlen := tas_len
  exact cycleInv_at tasInputs f (by omega) (Nat.le_trans (show f ≤ 1286 by omega) hlen) hb

/-- So the checked normal-play results aren't vacuous. -/
theorem tas_not_left (f : Nat) (hf : (195 ≤ f ∧ f ≤ 610) ∨ (1047 ≤ f ∧ f ≤ 1286)) : left (at' tasInputs f) = false :=
  cycle_not_left (tas_in_cycle f hf)

end Smb.Goal.OneOne
