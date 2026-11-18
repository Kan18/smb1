import Smb.Nes
import Smb.Plain
import Std.Tactic.BVDecide

/-!
# Refinement: the full NES runs CPU code exactly like the plain machine

`Rel s t` relates a full NES state `s` to a plain state `t`: same CPU registers, RAM,
ROM and cycle count, with NMI generation off (`PPUCTRL.7 = 0`) and no NMI or OAM DMA
pending. `Sim m₁ m₂` says the full-machine program `m₁` and the plain program `m₂` return
the same value and preserve `Rel` whenever the plain run does not go `bad`.

The main theorem, `sim_step`, is that one `CPU.step` on the two machines simulates.
Since `CPU.step` is one piece of code instantiated with two buses, the proof only has to
relate the bus operations; the rest is mechanical, opcode by opcode.

The PPU keeps running in the full machine (it may set its own flags, its `unmodelled`
guard, etc.); nothing here constrains that. Only the CPU-visible state is related.
-/
namespace Smb

/-! ### ByteArray lemmas -/

theorem ByteArray.size_set! (a : ByteArray) (i : Nat) (b : UInt8) : (a.set! i b).size = a.size := by
  cases a; simp [ByteArray.set!, ByteArray.size]

theorem ByteArray.get!_set!_self (a : ByteArray) (i : Nat) (b : UInt8) (h : i < a.size) :
    (a.set! i b).get! i = b := by
  cases a with | mk d =>
  simp only [ByteArray.set!, ByteArray.get!]
  exact Array.getElem!_set!_self d i b h

theorem ByteArray.get!_set!_ne (a : ByteArray) (i j : Nat) (b : UInt8) (h : i ≠ j) :
    (a.set! i b).get! j = a.get! j := by
  cases a with | mk d =>
  simp only [ByteArray.set!, ByteArray.get!]
  exact Array.getElem!_set!_ne d i j b h

/-! ### PPU activity leaves the CPU-visible state alone -/

/-- What the refinement relates or relies on. -/
structure Core where
  pc : UInt16
  a : UInt8
  x : UInt8
  y : UInt8
  s : UInt8
  p : UInt8
  ram : ByteArray
  prg : ByteArray
  ctrl : UInt8
  dmaPending : Bool
  nmiPending : Bool
  nmiPolled : Bool
  cyc : UInt64

def core (n : NES) : Core :=
  ⟨n.pc, n.a, n.x, n.y, n.s, n.p, n.ram, n.prg, n.ctrl, n.dmaPending, n.nmiPending, n.nmiPolled, n.cyc⟩

namespace NES

theorem core_sched_go (n : Nat) (s : NES) : core (sched.go n s) = core s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [sched.go]
    split
    · rfl
    · split
      · rfl
      · rw [ih]; rfl

theorem core_sched (s : NES) : core (sched s) = core s := by
  simp only [sched]
  have := core_sched_go 9 s
  simp only [core] at this ⊢
  exact this

theorem core_fetchSprite0 (s : NES) : core (fetchSprite0 s) = core s := by
  unfold fetchSprite0; dsimp only
  repeat' split
  all_goals rfl

theorem fetchSprite0_proj (s : NES) :
    (fetchSprite0 s).pc = s.pc ∧ (fetchSprite0 s).a = s.a ∧ (fetchSprite0 s).x = s.x ∧
    (fetchSprite0 s).y = s.y ∧ (fetchSprite0 s).s = s.s ∧ (fetchSprite0 s).p = s.p ∧
    (fetchSprite0 s).ram = s.ram ∧ (fetchSprite0 s).prg = s.prg ∧ (fetchSprite0 s).ctrl = s.ctrl ∧
    (fetchSprite0 s).dmaPending = s.dmaPending ∧ (fetchSprite0 s).nmiPending = s.nmiPending ∧
    (fetchSprite0 s).nmiPolled = s.nmiPolled ∧ (fetchSprite0 s).cyc = s.cyc := by
  have := core_fetchSprite0 s
  simp only [core, Core.mk.injEq] at this
  exact this

theorem core_handleEv (s : NES) : core (handleEv s) = core s := by
  unfold handleEv; dsimp only
  repeat' split
  all_goals (try rw [core_sched])
  all_goals simp only [core, fetchSprite0_proj]

theorem core_ppuEvents_go (n : Nat) (s : NES) : core (ppuEvents.go n s) = core s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [ppuEvents.go]
    split
    · rw [ih, core_handleEv]
    · rfl

theorem core_advancePpu (s : NES) (d : UInt32) : core (advancePpu s d) = core s := by
  simp only [advancePpu, ppuEvents]
  split
  · rw [core_ppuEvents_go]; rfl
  · rfl

theorem core_beginCycle (s : NES) : core (beginCycle s) = core { s with cyc := s.cyc + 1 } := by
  unfold beginCycle; dsimp only
  split <;> rw [core_advancePpu] <;> rfl

/-- With NMI generation off and no NMI pending, a cycle end polls "no NMI". -/
theorem core_endCycle (s : NES) (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    core (endCycle s) = core { s with nmiPolled := false } := by
  unfold endCycle; dsimp only
  rw [core_advancePpu]
  have h1 := core_advancePpu s 1
  simp only [core, Core.mk.injEq] at h1 ⊢
  simp [h1, hp, hc]

theorem not_le_of_lt_2000 {a : UInt16} (h : a < 0x2000) : ¬ (0x2000 ≤ a) := by bv_decide
theorem lt_of_ge_8000 {a : UInt16} (h : 0x8000 ≤ a) :
    ¬ (a < 0x2000) ∧ ¬ (a < 0x4000) ∧ a ≠ 0x4016 ∧ a ≠ 0x4017 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem readCycle_ram (s : NES) (a : UInt16) (ha : a < 0x2000)
    (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    (readCycle s a).1 = s.ram.get! (a &&& 0x7FF).toNat ∧
    core (readCycle s a).2 = core { s with cyc := s.cyc + 1, nmiPolled := false } := by
  have hb := core_beginCycle s
  simp only [core, Core.mk.injEq] at hb
  unfold readCycle; dsimp only
  simp only [ha, ↓reduceIte, not_le_of_lt_2000 ha, decide_false, Bool.false_and, Bool.false_eq_true]
  refine ⟨by simp [hb], ?_⟩
  rw [core_endCycle _ (by simp [hb, hp]) (by simp [hb, hc])]
  simp [core, hb]

theorem readCycle_rom (s : NES) (a : UInt16) (ha : 0x8000 ≤ a)
    (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    (readCycle s a).1 = s.prgAt a ∧
    core (readCycle s a).2 = core { s with cyc := s.cyc + 1, nmiPolled := false } := by
  have hb := core_beginCycle s
  simp only [core, Core.mk.injEq] at hb
  obtain ⟨h1, h2, h3, h4⟩ := lt_of_ge_8000 ha
  unfold readCycle; dsimp only
  simp only [h1, h2, h3, h4, ha, ↓reduceIte, decide_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, beq_iff_eq]
  split
  · exfalso; bv_decide
  refine ⟨by simp [prgAt, hb], ?_⟩
  rw [core_endCycle _ (by simp [hb, hp]) (by simp [hb, hc])]
  simp [core, hb]

theorem wrS_ram (s : NES) (a : UInt16) (b : UInt8) (ha : a < 0x2000)
    (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    core (wrS s a b) =
      core { s with ram := s.ram.set! (a &&& 0x7FF).toNat b, cyc := s.cyc + 1, nmiPolled := false } := by
  have hb := core_beginCycle s
  simp only [core, Core.mk.injEq] at hb
  unfold wrS; dsimp only
  simp only [ha, ↓reduceIte]
  rw [core_endCycle _ (by simp [setRam, hb, hp]) (by simp [setRam, hb, hc])]
  simp [core, setRam, hb]

theorem tickS_core (s : NES) (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    core (tickS s) = core { s with cyc := s.cyc + 1, nmiPolled := false } := by
  have hb := core_beginCycle s
  simp only [core, Core.mk.injEq] at hb
  unfold tickS
  rw [core_endCycle _ (by simp [hb, hp]) (by simp [hb, hc])]
  simp [core, hb]

end NES

/-! ### The relation and the simulation judgement -/

structure Rel (s : NES) (t : Plain) : Prop where
  regs : (⟨s.pc, s.a, s.x, s.y, s.s, s.p⟩ : Regs) = t.regs
  ram : ∀ i : UInt16, s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF)
  size : s.ram.size = 0x800
  prg : ∀ a : UInt16, s.prg.get! (a &&& 0x7FFF).toNat = t.prg (a &&& 0x7FFF)
  cyc : s.cyc = t.cyc
  ctrl : s.ctrl &&& 0x80 = 0
  nmiPending : s.nmiPending = false
  nmiPolled : s.nmiPolled = false
  dma : s.dmaPending = false

/-- After one bus cycle that left RAM unchanged. -/
theorem Rel.tick {s s' : NES} {t : Plain} (hr : Rel s t)
    (hc : core s' = core { s with cyc := s.cyc + 1, nmiPolled := false }) :
    Rel s' { t with cyc := t.cyc + 1 } := by
  simp only [core, Core.mk.injEq] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
  exact { regs := by rw [h1, h2, h3, h4, h5, h6]; exact hr.regs
          ram := by rw [h7]; exact hr.ram
          size := by rw [h7]; exact hr.size
          prg := by rw [h8]; exact hr.prg
          cyc := by rw [h13, hr.cyc]
          ctrl := by rw [h9]; exact hr.ctrl
          nmiPending := by rw [h11]; exact hr.nmiPending
          nmiPolled := h12
          dma := by rw [h10]; exact hr.dma }

/-- `Rel` ignores the plain machine's `bad` flag. -/
theorem Rel.with_bad {s : NES} {t : Plain} (hr : Rel s t) (b : Bool) : Rel s { t with bad := b } :=
  { regs := hr.regs, ram := hr.ram, size := hr.size, prg := hr.prg, cyc := hr.cyc, ctrl := hr.ctrl
    nmiPending := hr.nmiPending, nmiPolled := hr.nmiPolled, dma := hr.dma }

theorem and_7ff_lt (a : UInt16) : (a &&& 0x7FF).toNat < 0x800 := by
  have : (a &&& 0x7FF) < 0x800 := by bv_decide
  exact this

/-- After one bus cycle that wrote `b` at RAM address `a`. -/
theorem Rel.write {s s' : NES} {t : Plain} (hr : Rel s t) (a : UInt16) (b : UInt8)
    (hin : Plain.inRam a = true)
    (hc : core s' = core { s with ram := s.ram.set! (a &&& 0x7FF).toNat b, cyc := s.cyc + 1,
                                   nmiPolled := false }) :
    Rel s' { t with cyc := t.cyc + 1,
                    ram := fun i => bif Plain.inRam a && i == a &&& 0x7FF then b else t.ram i } := by
  simp only [core, Core.mk.injEq] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
  exact { regs := by rw [h1, h2, h3, h4, h5, h6]; exact hr.regs
          ram := by
            intro i
            rw [h7]
            dsimp only
            simp only [hin, Bool.true_and]
            by_cases he : i &&& 0x7FF = a &&& 0x7FF
            · simp only [he, beq_self_eq_true, cond_true]
              exact ByteArray.get!_set!_self _ _ _ (by rw [hr.size]; exact and_7ff_lt a)
            · have : ((i &&& 0x7FF) == (a &&& 0x7FF)) = false := by simpa using he
              simp only [this, cond_false]
              rw [ByteArray.get!_set!_ne _ _ _ _ (fun h => he (UInt16.toNat_inj.mp h).symm)]
              exact hr.ram i
          size := by rw [h7, ByteArray.size_set!]; exact hr.size
          prg := by rw [h8]; exact hr.prg
          cyc := by rw [h13, hr.cyc]
          ctrl := by rw [h9]; exact hr.ctrl
          nmiPending := by rw [h11]; exact hr.nmiPending
          nmiPolled := h12
          dma := by rw [h10]; exact hr.dma }

/-- `m₁` on the full NES simulates `m₂` on the plain machine: whenever the plain run does
not go `bad`, both return the same value and end related. `bad` is also sticky. -/
def Sim {α : Type} (m₁ : StateM NES α) (m₂ : StateM Plain α) : Prop :=
  (∀ t, (m₂.run t).2.bad = false → t.bad = false) ∧
  ∀ s t, Rel s t → (m₂.run t).2.bad = false →
    (m₁.run s).1 = (m₂.run t).1 ∧ Rel (m₁.run s).2 (m₂.run t).2

namespace Sim

theorem run_bind {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

theorem pure {α : Type} (a : α) : Sim (Pure.pure a) (Pure.pure a) :=
  ⟨fun _ h => h, fun _ _ hr _ => ⟨rfl, hr⟩⟩

theorem bind {α β : Type} {m₁ : StateM NES α} {m₂ : StateM Plain α}
    {f₁ : α → StateM NES β} {f₂ : α → StateM Plain β}
    (hm : Sim m₁ m₂) (hf : ∀ a, Sim (f₁ a) (f₂ a)) : Sim (m₁ >>= f₁) (m₂ >>= f₂) := by
  refine ⟨fun t h => ?_, fun s t hr h => ?_⟩
  · rw [run_bind] at h
    exact hm.1 t ((hf _).1 _ h)
  · rw [run_bind] at h ⊢
    rw [run_bind]
    obtain ⟨hv, hr'⟩ := hm.2 s t hr ((hf _).1 _ h)
    rw [hv]
    exact (hf _).2 _ _ hr' h

/-- Bind on an operation whose plain result is always `v`. -/
theorem bind' {α β : Type} {m₁ : StateM NES α} {m₂ : StateM Plain α}
    {f₁ : α → StateM NES β} {f₂ : α → StateM Plain β} {v : α}
    (hm : Sim m₁ m₂) (hv : ∀ t, (m₂.run t).1 = v) (hf : Sim (f₁ v) (f₂ v)) :
    Sim (m₁ >>= f₁) (m₂ >>= f₂) := by
  refine ⟨fun t h => ?_, fun s t hr h => ?_⟩
  · rw [run_bind, hv] at h
    exact hm.1 t (hf.1 _ h)
  · rw [run_bind, hv] at h
    rw [run_bind, run_bind]
    obtain ⟨hv', hr'⟩ := hm.2 s t hr (hf.1 _ h)
    rw [hv', hv]
    exact hf.2 _ _ hr' h

theorem ite {α : Type} {c : Prop} [Decidable c] {a₁ b₁ : StateM NES α} {a₂ b₂ : StateM Plain α}
    (ha : c → Sim a₁ a₂) (hb : ¬c → Sim b₁ b₂) : Sim (if c then a₁ else b₁) (if c then a₂ else b₂) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

open CPU

theorem getRegs : Sim (getRegs (σ := NES)) (getRegs (σ := Plain)) :=
  ⟨fun _ h => h, fun _ _ hr _ => ⟨hr.regs, hr⟩⟩

theorem modRegs (f : Regs → Regs) : Sim (modRegs (σ := NES) f) (modRegs (σ := Plain) f) := by
  refine ⟨fun _ h => h, fun s t hr _ => ⟨rfl, ?_⟩⟩
  have hregs := hr.regs
  exact { regs := by
            show (⟨_, _, _, _, _, _⟩ : Regs) = f t.regs
            rw [← hregs]
            rfl
          ram := hr.ram, size := hr.size, prg := hr.prg, cyc := hr.cyc, ctrl := hr.ctrl
          nmiPending := hr.nmiPending, nmiPolled := hr.nmiPolled, dma := hr.dma }

theorem rd (a : UInt16) : Sim (rd (σ := NES) a) (rd (σ := Plain) a) := by
  refine ⟨fun t h => ?_, fun s t hr h => ?_⟩
  · change (t.bad || !Plain.readable a) = false at h
    simp only [Bool.or_eq_false_iff] at h
    exact h.1
  · change (NES.rdS s a).1 = (Plain.read t a).1 ∧ Rel (NES.rdS s a).2 (Plain.read t a).2
    change (t.bad || !Plain.readable a) = false at h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Plain.readable, Bool.or_eq_true,
      decide_eq_true_eq] at h
    simp only [NES.rdS, hr.dma, Bool.false_eq_true, ↓reduceIte]
    by_cases ha : a < 0x2000
    · obtain ⟨hv, hc⟩ := NES.readCycle_ram s a ha hr.nmiPending hr.ctrl
      refine ⟨?_, (hr.tick hc).with_bad _⟩
      simp only [Plain.read, Plain.memRead, Plain.inRam, ha, decide_true, cond_true, hv]
      exact hr.ram a
    · have hb : 0x8000 ≤ a := h.2.resolve_left ha
      obtain ⟨hv, hc⟩ := NES.readCycle_rom s a hb hr.nmiPending hr.ctrl
      refine ⟨?_, (hr.tick hc).with_bad _⟩
      simp only [Plain.read, Plain.memRead, Plain.inRam, ha, decide_false, cond_false, hv]
      exact hr.prg a

theorem wr (a : UInt16) (b : UInt8) : Sim (wr (σ := NES) a b) (wr (σ := Plain) a b) := by
  refine ⟨fun t h => ?_, fun s t hr h => ?_⟩
  · change (t.bad || !Plain.inRam a) = false at h
    simp only [Bool.or_eq_false_iff] at h
    exact h.1
  · change () = () ∧ Rel (NES.wrS s a b) (Plain.write t a b)
    change (t.bad || !Plain.inRam a) = false at h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    have ha : a < 0x2000 := by simpa [Plain.inRam] using h.2
    exact ⟨rfl, (hr.write a b h.2 (NES.wrS_ram s a b ha hr.nmiPending hr.ctrl)).with_bad _⟩

theorem idle : Sim (idle (σ := NES)) (idle (σ := Plain)) := by
  refine ⟨fun _ h => h, fun s t hr _ => ⟨rfl, ?_⟩⟩
  exact hr.tick (NES.tickS_core s hr.nmiPending hr.ctrl)

theorem unsupported : Sim (unsupported (σ := NES)) (unsupported (σ := Plain)) := by
  refine ⟨fun _ h => ?_, fun _ _ _ h => ?_⟩ <;> (change true = false at h; exact absurd h (by decide))

theorem nmiPending : Sim (nmiPending (σ := NES)) (nmiPending (σ := Plain)) :=
  ⟨fun _ h => h, fun _ _ hr _ => ⟨hr.nmiPending, hr⟩⟩

theorem nmiPolled : Sim (nmiPolled (σ := NES)) (nmiPolled (σ := Plain)) :=
  ⟨fun _ h => h, fun _ _ hr _ => ⟨hr.nmiPolled, hr⟩⟩

theorem clearNmiPending : Sim (clearNmiPending (σ := NES)) (clearNmiPending (σ := Plain)) := by
  refine ⟨fun _ h => h, fun s t hr _ => ⟨rfl, ?_⟩⟩
  exact { regs := hr.regs, ram := hr.ram, size := hr.size, prg := hr.prg, cyc := hr.cyc
          ctrl := hr.ctrl, nmiPending := rfl, nmiPolled := hr.nmiPolled, dma := hr.dma }

theorem setNmiPolled (b : Bool) (hb : b = false) :
    Sim (setNmiPolled (σ := NES) b) (setNmiPolled (σ := Plain) b) := by
  subst hb
  refine ⟨fun _ h => h, fun s t hr _ => ⟨rfl, ?_⟩⟩
  exact { regs := hr.regs, ram := hr.ram, size := hr.size, prg := hr.prg, cyc := hr.cyc
          ctrl := hr.ctrl, nmiPending := hr.nmiPending, nmiPolled := rfl, dma := hr.dma }

theorem bind_nmiPolled {β : Type} {f₁ : Bool → StateM NES β} {f₂ : Bool → StateM Plain β}
    (hf : Sim (f₁ false) (f₂ false)) : Sim (CPU.nmiPolled >>= f₁) (CPU.nmiPolled >>= f₂) :=
  bind' nmiPolled (fun _ => rfl) hf

theorem bind_nmiPending {β : Type} {f₁ : Bool → StateM NES β} {f₂ : Bool → StateM Plain β}
    (hf : Sim (f₁ false) (f₂ false)) : Sim (CPU.nmiPending >>= f₁) (CPU.nmiPending >>= f₂) :=
  bind' nmiPending (fun _ => rfl) hf

theorem setNmiPolled_false : Sim (CPU.setNmiPolled (σ := NES) false) (CPU.setNmiPolled (σ := Plain) false) :=
  setNmiPolled false rfl

/-- The CPU definitions above the bus primitives. -/
syntax "sim_unfold" : tactic
macro_rules
  | `(tactic| sim_unfold) => `(tactic|
      simp (config := {decide := true}) only [CPU.exec, CPU.setNZ, CPU.flag, CPU.setA, CPU.setX,
        CPU.setY, CPU.fetch, CPU.fetch16, CPU.dummyPc, CPU.dummyStack, CPU.dummyRdIf, CPU.push, CPU.pull, CPU.aZp,
        CPU.aZpX, CPU.aZpY, CPU.aAbs, CPU.aAbsI, CPU.aAbsX, CPU.aAbsY, CPU.aIndX, CPU.aIndY, CPU.adc,
        CPU.cmp, CPU.branch, CPU.shiftOp, CPU.rmw, CPU.interrupt, CPU.nmi, CPU.ld, CPU.st,
        CPU.aluOperand, CPU.isAlu, CPU.alu, ↓reduceIte])

/-- Match both programs step by step with the simulation lemmas. Lemmas are applied at
reducible transparency, so a mismatch fails without unfolding the state monad. -/
syntax "sim_tac" : tactic
macro_rules
  | `(tactic| sim_tac) => `(tactic| (
      sim_unfold
      repeat' (first
        | with_reducible exact Sim.getRegs | with_reducible exact Sim.modRegs _
        | with_reducible exact Sim.rd _ | with_reducible exact Sim.wr _ _
        | with_reducible exact Sim.idle | with_reducible exact Sim.unsupported
        | with_reducible exact Sim.clearNmiPending | with_reducible exact Sim.pure _
        | with_reducible exact Sim.setNmiPolled_false
        | with_reducible refine Sim.bind_nmiPolled ?_
        | with_reducible refine Sim.bind_nmiPending ?_
        | with_reducible refine Sim.bind ?_ (fun _ => ?_)
        | with_reducible refine Sim.ite (fun _ => ?_) (fun _ => ?_)
        | split
        | dsimp only
        | simp only [Bool.or_self, Bool.false_or, Bool.or_false])))

end Sim
end Smb
