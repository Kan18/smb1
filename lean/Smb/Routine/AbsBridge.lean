import Smb.Routine.AbsIO

/-!
# Between frames

The checker's invariant, carried over the instructions that run with NMI generation on: the handler's closing `sta $2000` and
`rti`, the idle loop, an NMI, and the handler's first instructions. These instructions touch only RAM and ROM, so the NES does what
the plain machine does, except that the NMI latches move. `ginv_step` closes the invariant over frames.
-/
set_option maxRecDepth 20000
namespace Smb

/-- A full NES state whose CPU view is a plain state, with NMI generation free. -/
structure RelOn (s : NES) (t : Plain) : Prop where
  regs : (⟨s.pc, s.a, s.x, s.y, s.s, s.p⟩ : Regs) = t.regs
  ram : ∀ i : UInt16, s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF)
  size : s.ram.size = 0x800
  prg : ∀ a : UInt16, s.prg.get! (a &&& 0x7FFF).toNat = t.prg (a &&& 0x7FFF)
  dma : s.dmaPending = false

namespace RelOn

/-- A core-level change of only the cycle and the NMI latches and `ctrl`. -/
theorem of_core {s s' : NES} {t : Plain} (h : RelOn s t) {k y pol pen}
    (hc : core s' = core { s with ctrl := k, cyc := y, nmiPolled := pol, nmiPending := pen }) : RelOn s' t := by
  simp only [core, Core.mk.injEq] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
  exact { regs := by rw [h1, h2, h3, h4, h5, h6]; exact h.regs
          ram := by rw [h7]; exact h.ram
          size := by rw [h7]; exact h.size
          prg := by rw [h8]; exact h.prg
          dma := by rw [h10]; exact h.dma }

theorem cyc {s : NES} {t : Plain} (h : RelOn s t) (c : UInt64) : RelOn s { t with cyc := c } :=
  ⟨h.regs, h.ram, h.size, h.prg, h.dma⟩

theorem with_bad {s : NES} {t : Plain} (h : RelOn s t) (b : Bool) : RelOn s { t with bad := b } :=
  ⟨h.regs, h.ram, h.size, h.prg, h.dma⟩

theorem read {s : NES} {t : Plain} (h : RelOn s t) (a : UInt16) : RelOn (NES.rdS s a).2 t := by
  simp only [NES.rdS, h.dma, Bool.false_eq_true, if_false]
  obtain ⟨pol, pen, hc⟩ := NES.core_readCycle_any s a
  exact h.of_core (k := s.ctrl) hc

theorem read_val {s : NES} {t : Plain} (h : RelOn s t) (a : UInt16) (ha : Plain.readable a = true) :
    (NES.rdS s a).1 = Plain.memRead t.ram t.prg a := by
  simp only [NES.rdS, h.dma, Bool.false_eq_true, if_false]
  by_cases hl : a < 0x2000
  · rw [NES.readCycle_ram' s a hl]
    simp only [Plain.memRead, Plain.inRam, hl, decide_true, cond_true]
    exact h.ram a
  · have hb : 0x8000 ≤ a := by simpa [Plain.readable, hl] using ha
    rw [NES.readCycle_rom' s a hb]
    simp only [Plain.memRead, Plain.inRam, hl, decide_false, cond_false]
    exact h.prg a

end RelOn

/-- `m₁` on the NES with NMI generation free does what `m₂` does on the plain machine, as long as it does not go `bad`. -/
def SimO {α : Type} (m₁ : StateM NES α) (m₂ : StateM Plain α) : Prop :=
  (∀ t, (m₂.run t).2.bad = false → t.bad = false) ∧
  ∀ s t, RelOn s t → (m₂.run t).2.bad = false →
    (m₁.run s).1 = (m₂.run t).1 ∧ RelOn (m₁.run s).2 (m₂.run t).2

namespace SimO
open CPU

theorem pure {α : Type} (a : α) : SimO (Pure.pure a) (Pure.pure a) :=
  ⟨fun _ h => h, fun _ _ hr _ => ⟨rfl, hr⟩⟩

theorem bind {α β : Type} {m₁ : StateM NES α} {m₂ : StateM Plain α}
    {f₁ : α → StateM NES β} {f₂ : α → StateM Plain β}
    (hm : SimO m₁ m₂) (hf : ∀ a, SimO (f₁ a) (f₂ a)) : SimO (m₁ >>= f₁) (m₂ >>= f₂) := by
  refine ⟨fun t h => ?_, fun s t hr h => ?_⟩
  · rw [Sim.run_bind] at h
    exact hm.1 t ((hf _).1 _ h)
  · rw [Sim.run_bind] at h ⊢
    rw [Sim.run_bind]
    obtain ⟨hv, hr'⟩ := hm.2 s t hr ((hf _).1 _ h)
    rw [hv]
    exact (hf _).2 _ _ hr' h

theorem ite {α : Type} {c : Prop} [Decidable c] {a₁ b₁ : StateM NES α} {a₂ b₂ : StateM Plain α}
    (ha : c → SimO a₁ a₂) (hb : ¬c → SimO b₁ b₂) : SimO (if c then a₁ else b₁) (if c then a₂ else b₂) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

theorem getRegs : SimO (getRegs (σ := NES)) (getRegs (σ := Plain)) :=
  ⟨fun _ h => h, fun _ _ hr _ => ⟨hr.regs, hr⟩⟩

theorem modRegs (f : Regs → Regs) : SimO (modRegs (σ := NES) f) (modRegs (σ := Plain) f) := by
  refine ⟨fun _ h => h, fun s t hr _ => ⟨rfl, ?_⟩⟩
  have hregs := hr.regs
  exact { regs := by
            show (⟨_, _, _, _, _, _⟩ : Regs) = f t.regs
            rw [← hregs]
            rfl
          ram := hr.ram, size := hr.size, prg := hr.prg, dma := hr.dma }

theorem rd (a : UInt16) : SimO (rd (σ := NES) a) (rd (σ := Plain) a) := by
  refine ⟨fun t h => ?_, fun s t hr h => ?_⟩
  · change (t.bad || !Plain.readable a) = false at h
    simp only [Bool.or_eq_false_iff] at h
    exact h.1
  · change (NES.rdS s a).1 = (Plain.read t a).1 ∧ RelOn (NES.rdS s a).2 (Plain.read t a).2
    change (t.bad || !Plain.readable a) = false at h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    exact ⟨hr.read_val a h.2, ⟨(hr.read a).regs, (hr.read a).ram, (hr.read a).size, (hr.read a).prg, (hr.read a).dma⟩⟩

theorem wr (a : UInt16) (b : UInt8) : SimO (wr (σ := NES) a b) (wr (σ := Plain) a b) := by
  refine ⟨fun t h => ?_, fun s t hr h => ?_⟩
  · change (t.bad || !Plain.inRam a) = false at h
    simp only [Bool.or_eq_false_iff] at h
    exact h.1
  · change () = () ∧ RelOn (NES.wrS s a b) (Plain.write t a b)
    change (t.bad || !Plain.inRam a) = false at h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    have ha : a < 0x2000 := by simpa [Plain.inRam] using h.2
    obtain ⟨pol, pen, hc⟩ := NES.core_wrS_ram_any s a b ha
    simp only [core, Core.mk.injEq] at hc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
    refine ⟨rfl, ?_⟩
    exact { regs := by rw [h1, h2, h3, h4, h5, h6]; exact hr.regs
            ram := by
              intro i
              rw [h7]
              show _ = (bif Plain.inRam a && (i &&& 0x7FF) == a &&& 0x7FF then b else t.ram (i &&& 0x7FF))
              simp only [h.2, Bool.true_and]
              by_cases he : i &&& 0x7FF = a &&& 0x7FF
              · simp only [he, beq_self_eq_true, cond_true]
                exact ByteArray.get!_set!_self _ _ _ (by rw [hr.size]; exact and_7ff_lt a)
              · have : ((i &&& 0x7FF) == (a &&& 0x7FF)) = false := by simpa using he
                simp only [this, cond_false]
                rw [ByteArray.get!_set!_ne _ _ _ _ (fun h => he (UInt16.toNat_inj.mp h).symm)]
                exact hr.ram i
            size := by rw [h7, ByteArray.size_set!]; exact hr.size
            prg := by rw [h8]; exact hr.prg
            dma := by rw [h10]; exact hr.dma }

theorem clearNmiPending : SimO (clearNmiPending (σ := NES)) (clearNmiPending (σ := Plain)) := by
  refine ⟨fun _ h => h, fun s t hr _ => ⟨rfl, ?_⟩⟩
  exact ⟨hr.regs, hr.ram, hr.size, hr.prg, hr.dma⟩

/-- What the plain program does not ask: an NMI being pending only re-selects the same vector. -/
theorem bind_pending {β : Type} {f₁ : Bool → StateM NES β} {f₂ : Bool → StateM Plain β} {g₁ : StateM NES β} {g₂ : StateM Plain β}
    (h1 : ∀ b, f₁ b = g₁) (h2 : ∀ b, f₂ b = g₂) (hg : SimO g₁ g₂) : SimO (CPU.nmiPending >>= f₁) (CPU.nmiPending >>= f₂) := by
  refine ⟨fun t h => ?_, fun s t hr h => ?_⟩
  · rw [Sim.run_bind, h2] at h
    exact hg.1 _ h
  · rw [Sim.run_bind, h2] at h
    have e1 : (CPU.nmiPending >>= f₁).run s = g₁.run s := by rw [Sim.run_bind, h1]; rfl
    have e2 : (CPU.nmiPending >>= f₂).run t = g₂.run t := by rw [Sim.run_bind, h2]; rfl
    rw [e1, e2]
    exact hg.2 _ _ hr h

syntax "simo_tac" : tactic
macro_rules
  | `(tactic| simo_tac) => `(tactic| (
      sim_unfold
      repeat' (first
        | with_reducible exact SimO.getRegs | with_reducible exact SimO.modRegs _
        | with_reducible exact SimO.rd _ | with_reducible exact SimO.wr _ _
        | with_reducible exact SimO.clearNmiPending | with_reducible exact SimO.pure _
        | with_reducible refine SimO.bind_pending (fun _ => rfl) (fun _ => rfl) ?_
        | with_reducible refine SimO.bind ?_ (fun _ => ?_)
        | with_reducible refine SimO.ite (fun _ => ?_) (fun _ => ?_)
        | split
        | dsimp only
        | simp only [Bool.or_self, Bool.false_or, Bool.or_false])))

theorem fetch : SimO (CPU.fetch (σ := NES)) (CPU.fetch (σ := Plain)) := by simo_tac
theorem exec40 : SimO (CPU.exec (σ := NES) 0x40) (CPU.exec (σ := Plain) 0x40) := by simo_tac
theorem exec4c : SimO (CPU.exec (σ := NES) 0x4C) (CPU.exec (σ := Plain) 0x4C) := by simo_tac
theorem execad : SimO (CPU.exec (σ := NES) 0xAD) (CPU.exec (σ := Plain) 0xAD) := by simo_tac
theorem exec29 : SimO (CPU.exec (σ := NES) 0x29) (CPU.exec (σ := Plain) 0x29) := by simo_tac
theorem exec8d : SimO (CPU.exec (σ := NES) 0x8D) (CPU.exec (σ := Plain) 0x8D) := by simo_tac

theorem fetch16 : SimO (CPU.fetch16 (σ := NES)) (CPU.fetch16 (σ := Plain)) := by simo_tac

theorem nmi : SimO (CPU.nmi (σ := NES)) (CPU.nmi (σ := Plain)) := by
  simp only [CPU.nmi, CPU.interrupt, ite_self]
  simo_tac

end SimO

open Abs in
/-- An NMI on the plain machine. -/
theorem plain_nmi {rom : UInt16 → UInt8} (t : Plain) (hc : Code rom t) (h0 : 0x8000 ≤ t.regs.pc) (hb : t.bad = false) :
    StepOk t (CPU.nmi.run t).2 (nmiEff rom t.regs) := by
  have hv0 : t.prg (0xFFFA &&& 0x7FFF) = rom 0xFFFA := hc _ (by decide)
  have hv1 : t.prg (0xFFFB &&& 0x7FFF) = rom 0xFFFB := hc _ (by decide)
  obtain ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩ := t
  simp only at h0 hb hv0 hv1
  subst hb
  have hpc : Plain.readable pc = true := by simp [Plain.readable, h0]
  have hst : ∀ v : UInt8, Plain.inRam (0x100 ||| v.toUInt16) = true := by
    intro v; simp only [Plain.inRam, decide_eq_true_eq]; bv_decide (config := { enums := false })
  have hr0 : Plain.readable (0xFFFA : UInt16) = true := by decide
  have hr1 : Plain.readable (0xFFFB : UInt16) = true := by decide
  have e2 : sp - 1 - 1 = sp - 2 := by bv_decide (config := { enums := false })
  have e3 : sp - 2 - 1 = sp - 3 := by bv_decide (config := { enums := false })
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp only [nmiEff]
    rw [← hv0, ← hv1]
    show Regs.mk _ a x y (sp - 1 - 1 - 1) (p ||| CPU.FI) = _
    rw [e2, e3]
    rfl
  · funext i
    show (bif Plain.inRam (0x100 ||| (sp - 1 - 1).toUInt16) && i == (0x100 ||| (sp - 1 - 1).toUInt16) &&& 0x7FF then _ else
      (bif Plain.inRam (0x100 ||| (sp - 1).toUInt16) && i == (0x100 ||| (sp - 1).toUInt16) &&& 0x7FF then _ else
      (bif Plain.inRam (0x100 ||| sp.toUInt16) && i == (0x100 ||| sp.toUInt16) &&& 0x7FF then _ else ram i))) = _
    simp only [hst, Bool.true_and, nmiEff, applyW, stack, e2]
    simp
    rfl
  · show (false || !Plain.readable pc || !Plain.readable pc || !Plain.inRam (0x100 ||| sp.toUInt16) ||
      !Plain.inRam (0x100 ||| (sp - 1).toUInt16) || !Plain.inRam (0x100 ||| (sp - 1 - 1).toUInt16) ||
      !Plain.readable 0xFFFA || !Plain.readable 0xFFFB) = false
    simp only [hpc, hst, hr0, hr1, Bool.not_true, Bool.or_self]

namespace Abs
open CPU

/-- A state in the table, with NMI generation off or, at the addresses that run with it on, free. -/
def GInv (rom : UInt16 → UInt8) (prot : UInt16 → Bool) (g : Global) (ram0 : UInt16 → UInt8) (T : Table) (s : NES) : Prop :=
  ∃ t, Code rom t ∧ Inv prot g ram0 T t ∧ (RelD s t ∨ (onPC t.regs.pc = true ∧ RelOn s t))

/-- A state after an instruction's own cycles, before `stepTail` looks at the NMI poll. -/
def preChecks (s : NES) : NES := ((CPU.exec (CPU.fetch.run s).1).run (CPU.fetch.run s).2).2

theorem step_eq (s : NES) : (CPU.step.run s).2 = (checks.run (preChecks s)).2 := rfl

/-- No NMI arrives during the handler's first instructions, and the PPU has left its power-on state, so `sta $2000` takes effect. -/
def Guard (s : NES) : Prop :=
  preamblePC s.pc = true → (preChecks s).nmiPolled = false ∧ (preChecks s).nmiPending = false ∧
    (s.pc = onExit → (preChecks s).ctrl = s.a)

theorem check_box {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {b : Box} {pc : UInt16}
    (hchk : checkF rom exit prot g T = true) (hb : b ∈ T.at pc) : boxF rom exit prot g T b = true := by
  simp only [checkF, List.all_eq_true, List.mem_range] at hchk
  have := hchk _ (table_at_lt pc) b hb
  simp only [Bool.and_eq_true] at this
  exact this.2

theorem checks_nes_id {s : NES} (hi : s.p &&& 4 ≠ 0) (hn : s.nmiPolled = false) : (checks.run s).2 = s := by
  have : (s.p &&& FI == 0) = false := by simpa [FI] using hi
  simp [checks, bind, StateT.bind, getRegs, nmiPolled, Bus.nmiPolled, Bus.regs, hn, this, pure, StateT.pure, StateT.run]

theorem checks_nes_nmi {s : NES} (hi : s.p &&& 4 ≠ 0) (hn : s.nmiPolled = true) : (checks.run s).2 = (CPU.nmi.run s).2 := by
  have : (s.p &&& FI == 0) = false := by simpa [FI] using hi
  simp [checks, bind, StateT.bind, getRegs, nmiPolled, Bus.nmiPolled, Bus.regs, hn, this, pure, StateT.pure, StateT.run]

theorem checks_plain {x : Plain} (h : (checks.run x).2.bad = false) : (checks.run x).2 = x ∧ x.regs.p &&& 4 ≠ 0 := by
  by_cases hp : x.regs.p &&& FI = 0
  · have : (x.regs.p &&& FI == 0) = true := by simpa using hp
    exfalso
    simp [checks, bind, StateT.bind, getRegs, nmiPolled, Bus.nmiPolled, Bus.regs, this, pure, StateT.pure, StateT.run, unsupported, Bus.unsupported] at h
  · have : (x.regs.p &&& FI == 0) = false := by simpa using hp
    refine ⟨?_, by simpa [FI] using hp⟩
    simp [checks, bind, StateT.bind, getRegs, nmiPolled, Bus.nmiPolled, Bus.regs, this, pure, StateT.pure, StateT.run]

theorem on_exec (op : UInt8) (h : op = 0x40 ∨ op = 0x4C ∨ op = 0xAD ∨ op = 0x29 ∨ op = 0x8D) :
    SimO (CPU.exec (σ := NES) op) (CPU.exec (σ := Plain) op) := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact SimO.exec40
  · exact SimO.exec4c
  · exact SimO.execad
  · exact SimO.exec29
  · exact SimO.exec8d

/-- The plain machine's instruction, before `stepTail`'s checks. -/
def plainExec (t : Plain) : Plain := ((CPU.exec (CPU.fetch.run t).1).run (CPU.fetch.run t).2).2

theorem plain_step_eq (t : Plain) : (CPU.step.run t).2 = (checks.run (plainExec t)).2 := rfl

/-- With NMI generation free, an instruction of these five does what the plain machine does. -/
theorem on_plain {s : NES} {t : Plain} (h : RelOn s t) (h0 : 0x8000 ≤ t.regs.pc)
    (hop : t.prg (t.regs.pc &&& 0x7FFF) = 0x40 ∨ t.prg (t.regs.pc &&& 0x7FFF) = 0x4C ∨ t.prg (t.regs.pc &&& 0x7FFF) = 0xAD ∨
      t.prg (t.regs.pc &&& 0x7FFF) = 0x29 ∨ t.prg (t.regs.pc &&& 0x7FFF) = 0x8D)
    (hb : (CPU.step.run t).2.bad = false) :
    RelOn (preChecks s) (plainExec t) ∧ (CPU.step.run t).2 = plainExec t ∧ (plainExec t).regs.p &&& 4 ≠ 0 := by
  rw [plain_step_eq] at hb ⊢
  obtain ⟨he, hi⟩ := checks_plain hb
  rw [he] at hb
  have hv : (CPU.fetch.run t).1 = t.prg (t.regs.pc &&& 0x7FFF) := by
    show Plain.memRead t.ram t.prg t.regs.pc = _
    have hn : Plain.inRam t.regs.pc = false := by
      simp only [Plain.inRam, decide_eq_false_iff_not]; revert h0; bv_decide (config := { enums := false })
    simp [Plain.memRead, hn]
  have hE := on_exec _ hop
  rw [← hv] at hE
  have hf0 : (CPU.fetch.run t).2.bad = false := hE.1 _ hb
  have hF := SimO.fetch.2 s t h hf0
  have hs : preChecks s = ((CPU.exec (CPU.fetch.run t).1).run (CPU.fetch.run s).2).2 := by
    simp only [preChecks, hF.1]
  refine ⟨?_, he, hi⟩
  rw [hs]
  exact (hE.2 _ _ hF.2 hb).2

theorem fetch_pc (t : Plain) : (CPU.fetch.run t).2.regs.pc = t.regs.pc + 1 := rfl
theorem fetch_val (t : Plain) (h0 : 0x8000 ≤ t.regs.pc) : (CPU.fetch.run t).1 = t.prg (t.regs.pc &&& 0x7FFF) := by
  show Plain.memRead t.ram t.prg t.regs.pc = _
  have hn : Plain.inRam t.regs.pc = false := by
    simp only [Plain.inRam, decide_eq_false_iff_not]; revert h0; bv_decide (config := { enums := false })
  simp [Plain.memRead, hn]

theorem pc_ad (u : Plain) : ((CPU.exec (σ := Plain) 0xAD).run u).2.regs.pc = u.regs.pc + 1 + 1 := rfl
theorem pc_29 (u : Plain) : ((CPU.exec (σ := Plain) 0x29).run u).2.regs.pc = u.regs.pc + 1 := rfl
theorem pc_8d (u : Plain) : ((CPU.exec (σ := Plain) 0x8D).run u).2.regs.pc = u.regs.pc + 1 + 1 := rfl

theorem stack_ne_300 (x : UInt8) : ((0x300 : UInt16) == (stack x &&& 0x7FF)) = false := by
  have hx : x.toUInt16 ≤ 255 := by
    have := x.toNat_lt
    rw [UInt16.le_iff_toNat_le, UInt8.toNat_toUInt16]
    show _ ≤ 255
    omega
  simp only [stack]
  generalize x.toUInt16 = y at *
  bv_decide (config := { enums := false })

theorem stack_ne_340 (x : UInt8) : ((0x340 : UInt16) == (stack x &&& 0x7FF)) = false := by
  have hx : x.toUInt16 ≤ 255 := by
    have := x.toNat_lt
    rw [UInt16.le_iff_toNat_le, UInt8.toNat_toUInt16]
    show _ ≤ 255
    omega
  simp only [stack]
  generalize x.toUInt16 = y at *
  bv_decide (config := { enums := false })

/-- An NMI only pushes onto the stack page, so the assumed cells keep their values. -/
theorem nmi_keeps_assumed {rom : UInt16 → UInt8} (t : Plain) (hc : Code rom t) (h0 : 0x8000 ≤ t.regs.pc) (hb : t.bad = false)
    {i : UInt16} (hi : assumedCell i = true) : (CPU.nmi.run t).2.ram i = t.ram i := by
  obtain ⟨_, _, hram, _⟩ := plain_nmi t hc h0 hb
  have h : i = 0x300 ∨ i = 0x340 := by simpa [assumedCell] using hi
  rw [hram, applyW_lookup]
  rcases h with rfl | rfl
  · simp [nmiEff, wrLookup, stack_ne_300]
  · simp [nmiEff, wrLookup, stack_ne_340]

/-- It leaves everything off the stack page alone. -/
theorem nmi_keeps_high {rom : UInt16 → UInt8} (t : Plain) (hc : Code rom t) (h0 : 0x8000 ≤ t.regs.pc) (hb : t.bad = false)
    {i : UInt16} (hi : 0x200 ≤ i) : (CPU.nmi.run t).2.ram i = t.ram i := by
  obtain ⟨_, _, hram, _⟩ := plain_nmi t hc h0 hb
  rw [hram, applyW_lookup]
  have hne (x : UInt8) : (i == stack x &&& 0x7FF) = false := by
    simp only [stack]
    revert hi
    bv_decide (config := { enums := false })
  simp [nmiEff, wrLookup, hne]

theorem nmi_next {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {t : Plain} {b : Box} (hc : Code rom t) (hb : Holds prot g ram0 b t) (h0 : 0x8000 ≤ t.regs.pc)
    (hbox : nmiBox rom prot g T b = true) :
    Code rom (CPU.nmi.run t).2 ∧ Inv prot g ram0 T (CPU.nmi.run t).2 ∧ onPC (CPU.nmi.run t).2.regs.pc = true := by
  have hrun := plain_nmi t hc h0 hb.bad
  obtain ⟨hregs, hprg, hram, hbad⟩ := hrun
  unfold nmiBox at hbox
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true] at hbox
  obtain ⟨hvec, hall⟩ := hbox
  have hl := hall t.regs.p (VS.mem_elems hb.p)
  obtain ⟨hw, cand, hcm, hcov⟩ := hl
  have hpc : b.pc = t.regs.pc := hb.pc.symm
  have hsp : b.s = t.regs.s := hb.sp.symm
  simp only [hpc, hsp] at hw hcm hcov
  have hwr : (nmiEff rom ⟨t.regs.pc, 0, 0, 0, t.regs.s, t.regs.p⟩).wr = (nmiEff rom t.regs).wr := rfl
  have hE : (CPU.nmi.run t).2.regs.pc = 0x8082 := by rw [hregs]; exact hvec
  refine ⟨fun a' ha' => by rw [hprg]; exact hc a' ha', ⟨cand, ?_, ?_⟩, by rw [hE]; decide⟩
  · rw [hregs]; exact hcm
  · simp only [covers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcov
    obtain ⟨⟨⟨⟨⟨⟨hcpc, hcs⟩, hcp⟩, hca⟩, hcx⟩, hcy⟩, hcc⟩ := hcov
    rw [hwr] at hw hcc
    exact {
      pc := by rw [hregs]; exact hcpc.symm
      sp := by rw [hregs]; exact hcs.symm
      a := by rw [hregs]; exact VS.sub_sound (by simpa [readsA, writesA] using hca) hb.a
      x := by rw [hregs]; exact VS.sub_sound (by simpa [readsX, writesX] using hcx) hb.x
      y := by rw [hregs]; exact VS.sub_sound (by simpa [readsY, writesY] using hcy) hb.y
      p := by rw [hregs]; exact hcp
      i := by
        rw [hregs]
        show (t.regs.p ||| FI) &&& 4 ≠ 0
        simp only [FI]
        bv_decide (config := { enums := false })
      bad := by rw [hbad]; exact hb.bad
      cells := by
        intro c hcin
        rw [hram]
        have hcc' := hcc c hcin
        simp only [cellCoveredR, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, reduceCtorEq, false_and, or_false] at hcc'
        exact cellCovered_sound hb hcc'
      glob := by
        intro i
        rw [hram, applyW_lookup]
        cases hl : wrLookup (nmiEff rom t.regs).wr i with
        | some v =>
          rcases (wrLookup_ok (List.all_eq_true.mpr hw) hl).2 with h1 | h1
          · exact h1
          · have hi : i = 0x300 ∨ i = 0x340 := by simpa [assumedCell] using h1
            rcases hi with rfl | rfl
            · simp [nmiEff, wrLookup, stack_ne_300] at hl
            · simp [nmiEff, wrLookup, stack_ne_340] at hl
        | none => exact hb.glob i
      frame := by
        intro i hpi
        rw [hram, applyW_lookup]
        cases hl : wrLookup (nmiEff rom t.regs).wr i with
        | some v =>
          have := (wrLookup_ok (List.all_eq_true.mpr hw) hl).1
          rw [hpi] at this
          cases this
        | none => exact hb.frame i hpi }

theorem exec8d_eq (u : NES) : ((CPU.exec (σ := NES) 0x8D).run u).2 = NES.wrS (CPU.fetch16.run u).2 (CPU.fetch16.run u).1 (Bus.regs (CPU.fetch16.run u).2).a := rfl

theorem fetch16_plain_val (u : Plain) : (CPU.fetch16.run u).1 = base (CPU.fetch.run u).1 (CPU.fetch.run (CPU.fetch.run u).2).1 := rfl

theorem dec_sta (op : UInt8) (h : decode op = .store .a .abs) : op = 0x8D := by
  have key : ∀ n : Fin 256, decode (UInt8.ofNat n.val) = .store .a .abs → UInt8.ofNat n.val = 0x8D := by decide
  have := key ⟨op.toNat, op.toNat_lt⟩
  simpa using this (by simpa using h)

theorem RelD.to_on {s : NES} {t : Plain} (h : RelD s t) (hd : s.dmaPending = false) : RelOn s t :=
  ⟨h.regs, h.ram, h.size, h.prg, hd⟩

/-- `sta $2000` at the end of the handler: NMI generation may go on; the instruction's last poll still reads false. -/
theorem enter_sound {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} {t : Plain} {b : Box} (h : RelD s t) (hc : Code rom t) (hb : Holds prot g ram0 b t) (hpc : b.pc = onEnter)
    (hbox : enterBox rom g T b = true) :
    GInv rom prot g ram0 T (CPU.step.run s).2 := by
  have htpc : t.regs.pc = 0x817E := hb.pc.trans hpc
  have hsp' : b.s = t.regs.s := hb.sp.symm
  unfold enterBox at hbox
  simp only [hpc, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true, bne_iff_ne, ne_eq] at hbox
  obtain ⟨⟨⟨hk, hbase⟩, hon⟩, hall⟩ := hbox
  have h0 : 0x8000 ≤ t.regs.pc := by rw [htpc]; decide
  have hop : t.prg (t.regs.pc &&& 0x7FFF) = 0x8D := by
    rw [hc _ h0, htpc]; exact dec_sta _ hk
  have hf := h.fetch h0
  rw [step_split, hf.1, hop, tail_8d]
  generalize (CPU.fetch.run s).2 = s1 at hf
  have h1 := hf.2.2
  have hf16 := h1.fetch16 (by dsimp only; rw [htpc]; decide) (by dsimp only; rw [htpc]; decide)
  have hd2 : (CPU.fetch16.run s1).2.dmaPending = false := by
    have hf1 := h1.fetch (by dsimp only; rw [htpc]; decide)
    exact (hf1.2.2.fetch (by dsimp only; rw [htpc]; decide)).2.1
  obtain ⟨hval, h2⟩ := hf16
  have hb1 : t.prg (t.regs.pc + 1 &&& 0x7FFF) = rom (0x817E + 1) := by
    rw [htpc]; exact hc _ (by decide)
  have hb2 : t.prg (t.regs.pc + 1 + 1 &&& 0x7FFF) = rom (0x817E + 2) := by
    rw [htpc]; exact hc _ (by decide)
  have hA : (CPU.fetch16.run s1).1 = 0x2000 := by
    rw [hval]
    show base (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 1 + 1 &&& 0x7FFF)) = _
    rw [hb1, hb2]
    exact hbase
  rw [hA]
  generalize hs2 : (CPU.fetch16.run s1).2 = s2 at h2 hd2
  obtain ⟨c, pen, hcore, -⟩ := NES.core_wrS_2000 s2 (Bus.regs s2).a
  have hon2 : RelOn (NES.wrS s2 0x2000 (Bus.regs s2).a) { t with regs := { { t.regs with pc := t.regs.pc + 1 } with pc := t.regs.pc + 1 + 2 } } :=
    (RelD.to_on h2 hd2).of_core hcore
  have hnp : (NES.wrS s2 0x2000 (Bus.regs s2).a).nmiPolled = false := by
    have := congrArg Core.nmiPolled hcore
    simpa [core, h2.nmiPending] using this
  have hreg : (⟨(NES.wrS s2 0x2000 (Bus.regs s2).a).pc, (NES.wrS s2 0x2000 (Bus.regs s2).a).a, (NES.wrS s2 0x2000 (Bus.regs s2).a).x, (NES.wrS s2 0x2000 (Bus.regs s2).a).y, (NES.wrS s2 0x2000 (Bus.regs s2).a).s, (NES.wrS s2 0x2000 (Bus.regs s2).a).p⟩ : Regs) = _ := hon2.regs
  have hpp : (NES.wrS s2 0x2000 (Bus.regs s2).a).p = t.regs.p := congrArg Regs.p hreg
  rw [checks_nes_id (by rw [hpp]; exact hb.i) hnp]
  obtain ⟨hI, cand, hcm, hcov⟩ := hall t.regs.a (VS.mem_elems hb.a) t.regs.p (VS.mem_elems hb.p)
  rw [hk] at hcov
  simp only [covers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, readsA, writesA, readsX, writesX, readsY, writesY, Mode.usesX, Mode.usesY] at hcov
  obtain ⟨⟨⟨⟨⟨⟨hcpc, hcs⟩, hcp⟩, hca⟩, hcx⟩, hcy⟩, hcc⟩ := hcov
  have hnext : t.regs.pc + 1 + 2 = onEnter + 3 := by rw [htpc]; decide
  refine ⟨_, ?_, ⟨cand, ?_, ?_⟩, Or.inr ⟨?_, hon2⟩⟩
  · exact fun a' ha' => hc a' ha'
  · show cand ∈ T.at (t.regs.pc + 1 + 2)
    rw [hnext]; exact hcm
  · exact {
      pc := by show t.regs.pc + 1 + 2 = cand.pc; rw [hnext]; exact hcpc.symm
      sp := by show t.regs.s = cand.s; rw [← hsp']; exact hcs.symm
      a := by simpa using hca
      x := VS.sub_sound (by simpa using hcx) hb.x
      y := VS.sub_sound (by simpa using hcy) hb.y
      p := hcp
      i := hb.i
      bad := hb.bad
      cells := by
        intro c hcin
        have hcc' := hcc c hcin
        simp only [cellCoveredR, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, reduceCtorEq, false_and, or_false] at hcc'
        simpa [applyW] using cellCovered_sound hb hcc'
      glob := hb.glob
      frame := hb.frame }
  · show onPC (t.regs.pc + 1 + 2) = true
    rw [hnext]; exact hon

/-- `sta $2000` with bit 7 clear in the handler's first instructions: NMI generation goes off. -/
theorem exit_sound {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} {t : Plain} {b : Box} (h : RelOn s t) (hc : Code rom t) (hb : Holds prot g ram0 b t) (hpc : b.pc = onExit)
    (hbox : exitBox rom g T b = true) (hg : Guard s) :
    GInv rom prot g ram0 T (CPU.step.run s).2 := by
  have htpc : t.regs.pc = 0x808C := hb.pc.trans hpc
  have hspc : s.pc = 0x808C := (congrArg Regs.pc h.regs).trans htpc
  unfold exitBox at hbox
  simp only [hpc, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hbox
  obtain ⟨⟨⟨hk, hbase⟩, hbit⟩, hio⟩ := hbox
  obtain ⟨hpol, hpen, hct⟩ := hg (by rw [hspc]; decide)
  have hct : (preChecks s).ctrl &&& 0x80 = 0 := by
    rw [hct hspc]
    have ha : s.a = t.regs.a := congrArg Regs.a h.regs
    have := hbit t.regs.a (VS.mem_elems hb.a)
    rw [ha]
    simpa using this
  obtain ⟨h0, h2, -, -, hinv⟩ := io_box_next hc hb hio
  have hop : t.prg (t.regs.pc &&& 0x7FFF) = 0x8D := by
    rw [hc _ h0, htpc]; exact dec_sta _ hk
  have hb1 : t.prg (t.regs.pc + 1 &&& 0x7FFF) = rom (0x808C + 1) := by
    rw [htpc]; exact hc _ (by decide)
  have hb2 : t.prg (t.regs.pc + 1 + 1 &&& 0x7FFF) = rom (0x808C + 2) := by
    rw [htpc]; exact hc _ (by decide)
  have hF := SimO.fetch.2 s t h (by
    show (t.bad || !Plain.readable t.regs.pc) = false
    have : Plain.readable t.regs.pc = true := by simp [Plain.readable, h0]
    simp [hb.bad, this])
  have hv := fetch_val t h0
  rw [hop] at hv
  have hop' : (CPU.fetch.run s).1 = 0x8D := hF.1.trans hv
  have hpre : preChecks s = NES.wrS (CPU.fetch16.run (CPU.fetch.run s).2).2 (CPU.fetch16.run (CPU.fetch.run s).2).1 (Bus.regs (CPU.fetch16.run (CPU.fetch.run s).2).2).a := by
    rw [preChecks, hop', exec8d_eq]
  have hbt : Plain.readable (t.regs.pc + 1) = true ∧ Plain.readable (t.regs.pc + 1 + 1) = true := by
    rw [htpc]; decide
  have h16 := SimO.fetch16.2 _ _ hF.2 (by
    show (t.bad || !Plain.readable t.regs.pc || !Plain.readable (t.regs.pc + 1) || !Plain.readable (t.regs.pc + 1 + 1)) = false
    have : Plain.readable t.regs.pc = true := by simp [Plain.readable, h0]
    simp [hb.bad, this, hbt.1, hbt.2])
  have hA : (CPU.fetch16.run (CPU.fetch.run s).2).1 = 0x2000 := by
    rw [h16.1, fetch16_plain_val, fetch_val _ (by rw [fetch_pc, htpc]; decide), fetch_val _ (by rw [fetch_pc, fetch_pc, htpc]; decide)]
    show base (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 1 + 1 &&& 0x7FFF)) = _
    rw [hb1, hb2]
    exact hbase
  rw [hA] at hpre
  have hr2 := h16.2
  generalize (CPU.fetch16.run (CPU.fetch.run s).2).2 = s2 at hpre hr2
  obtain ⟨c, pen, hcore, -⟩ := NES.core_wrS_2000 s2 (Bus.regs s2).a
  have hon3 := hr2.of_core hcore
  rw [← hpre] at hon3
  have hp3 : (preChecks s).p &&& 4 ≠ 0 := by
    have hreg := congrArg Regs.p hon3.regs
    have : (preChecks s).p = t.regs.p := hreg
    rw [this]; exact hb.i
  rw [step_eq, checks_nes_id hp3 hpol]
  have hd : decode 0x8D = .store .a .abs := by decide
  have hop8 : decode (t.prg (t.regs.pc &&& 0x7FFF)) = .store .a .abs := by rw [hop]; exact hd
  rw [hop8] at hinv
  refine ⟨_, ?_, hinv, Or.inl ?_⟩
  · exact fun a' ha' => hc a' ha'
  · exact { regs := hon3.regs.trans (by
              have e : t.regs.pc + 1 + 1 + 1 = t.regs.pc + 3 := by bv_decide (config := { enums := false })
              show Regs.mk (t.regs.pc + 1 + 1 + 1) t.regs.a t.regs.x t.regs.y t.regs.s t.regs.p = Regs.mk (t.regs.pc + 3) t.regs.a t.regs.x t.regs.y t.regs.s t.regs.p
              rw [e])
            ram := hon3.ram, size := hon3.size, prg := hon3.prg, ctrl := hct, nmiPending := hpen, nmiPolled := hpol }

/-- An instruction run with NMI generation on, from a box the plain checker accepted: its plain successor is in the table. If the
last poll asked for an NMI, the successor has to be a state that can take one. -/
theorem on_sound {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} {t : Plain} {b : Box} (hchk : checkF rom exit prot g T = true) (hidle : exit idlePC = false)
    (h : RelOn s t) (hc : Code rom t) (hb : Holds prot g ram0 b t) (h0 : 0x8000 ≤ t.regs.pc)
    (hck : checkBox rom prot g T b = true)
    (hop : t.prg (t.regs.pc &&& 0x7FFF) = 0x40 ∨ t.prg (t.regs.pc &&& 0x7FFF) = 0x4C ∨ t.prg (t.regs.pc &&& 0x7FFF) = 0xAD ∨
      t.prg (t.regs.pc &&& 0x7FFF) = 0x29 ∨ t.prg (t.regs.pc &&& 0x7FFF) = 0x8D)
    (hnext : (plainExec t).bad = false → (plainExec t).regs.pc = idlePC ∨ (preamblePC (plainExec t).regs.pc = true ∧ (preChecks s).nmiPolled = false))
    (hA : ProtKept prot ram0 (CPU.step.run s).2 → Clean g (CPU.step.run s).2) :
    GInv rom prot g ram0 T (CPU.step.run s).2 := by
  obtain ⟨hcode, cand, hcm, hcb⟩ := inv_step_box hck hc hb
  obtain ⟨hrel, he, hi⟩ := on_plain h h0 hop hcb.bad
  rw [he] at hcode hcm hcb
  have hp3 : (preChecks s).p &&& 4 ≠ 0 := by
    have : (preChecks s).p = (plainExec t).regs.p := congrArg Regs.p hrel.regs
    rw [this]; exact hi
  have honpc : onPC (plainExec t).regs.pc = true := by
    rcases hnext hcb.bad with h1 | ⟨h1, _⟩
    · rw [h1]; decide
    · simp [onPC, h1]
  cases hpol : (preChecks s).nmiPolled with
  | false =>
    rw [step_eq, checks_nes_id hp3 hpol] at hA ⊢
    exact ⟨_, hcode, ⟨cand, hcm, hcb.holds ((hA (fun i hp _ => (hrel.ram i).trans (hcb.frame _ hp))).plain hrel.ram)⟩, Or.inr ⟨honpc, hrel⟩⟩
  | true =>
    rcases hnext hcb.bad with h1 | ⟨_, h1⟩
    · have hcp : cand.pc = idlePC := hcb.pc.symm.trans h1
      have hbx := check_box hchk hcm
      have hbox : nmiBox rom prot g T cand = true := by
        unfold boxF checkAny at hbx
        simp only [hcp, hidle, Bool.false_or, beq_self_eq_true, if_true] at hbx
        have hne1 : (idlePC == onEnter) = false := by decide
        have hne2 : (idlePC == onExit) = false := by decide
        have hne3 : (idlePC == rtiPC) = false := by decide
        simp only [hne1, hne2, hne3, Bool.false_eq_true, if_false, if_true, Bool.and_eq_true, idleLoop] at hbx
        exact hbx.2.2
      have h0' : 0x8000 ≤ (plainExec t).regs.pc := by rw [h1]; decide
      obtain ⟨_, hR⟩ := SimO.nmi.2 _ _ hrel (by
        obtain ⟨_, _, _, hbad⟩ := plain_nmi (plainExec t) hcode h0' hcb.bad
        rw [hbad]; exact hcb.bad)
      rw [step_eq, checks_nes_nmi hp3 hpol] at hA ⊢
      have hK := hA (fun i hp hl => (hR.ram i).trans ((nmi_keeps_high _ hcode h0' hcb.bad hl).trans (hcb.frame _ hp)))
      have hclean : AssumedOk g (plainExec t).ram := fun i hi => by
        have h1 := hK.plain hR.ram i hi
        rwa [nmi_keeps_assumed _ hcode h0' hcb.bad hi] at h1
      obtain ⟨c2, i2, on2⟩ := nmi_next hcode (hcb.holds hclean) h0' hbox
      exact ⟨_, c2, i2, Or.inr ⟨on2, hR⟩⟩
    · rw [hpol] at h1; cases h1

theorem pc_40 (u : Plain) : ((CPU.exec (σ := Plain) 0x40).run u).2.regs.pc =
    base (Plain.memRead u.ram u.prg (0x100 ||| (u.regs.s + 1 + 1).toUInt16)) (Plain.memRead u.ram u.prg (0x100 ||| (u.regs.s + 1 + 1 + 1).toUInt16)) := rfl
theorem pc_4c (u : Plain) : ((CPU.exec (σ := Plain) 0x4C).run u).2.regs.pc = (CPU.fetch16.run u).1 := rfl

theorem elems_single {t : VS} {v w : UInt8} (h : t.elems == [v]) (hm : t.mem w = true) : w = v := by
  have h1 := VS.mem_elems hm
  rw [beq_iff_eq.mp h] at h1
  simpa using h1

theorem plainExec_op {t : Plain} {op : UInt8} (h0 : 0x8000 ≤ t.regs.pc) (hop : t.prg (t.regs.pc &&& 0x7FFF) = op) :
    plainExec t = ((CPU.exec op).run (CPU.fetch.run t).2).2 := by
  rw [plainExec, fetch_val t h0, hop]

/-- One instruction on the full NES, in the table `checkF` accepted, including those that run with NMI generation on. -/
theorem ginv_stepK {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} (hchk : checkF rom exit prot g T = true) (hidle : exit idlePC = false)
    (h : GInv rom prot g ram0 T s) (hx : exit s.pc = false) (hg : Guard s) (hA : ProtKept prot ram0 (CPU.step.run s).2 → Clean g (CPU.step.run s).2) :
    GInv rom prot g ram0 T (CPU.step.run s).2 := by
  obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := h
  have hspc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  have hbpc : b.pc = t.regs.pc := hb.pc.symm
  have hbx := check_box hchk hbm
  unfold boxF checkAny at hbx
  have hxb : exit b.pc = false := by rw [hbpc, ← hspc]; exact hx
  rw [hxb, Bool.false_or] at hbx
  have ofN : NInv rom prot g ram0 T (CPU.step.run s).2 → GInv rom prot g ram0 T (CPU.step.run s).2 := by
    rintro ⟨t', r, c, i⟩
    exact ⟨t', c, i, Or.inl r⟩
  have hcov : ∀ {q : UInt16}, ¬ (b.pc == q) = true ↔ b.pc ≠ q := by simp
  by_cases h1 : b.pc = onEnter
  · rw [if_pos (by simp [h1])] at hbx
    rcases hrel with hr | ⟨hon, _⟩
    · exact enter_sound hr hc hb h1 hbx
    · rw [← hbpc, h1] at hon; exact absurd hon (by decide)
  rw [if_neg (hcov.mpr h1)] at hbx
  by_cases h2 : b.pc = onExit
  · rw [if_pos (by simp [h2])] at hbx
    rcases hrel with hr | ⟨_, hr⟩
    · refine ofN (io_box_sound hr hc hb ?_)
      simp only [exitBox, Bool.and_eq_true] at hbx
      exact hbx.2
    · exact exit_sound hr hc hb h2 hbx hg
  rw [if_neg (hcov.mpr h2)] at hbx
  by_cases h3 : b.pc = rtiPC
  · rw [if_pos (by simp [h3])] at hbx
    simp only [Bool.and_eq_true] at hbx
    obtain ⟨hck, hr2⟩ := hbx
    rcases hrel with hr | ⟨_, hr⟩
    · exact ofN (plain_box_sound hr hc hb hck hA)
    · simp only [rtiToIdle, Bool.and_eq_true] at hr2
      obtain ⟨⟨hop, hlo⟩, hhi⟩ := hr2
      have h0 : 0x8000 ≤ t.regs.pc := by rw [← hbpc, h3]; decide
      have hop' : t.prg (t.regs.pc &&& 0x7FFF) = 0x40 := by
        rw [hc _ h0, ← hbpc]; simpa using hop
      refine on_sound hchk hidle hr hc hb h0 hck (Or.inl hop') (fun _ => Or.inl ?_) hA
      rw [plainExec_op h0 hop', pc_40]
      show base (Plain.memRead t.ram t.prg (0x100 ||| (t.regs.s + 1 + 1).toUInt16)) (Plain.memRead t.ram t.prg (0x100 ||| (t.regs.s + 1 + 1 + 1).toUInt16)) = _
      have e1 : t.regs.s + 1 + 1 = b.s + 2 := by rw [hb.sp]; bv_decide (config := { enums := false })
      have e2 : t.regs.s + 1 + 1 + 1 = b.s + 3 := by rw [hb.sp]; bv_decide (config := { enums := false })
      rw [e2, e1]
      have v1 := elems_single hlo (readVS_sound hc hb (stack (b.s + 2)))
      have v2 := elems_single hhi (readVS_sound hc hb (stack (b.s + 3)))
      show base (Plain.memRead t.ram t.prg (stack (b.s + 2))) (Plain.memRead t.ram t.prg (stack (b.s + 3))) = _
      rw [v1, v2]
      decide
  rw [if_neg (hcov.mpr h3)] at hbx
  by_cases h4 : b.pc = idlePC
  · rw [if_pos (by simp [h4])] at hbx
    simp only [Bool.and_eq_true] at hbx
    obtain ⟨hck, hr2⟩ := hbx
    rcases hrel with hr | ⟨_, hr⟩
    · exact ofN (plain_box_sound hr hc hb hck hA)
    · simp only [idleLoop, Bool.and_eq_true, beq_iff_eq] at hr2
      obtain ⟨⟨hop, hbase⟩, _⟩ := hr2
      have htp : t.regs.pc = 0x8057 := by rw [← hbpc, h4]; rfl
      have h0 : 0x8000 ≤ t.regs.pc := by rw [htp]; decide
      have hop' : t.prg (t.regs.pc &&& 0x7FFF) = 0x4C := by
        rw [hc _ h0, ← hbpc]; exact hop
      refine on_sound hchk hidle hr hc hb h0 hck (Or.inr (Or.inl hop')) (fun _ => Or.inl ?_) hA
      rw [plainExec_op h0 hop', pc_4c, fetch16_plain_val, fetch_val _ (by rw [fetch_pc, htp]; decide), fetch_val _ (by rw [fetch_pc, fetch_pc, htp]; decide)]
      show base (t.prg (t.regs.pc + 1 &&& 0x7FFF)) (t.prg (t.regs.pc + 1 + 1 &&& 0x7FFF)) = _
      rw [← hbase, hbpc, htp]
      have hb1 : t.prg (0x8057 + 1 &&& 0x7FFF) = rom (0x8057 + 1) := hc _ (by decide)
      have hb2 : t.prg (0x8057 + 1 + 1 &&& 0x7FFF) = rom (0x8057 + 2) := hc _ (by decide)
      rw [hb1, hb2]
  rw [if_neg (hcov.mpr h4)] at hbx
  by_cases h5 : preamblePC b.pc = true
  · rw [if_pos h5] at hbx
    simp only [Bool.and_eq_true] at hbx
    obtain ⟨hck, hr2⟩ := hbx
    rcases hrel with hr | ⟨_, hr⟩
    · exact ofN (plain_box_sound hr hc hb hck hA)
    · have hps : preamblePC s.pc = true := by rw [hspc, ← hbpc]; exact h5
      have hpol := (hg hps).1
      simp only [preambleOp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hr2
      have hrom : ∀ q : UInt16, b.pc = q → 0x8000 ≤ q → t.prg (t.regs.pc &&& 0x7FFF) = rom q := by
        intro q hq hq0
        have : t.regs.pc = q := hbpc.symm.trans hq
        rw [this]
        exact hc _ hq0
      rcases hr2 with ((⟨hq, hv⟩ | ⟨hq, hv⟩) | ⟨hq, hv⟩) | ⟨hq, hv⟩
      · have h0 : 0x8000 ≤ t.regs.pc := by rw [← hbpc, hq]; decide
        have hop' := hrom _ hq (by decide)
        rw [hq] at hv
        rw [hv] at hop'
        refine on_sound hchk hidle hr hc hb h0 hck (Or.inr (Or.inr (Or.inl hop'))) (fun _ => Or.inr ⟨?_, hpol⟩) hA
        rw [plainExec_op h0 hop', pc_ad, fetch_pc, ← hbpc, hq]; decide
      · have h0 : 0x8000 ≤ t.regs.pc := by rw [← hbpc, hq]; decide
        have hop' := hrom _ hq (by decide)
        rw [hq] at hv
        rw [hv] at hop'
        refine on_sound hchk hidle hr hc hb h0 hck (Or.inr (Or.inr (Or.inr (Or.inl hop')))) (fun _ => Or.inr ⟨?_, hpol⟩) hA
        rw [plainExec_op h0 hop', pc_29, fetch_pc, ← hbpc, hq]; decide
      · have h0 : 0x8000 ≤ t.regs.pc := by rw [← hbpc, hq]; decide
        have hop' := hrom _ hq (by decide)
        rw [hq] at hv
        rw [hv] at hop'
        refine on_sound hchk hidle hr hc hb h0 hck (Or.inr (Or.inr (Or.inr (Or.inr hop')))) (fun _ => Or.inr ⟨?_, hpol⟩) hA
        rw [plainExec_op h0 hop', pc_8d, fetch_pc, ← hbpc, hq]; decide
      · have h0 : 0x8000 ≤ t.regs.pc := by rw [← hbpc, hq]; decide
        have hop' := hrom _ hq (by decide)
        rw [hq] at hv
        rw [hv] at hop'
        refine on_sound hchk hidle hr hc hb h0 hck (Or.inr (Or.inr (Or.inr (Or.inl hop')))) (fun _ => Or.inr ⟨?_, hpol⟩) hA
        rw [plainExec_op h0 hop', pc_29, fetch_pc, ← hbpc, hq]; decide
  rw [if_neg h5] at hbx
  rcases hrel with hr | ⟨hon, _⟩
  · simp only [Bool.or_eq_true] at hbx
    rcases hbx with (h6 | h6) | h6
    · exact ofN (plain_box_sound hr hc hb h6 hA)
    · exact ofN (io_box_sound hr hc hb h6)
    · exact ofN (load_box_sound hr hc hb h6)
  · exfalso
    rw [← hbpc] at hon
    simp only [onPC, Bool.or_eq_true, beq_iff_eq] at hon
    rcases hon with (h6 | h6) | h6
    · exact h3 h6
    · exact h4 h6
    · exact h5 h6

theorem ginv_step {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    {s : NES} (hchk : checkF rom exit prot g T = true) (hidle : exit idlePC = false)
    (h : GInv rom prot g ram0 T s) (hx : exit s.pc = false) (hg : Guard s) (hA : Clean g (CPU.step.run s).2) :
    GInv rom prot g ram0 T (CPU.step.run s).2 :=
  ginv_stepK hchk hidle h hx hg (fun _ => hA)

/-- `n` steps of the machine. -/
def stepN : Nat → NES → NES
  | 0, s => s
  | n + 1, s => stepN n (CPU.step.run s).2

/-- The table's invariant, over any number of instructions and so over any number of frames, for any controller input and any
PPU timing: as long as no exit address comes up and `Guard` holds at each step. -/
theorem ginv_stepN {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8}
    (hchk : checkF rom exit prot g T = true) (hidle : exit idlePC = false) (n : Nat) (s : NES)
    (hx : ∀ i, i < n → exit (stepN i s).pc = false) (hg : ∀ i, i < n → Guard (stepN i s))
    (hA : ∀ i, i < n → Clean g (stepN (i + 1) s))
    (h : GInv rom prot g ram0 T s) : GInv rom prot g ram0 T (stepN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    exact ih (CPU.step.run s).2 (fun i hi => hx (i + 1) (Nat.succ_lt_succ hi)) (fun i hi => hg (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hA (i + 1) (Nat.succ_lt_succ hi))
      (ginv_step hchk hidle h (hx 0 (Nat.succ_pos _)) (hg 0 (Nat.succ_pos _)) (hA 0 (Nat.succ_pos _)))

/-- Moving to the next region's table at a region's exit: every box the first table has at this address is contained in a box of the second.
The second table's protected cells are measured from here. -/
theorem ginv_hop {rom : UInt16 → UInt8} {prot prot' : UInt16 → Bool} {g : Global} {T T' : Table} {ram0 : UInt16 → UInt8} {s : NES}
    (h : GInv rom prot g ram0 T s)
    (hl : (T.at s.pc).all (entryIn g T') = true) :
    ∃ ram1, GInv rom prot' g ram1 T' s := by
  obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := h
  have hspc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  have hin : entryIn g T' b = true := by
    rw [hspc] at hl
    exact List.all_eq_true.mp hl b hbm
  have hb' : Holds prot' g t.ram b t :=
    { pc := hb.pc, sp := hb.sp, a := hb.a, x := hb.x, y := hb.y, p := hb.p, i := hb.i, bad := hb.bad, cells := hb.cells, glob := hb.glob,
      frame := fun _ _ => rfl }
  exact ⟨t.ram, t, hc, inv_of_entry hin hb', hrel⟩

theorem holds_of_le {prot : UInt16 → Bool} {g : Global} {ram0 : UInt16 → UInt8} {b e : Box} {t : Plain}
    (hle : Box.le g b e = true) (h : Holds prot g ram0 b t) : Holds prot g ram0 e t := by
  simp only [Box.le, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨⟨hpc, hs⟩, ha⟩, hx⟩, hy⟩, hp⟩, hcells⟩ := hle
  exact {
    pc := by rw [h.pc, hpc]
    sp := by rw [h.sp, hs]
    a := VS.sub_sound ha h.a
    x := VS.sub_sound hx h.x
    y := VS.sub_sound hy h.y
    p := VS.sub_sound hp h.p
    i := h.i
    bad := h.bad
    cells := fun d hd => by simpa [applyW] using cellCovered_sound h (hcells d hd)
    glob := h.glob
    frame := h.frame }

/-- As `ginv_hop`, through the next region's entry boxes, so that a region's check need not compute the next region's table. -/
theorem ginv_hop' {rom : UInt16 → UInt8} {prot prot' : UInt16 → Bool} {g : Global} {T T' : Table} {ram0 : UInt16 → UInt8} {s : NES}
    {E : List Box} (h : GInv rom prot g ram0 T s)
    (hl : (T.at s.pc).all (fun b => E.any (Box.le g b)) = true) (hE : E.all (entryIn g T') = true) :
    ∃ ram1, GInv rom prot' g ram1 T' s := by
  obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := h
  have hspc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  have hb1 := List.all_eq_true.mp (by rw [hspc] at hl; exact hl) b hbm
  obtain ⟨e, he, hle⟩ := List.any_eq_true.mp hb1
  have hb' : Holds prot' g t.ram b t :=
    { pc := hb.pc, sp := hb.sp, a := hb.a, x := hb.x, y := hb.y, p := hb.p, i := hb.i, bad := hb.bad, cells := hb.cells, glob := hb.glob,
      frame := fun _ _ => rfl }
  exact ⟨t.ram, t, hc, inv_of_entry (List.all_eq_true.mp hE e he) (holds_of_le hle hb'), hrel⟩

/-- One region of a frame. -/
structure Region where
  exit : UInt16 → Bool
  prot : UInt16 → Bool
  T : Table
  entries : List Box

/-- A state in some region's table. -/
def RInv (rom : UInt16 → UInt8) (g : Global) (rs : List Region) (s : NES) : Prop :=
  ∃ r ∈ rs, ∃ ram0, GInv rom r.prot g ram0 r.T s

/-- Regions fit together: each is checked, its entry boxes are in its table, and at each exit other than `done`, its boxes are in the entry boxes of a region
that goes on from there. -/
structure Fits (rom : UInt16 → UInt8) (g : Global) (rs : List Region) (done : UInt16 → Bool) : Prop where
  chk : ∀ r ∈ rs, checkF rom r.exit r.prot g r.T = true
  idle : ∀ r ∈ rs, r.exit idlePC = false
  entries : ∀ r ∈ rs, r.entries.all (entryIn g r.T) = true
  link : ∀ r ∈ rs, ∀ pc, r.exit pc = true → done pc = true ∨
    ∃ r' ∈ rs, r'.exit pc = false ∧ (r.T.at pc).all (fun b => r'.entries.any (Box.le g b)) = true

theorem rinv_step {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {done : UInt16 → Bool} {s : NES}
    (hf : Fits rom g rs done) (h : RInv rom g rs s) (hd : done s.pc = false) (hg : Guard s) (hA : Clean g (CPU.step.run s).2) :
    RInv rom g rs (CPU.step.run s).2 := by
  obtain ⟨r, hr, ram0, hi⟩ := h
  cases hx : r.exit s.pc with
  | false => exact ⟨r, hr, ram0, ginv_step (hf.chk r hr) (hf.idle r hr) hi hx hg hA⟩
  | true =>
    rcases hf.link r hr s.pc hx with h1 | ⟨r', hr', hx', hl⟩
    · rw [hd] at h1; cases h1
    · obtain ⟨ram1, hi'⟩ := ginv_hop' (prot' := r'.prot) (T' := r'.T) hi hl (hf.entries r' hr')
      exact ⟨r', hr', ram1, ginv_step (hf.chk r' hr') (hf.idle r' hr') hi' hx' hg hA⟩

/-- The regions' invariant, over any number of instructions and so any number of frames, for any controller input and PPU timing, until a `done` address comes up, with
`Guard` at each step. -/
theorem rinv_stepN {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {done : UInt16 → Bool}
    (hf : Fits rom g rs done) (n : Nat) (s : NES)
    (hd : ∀ i, i < n → done (stepN i s).pc = false) (hg : ∀ i, i < n → Guard (stepN i s))
    (hA : ∀ i, i < n → Clean g (stepN (i + 1) s))
    (h : RInv rom g rs s) : RInv rom g rs (stepN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    exact ih (CPU.step.run s).2 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi)) (fun i hi => hg (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hA (i + 1) (Nat.succ_lt_succ hi))
      (rinv_step hf h (hd 0 (Nat.succ_pos _)) (hg 0 (Nat.succ_pos _)) (hA 0 (Nat.succ_pos _)))

/-- As `RInv`, with cells `K`, which every region protects, kept at their values in `start`. -/
def KInv (rom : UInt16 → UInt8) (g : Global) (rs : List Region) (K : UInt16 → Bool) (start : UInt16 → UInt8) (s : NES) : Prop :=
  ∃ r ∈ rs, ∃ ram0, GInv rom r.prot g ram0 r.T s ∧ ∀ i, K i = true → ram0 i = start i

theorem kinv_step {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {done K : UInt16 → Bool} {start : UInt16 → UInt8} {s : NES}
    (hf : Fits rom g rs done) (hK : ∀ r ∈ rs, ∀ i, K i = true → r.prot i = true)
    (h : KInv rom g rs K start s) (hd : done s.pc = false) (hg : Guard s) (hA : Clean g (CPU.step.run s).2) :
    KInv rom g rs K start (CPU.step.run s).2 := by
  obtain ⟨r, hr, ram0, hi, hk⟩ := h
  cases hx : r.exit s.pc with
  | false => exact ⟨r, hr, ram0, ginv_step (hf.chk r hr) (hf.idle r hr) hi hx hg hA, hk⟩
  | true =>
    rcases hf.link r hr s.pc hx with h1 | ⟨r', hr', hx', hl⟩
    · rw [hd] at h1; cases h1
    · obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := hi
      have hspc : s.pc = t.regs.pc := by
        rcases hrel with h1 | ⟨_, h1⟩
        · exact congrArg Regs.pc h1.regs
        · exact congrArg Regs.pc h1.regs
      have hb1 := List.all_eq_true.mp (by rw [hspc] at hl; exact hl) b hbm
      obtain ⟨e, he, hle⟩ := List.any_eq_true.mp hb1
      have hb' : Holds r'.prot g t.ram b t :=
        { pc := hb.pc, sp := hb.sp, a := hb.a, x := hb.x, y := hb.y, p := hb.p, i := hb.i, bad := hb.bad, cells := hb.cells, glob := hb.glob,
          frame := fun _ _ => rfl }
      have hi' : GInv rom r'.prot g t.ram r'.T s :=
        ⟨t, hc, inv_of_entry (List.all_eq_true.mp (hf.entries r' hr') e he) (holds_of_le hle hb'), hrel⟩
      exact ⟨r', hr', t.ram, ginv_step (hf.chk r' hr') (hf.idle r' hr') hi' hx' hg hA,
        fun i hi => (hb.frame i (hK r hr i hi)).trans (hk i hi)⟩

/-- Cells that all the regions protect keep their values, over any number of instructions, until a `done` address comes up. -/
theorem kinv_stepN {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {done K : UInt16 → Bool} {start : UInt16 → UInt8}
    (hf : Fits rom g rs done) (hK : ∀ r ∈ rs, ∀ i, K i = true → r.prot i = true) (n : Nat) (s : NES)
    (hd : ∀ i, i < n → done (stepN i s).pc = false) (hg : ∀ i, i < n → Guard (stepN i s))
    (hA : ∀ i, i < n → Clean g (stepN (i + 1) s))
    (h : KInv rom g rs K start s) : KInv rom g rs K start (stepN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    exact ih (CPU.step.run s).2 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi)) (fun i hi => hg (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hA (i + 1) (Nat.succ_lt_succ hi))
      (kinv_step hf hK h (hd 0 (Nat.succ_pos _)) (hg 0 (Nat.succ_pos _)) (hA 0 (Nat.succ_pos _)))

/-- What a kept cell's value is on the machine. -/
theorem kinv_ram {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {K : UInt16 → Bool} {start : UInt16 → UInt8} {s : NES}
    (hK : ∀ r ∈ rs, ∀ i, K i = true → r.prot i = true)
    (h : KInv rom g rs K start s) (i : UInt16) (hi : K i = true) (hl : i &&& 0x7FF = i) :
    s.ram.get! i.toNat = start i := by
  obtain ⟨r, hr, ram0, ⟨t, _, ⟨b, _, hb⟩, hrel⟩, hk⟩ := h
  have h2 : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact h1.ram i
    · exact h1.ram i
  rw [hl] at h2
  rw [h2, hb.frame i (hK r hr i hi), hk i hi]

end Abs
end Smb
