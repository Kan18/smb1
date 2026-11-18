import Smb.Routine.PpuEdge
import Smb.Routine.PpuCalm

/-!
# Between frames, with the PPU

The instructions between the handler's last read of `$2002` and the next `$808F`, cycle by cycle: after that read, vblank can only be one that has just started. So if NMI generation then
turns on with vblank set, or vblank rises in the idle loop, the NMI is taken within a few cycles of dot 342, and the handler's first instructions run long before the next PPU event. That is
`Guard`.
-/
set_option maxRecDepth 20000
namespace Smb.Routine.PpuFrame
open Smb NES

/-- NMI generation on, no DMA latched, the schedule known. -/
structure OnBase (x : NES) : Prop where
  sch : SchS x
  on : x.ctrl &&& 0x80 ≠ 0
  dma : x.dmaPending = false

def A0 (x : NES) : Prop := St0 x ∧ x.nmiPolled = false
def A1 (F : Nat) (x : NES) : Prop := St1 x F ∧ x.nmiPolled = false
def A2 (F : Nat) (x : NES) : Prop := St2 x F ∧ x.nmiPolled = false
def A3 (F : Nat) (x : NES) : Prop := St2 x F ∧ x.nmiPolled = true

def Any (F : Nat) (x : NES) : Prop := A0 x ∨ A1 F x ∨ A2 F x ∨ A3 F x
def L1 (F : Nat) (x : NES) : Prop := A1 F x ∨ A2 F x ∨ A3 F x
def L2 (F : Nat) (x : NES) : Prop := A2 F x ∨ A3 F x

/-- One bus cycle at RAM or ROM. -/
def OnBus (x r : NES) : Prop := ∃ y, MidOK (beginCycle x) y ∧ y.vbl = (beginCycle x).vbl ∧ r = endCycle y

theorem onBus_rd (x : NES) (a : UInt16) (ha : a < 0x2000 ∨ 0x8000 ≤ a) (hd : x.dmaPending = false) : OnBus x (rdS x a).2 := by
  simp only [rdS, hd, Bool.false_eq_true, if_false]
  exact read_mid x a ha

theorem onBus_wr (x : NES) (a : UInt16) (b : UInt8) (ha : a < 0x2000) : OnBus x (wrS x a b) := write_mid x a b ha

/-- `P` goes to `Q` over a cycle, within the base `B`. -/
def TR (B P Q : NES → Prop) : Prop := ∀ x r, B x → P x → OnBus x r → r.unmodelled = false → B r ∧ Q r

/-- A base: it ignores the CPU registers, and no DMA is latched. -/
structure IsBase (B : NES → Prop) : Prop where
  regs : ∀ x (f : Regs → Regs), B x → B (CPU.modRegs f |>.run x).2
  dma : ∀ x, B x → x.dmaPending = false

theorem tr_any {F : Nat} (h1 : 344 ≤ F) (h2 : F ≤ 6000) : TR OnBase (Any F) (Any (F + 3)) := by
  rintro x r hb hp ⟨y, hm, hv, rfl⟩ hu
  have oc : OnCyc x y := ⟨hb.sch, hb.on, hm, hv, hu⟩
  rcases hp with ⟨q, _⟩ | ⟨q, _⟩ | ⟨q, _⟩ | ⟨q, _⟩
  · obtain ⟨a, b, c, d, e⟩ := on0 oc q
    refine ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, ?_⟩
    rcases e with e | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
    · exact Or.inl ⟨e, d⟩
    · exact Or.inr (Or.inl ⟨⟨e1, by omega, e3, e4⟩, d⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨e1, by omega, e3, e4⟩, d⟩))
  · obtain ⟨a, b, c, d, e⟩ := on1 oc q h2
    exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, Or.inr (Or.inr (Or.inl ⟨e, d⟩))⟩
  · obtain ⟨a, b, c, d, e⟩ := on2 oc q h2
    exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, Or.inr (Or.inr (Or.inr ⟨e, d⟩))⟩
  · obtain ⟨a, b, c, d, e⟩ := on2 oc q h2
    exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, Or.inr (Or.inr (Or.inr ⟨e, d⟩))⟩

theorem tr_l1 {F : Nat} (h2 : F ≤ 6000) : TR OnBase (L1 F) (L2 (F + 3)) := by
  rintro x r hb hp ⟨y, hm, hv, rfl⟩ hu
  have oc : OnCyc x y := ⟨hb.sch, hb.on, hm, hv, hu⟩
  rcases hp with ⟨q, _⟩ | ⟨q, _⟩ | ⟨q, _⟩
  · obtain ⟨a, b, c, d, e⟩ := on1 oc q h2
    exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, Or.inl ⟨e, d⟩⟩
  · obtain ⟨a, b, c, d, e⟩ := on2 oc q h2
    exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, Or.inr ⟨e, d⟩⟩
  · obtain ⟨a, b, c, d, e⟩ := on2 oc q h2
    exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, Or.inr ⟨e, d⟩⟩

theorem tr_l2 {F : Nat} (h2 : F ≤ 6000) : TR OnBase (L2 F) (A3 (F + 3)) := by
  rintro x r hb hp ⟨y, hm, hv, rfl⟩ hu
  have oc : OnCyc x y := ⟨hb.sch, hb.on, hm, hv, hu⟩
  rcases hp with ⟨q, _⟩ | ⟨q, _⟩
  · obtain ⟨a, b, c, d, e⟩ := on2 oc q h2
    exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, ⟨e, d⟩⟩
  · obtain ⟨a, b, c, d, e⟩ := on2 oc q h2
    exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, ⟨e, d⟩⟩

theorem tr_a3 {F : Nat} (h2 : F ≤ 6000) : TR OnBase (A3 F) (A3 (F + 3)) := by
  rintro x r hb ⟨q, _⟩ ⟨y, hm, hv, rfl⟩ hu
  have oc : OnCyc x y := ⟨hb.sch, hb.on, hm, hv, hu⟩
  obtain ⟨a, b, c, d, e⟩ := on2 oc q h2
  exact ⟨⟨a, by rw [b]; exact hb.on, by rw [c]; exact hb.dma⟩, ⟨e, d⟩⟩

theorem OnBase.regs {x : NES} (h : OnBase x) (f : Regs → Regs) : OnBase (CPU.modRegs f |>.run x).2 :=
  ⟨SchS.of_sv h.sch ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, h.on, h.dma⟩

/-- `P` looks only at the PPU's side. -/
def RegFree (P : NES → Prop) : Prop := ∀ x (f : Regs → Regs), P x → P (CPU.modRegs f |>.run x).2

theorem rf_any (F : Nat) : RegFree (Any F) := fun _ _ h => h
theorem rf_l1 (F : Nat) : RegFree (L1 F) := fun _ _ h => h
theorem rf_l2 (F : Nat) : RegFree (L2 F) := fun _ _ h => h
theorem rf_a3 (F : Nat) : RegFree (A3 F) := fun _ _ h => h

theorem rdS_nodma (x : NES) (a : UInt16) (h : x.dmaPending = false) : rdS x a = readCycle x a := by
  simp only [rdS, h, Bool.false_eq_true, if_false]

theorem fetch_value (x : NES) (hd : x.dmaPending = false) (hpc : 0x8000 ≤ x.pc) : (CPU.fetch.run x).1 = x.prg.get! (x.pc &&& 0x7FFF).toNat := by
  have hd' : (CPU.modRegs (σ := NES) (fun r => { r with pc := x.pc + 1 }) |>.run x).2.dmaPending = false := hd
  have hv1 : (CPU.fetch.run x).1 = (rdS (CPU.modRegs (σ := NES) (fun r => { r with pc := x.pc + 1 }) |>.run x).2 x.pc).1 := rfl
  rw [hv1, rdS_nodma _ _ hd', readCycle_rom' _ _ hpc]
  rfl

theorem onIs : IsBase OnBase := ⟨fun x f h => h.regs f, fun _ h => h.dma⟩

/-- A fetch. -/
theorem fetch_tr {B P Q : NES → Prop} (hB : IsBase B) (h : TR B P Q) (hf : RegFree P) {x : NES} (hb : B x) (hp : P x) (hpc : 0x8000 ≤ x.pc)
    (hu : (CPU.fetch.run x).2.unmodelled = false) :
    B (CPU.fetch.run x).2 ∧ Q (CPU.fetch.run x).2 ∧ (CPU.fetch.run x).2.pc = x.pc + 1 ∧ (CPU.fetch.run x).2.prg = x.prg ∧
      (CPU.fetch.run x).1 = x.prg.get! (x.pc &&& 0x7FFF).toNat := by
  have e : (CPU.fetch.run x).2 = (rdS (CPU.modRegs (σ := NES) (fun r => { r with pc := x.pc + 1 }) |>.run x).2 x.pc).2 := rfl
  have hb' := hB.regs x (fun r => { r with pc := x.pc + 1 }) hb
  have hd' := hB.dma _ hb'
  have hp' := hf x (fun r => { r with pc := x.pc + 1 }) hp
  have hv1 := fetch_value x (hB.dma _ hb) hpc
  rw [e] at hu ⊢
  have hbus := onBus_rd _ x.pc (Or.inr hpc) hd'
  obtain ⟨r1, r2⟩ := h _ _ hb' hp' hbus hu
  have hv := BusStable.rdS_view (CPU.modRegs (σ := NES) (fun r => { r with pc := x.pc + 1 }) |>.run x).2 x.pc
  simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
  exact ⟨r1, r2, hv.1.1, hv.2, hv1⟩

/-- A cycle's state keeps the model's flag. -/
def UF {α : Type} (m : StateM NES α) : Prop := ∀ x, (m.run x).2.unmodelled = false → x.unmodelled = false

theorem wrMid_mono (x : NES) (a : UInt16) (b : UInt8) (h : x.unmodelled = true) : (wrMid x a b).unmodelled = true := by
  unfold wrMid
  split
  · exact h
  split
  · exact reg1_unm x a b h
  split
  · exact h
  split
  · exact h
  split
  · rfl
  · exact h

theorem wrS_mono (x : NES) (a : UInt16) (b : UInt8) (h : x.unmodelled = true) : (wrS x a b).unmodelled = true := by
  rw [wrS_eq]
  exact end_mono _ (wrMid_mono _ _ _ (begin_mono x h))

theorem dmago_mono (n : Nat) (i : UInt16) (x : NES) (h : x.unmodelled = true) : (oamDma.go n i x).unmodelled = true := by
  induction n generalizing i x with
  | zero => exact h
  | succ n ih =>
    simp only [oamDma.go]
    exact ih _ _ (end_mono _ (reg1_unm _ _ _ (begin_mono _ (read_mono x _ h))))

theorem rdS_mono (x : NES) (a : UInt16) (h : x.unmodelled = true) : (rdS x a).2.unmodelled = true := by
  unfold rdS
  apply read_mono
  split
  · unfold oamDma
    apply dmago_mono
    have h1 : (readCycle { x with dmaPending := false, unmodelled := x.unmodelled || rendering x } a).2.unmodelled = true :=
      read_mono _ a (by simp [h])
    split
    · exact read_mono _ a h1
    · exact h1
  · exact h

theorem uf_of {α : Type} {m : StateM NES α} (h : ∀ x, x.unmodelled = true → (m.run x).2.unmodelled = true) : UF m := by
  intro x hu
  cases hx : x.unmodelled with
  | false => rfl
  | true => rw [h x hx] at hu; cases hu

theorem uf_rd (a : UInt16) : UF (CPU.rd (σ := NES) a) := uf_of fun x h => rdS_mono x a h
theorem uf_fetch : UF (CPU.fetch (σ := NES)) := uf_of fun x h => rdS_mono _ _ h
theorem uf_fetch16 : UF (CPU.fetch16 (σ := NES)) := uf_of fun x h => by
  have h1 := rdS_mono { x with pc := x.pc + 1 } x.pc h
  exact rdS_mono _ _ h1

/-- Reading RAM or ROM from the regs side. -/
theorem rd_tr {B P Q : NES → Prop} (hB : IsBase B) (h : TR B P Q) {x : NES} (hb : B x) (hp : P x) (a : UInt16) (ha : a < 0x2000 ∨ 0x8000 ≤ a) (hu : (rdS x a).2.unmodelled = false) :
    B (rdS x a).2 ∧ Q (rdS x a).2 ∧ (rdS x a).2.prg = x.prg :=
  have hv := BusStable.rdS_view x a
  have hv2 : (rdS x a).2.prg = x.prg := by
    simp only [BusStable.view, Prod.mk.injEq] at hv
    exact hv.2
  have r := h _ _ hb hp (onBus_rd x a ha (hB.dma _ hb)) hu
  ⟨r.1, r.2, hv2⟩

theorem modRegs_prg (x : NES) (f : Regs → Regs) : (CPU.modRegs f |>.run x).2.prg = x.prg := rfl
theorem modRegs_pc (x : NES) (v : UInt16) : (CPU.modRegs (fun r => { r with pc := v }) |>.run x).2.pc = v := rfl

theorem jmp_eq (u : NES) : ((CPU.exec (σ := NES) 0x4C).run u).2 =
    (CPU.modRegs (fun r => { r with pc := (CPU.fetch16.run u).1 }) |>.run (CPU.fetch16.run u).2).2 := rfl

/-- `jmp` at `$8057`. -/
theorem jmp_stage {P0 P1 P2 Q : NES → Prop} (t1 : TR OnBase P0 P1) (t2 : TR OnBase P1 P2) (t3 : TR OnBase P2 Q) (f0 : RegFree P0) (f1 : RegFree P1) (f2 : RegFree P2) (fq : RegFree Q)
    {s : NES} (hb : OnBase s) (hp : P0 s) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0x8057) (hu : (Abs.preChecks s).unmodelled = false) :
    OnBase (Abs.preChecks s) ∧ Q (Abs.preChecks s) ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = 0x8057 := by
  have b0 : Smb.prg.get! ((0x8057 : UInt16) &&& 0x7FFF).toNat = 0x4C ∧ Smb.prg.get! ((0x8058 : UInt16) &&& 0x7FFF).toNat = 0x57 ∧ Smb.prg.get! ((0x8059 : UInt16) &&& 0x7FFF).toNat = 0x80 := by native_decide
  have e0 : (0x8000 : UInt16) ≤ s.pc := by rw [hpc]; decide
  have hop : (CPU.fetch.run s).1 = 0x4C := by
    rw [fetch_value s hb.dma e0, hprg, hpc]; exact b0.1
  have hpre : Abs.preChecks s = ((CPU.exec (σ := NES) 0x4C).run (CPU.fetch.run s).2).2 := by
    rw [Abs.preChecks, hop]
  rw [hpre, jmp_eq] at hu ⊢
  have e16 : (CPU.fetch16.run (CPU.fetch.run s).2).2 = (CPU.fetch.run (CPU.fetch.run (CPU.fetch.run s).2).2).2 := congrArg Prod.snd (PpuCalm.fetch16_eq _)
  have hu3 : (CPU.fetch.run (CPU.fetch.run (CPU.fetch.run s).2).2).2.unmodelled = false := by
    rw [← e16]; exact hu
  have hu2 := uf_fetch _ hu3
  have hu1 := uf_fetch _ hu2
  obtain ⟨o1, q1, c1, p1, -⟩ := fetch_tr onIs t1 f0 hb hp e0 hu1
  have e1 : (0x8000 : UInt16) ≤ (CPU.fetch.run s).2.pc := by rw [c1, hpc]; decide
  obtain ⟨o2, q2, c2, p2, v2⟩ := fetch_tr onIs t2 f1 o1 q1 e1 hu2
  have e2 : (0x8000 : UInt16) ≤ (CPU.fetch.run (CPU.fetch.run s).2).2.pc := by rw [c2, c1, hpc]; decide
  obtain ⟨o3, q3, c3, p3, v3⟩ := fetch_tr onIs t3 f2 o2 q2 e2 hu3
  have hval : (CPU.fetch16.run (CPU.fetch.run s).2).1 = 0x8057 := by
    have eV : (CPU.fetch16.run (CPU.fetch.run s).2).1 = Abs.base (CPU.fetch.run (CPU.fetch.run s).2).1 (CPU.fetch.run (CPU.fetch.run (CPU.fetch.run s).2).2).1 :=
      congrArg Prod.fst (PpuCalm.fetch16_eq _)
    rw [eV, v2, v3, p2, p1, c2, c1, hprg, hpc]
    have g1 : ((0x8057 : UInt16) + 1 &&& 0x7FFF) = ((0x8058 : UInt16) &&& 0x7FFF) := by decide
    have g2 : ((0x8057 : UInt16) + 1 + 1 &&& 0x7FFF) = ((0x8059 : UInt16) &&& 0x7FFF) := by decide
    rw [g1, g2, b0.2.1, b0.2.2]
    decide
  rw [e16]
  refine ⟨o3.regs _, fq _ _ q3, ?_, ?_⟩
  · rw [modRegs_prg, p3, p2, p1, hprg]
  · rw [modRegs_pc]; exact hval

theorem stack_lt (v : UInt8) : ((0x100 : UInt16) ||| v.toUInt16) < 0x2000 := by bv_decide (config := { enums := false })

theorem pull_eq (x : NES) : CPU.pull.run x =
    ((rdS x (0x100 ||| (x.s + 1).toUInt16)).1, (CPU.modRegs (fun r => { r with s := x.s + 1 }) |>.run (rdS x (0x100 ||| (x.s + 1).toUInt16)).2).2) := rfl

theorem pull_snd (x : NES) : (CPU.pull.run x).2 = (CPU.modRegs (fun r => { r with s := x.s + 1 }) |>.run (rdS x (0x100 ||| (x.s + 1).toUInt16)).2).2 := rfl

theorem uf_pull : UF (CPU.pull (σ := NES)) := by
  intro x h
  rw [pull_snd] at h
  exact uf_rd _ x h

/-- A program takes `P` to `Q` within the base `B`. -/
def T {α : Type} (B P Q : NES → Prop) (m : StateM NES α) : Prop :=
  UF m ∧ ∀ x, B x → P x → (m.run x).2.unmodelled = false → B (m.run x).2 ∧ Q (m.run x).2 ∧ (m.run x).2.prg = x.prg

variable {B : NES → Prop}

theorem T_bind {α β : Type} {P Q R : NES → Prop} {m : StateM NES α} {f : α → StateM NES β} (hm : T B P Q m) (hf : ∀ a, T B Q R (f a)) : T B P R (m >>= f) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Sim.run_bind] at hx
    exact hm.1 x ((hf _).1 _ hx)
  · intro x hb hp hx
    rw [Sim.run_bind] at hx ⊢
    obtain ⟨o, q, pr⟩ := hm.2 x hb hp ((hf _).1 _ hx)
    obtain ⟨o2, q2, pr2⟩ := (hf _).2 _ o q hx
    exact ⟨o2, q2, pr2.trans pr⟩

theorem T_regs {P : NES → Prop} (hB : IsBase B) (hP : RegFree P) (f : Regs → Regs) : T B P P (CPU.modRegs (σ := NES) f) :=
  ⟨fun _ h => h, fun x hb hp _ => ⟨hB.regs x f hb, hP x f hp, rfl⟩⟩

theorem T_dummyStack {P Q : NES → Prop} (hB : IsBase B) (h : TR B P Q) : T B P Q (CPU.dummyStack (σ := NES)) := by
  refine ⟨fun x hx => uf_rd _ x hx, fun x hb hp hx => ?_⟩
  exact rd_tr hB h hb hp _ (Or.inl (stack_lt _)) hx

theorem T_pull {P Q : NES → Prop} (hB : IsBase B) (h : TR B P Q) (fq : RegFree Q) : T B P Q (CPU.pull (σ := NES)) := by
  refine ⟨uf_pull, fun x hb hp hx => ?_⟩
  rw [pull_snd] at hx ⊢
  have r := rd_tr hB h hb hp (0x100 ||| (x.s + 1).toUInt16) (Or.inl (stack_lt _)) hx
  exact ⟨hB.regs _ _ r.1, fq _ _ r.2.1, r.2.2⟩

theorem T_dummyPc {P Q : NES → Prop} (hB : IsBase B) (h : TR B P Q) : T B (fun x => P x ∧ 0x8000 ≤ x.pc) (fun x => Q x ∧ 0x8000 ≤ x.pc) (CPU.dummyPc (σ := NES)) := by
  refine ⟨fun x hx => uf_rd _ x hx, fun x hb hp hx => ?_⟩
  have r := rd_tr hB h hb hp.1 _ (Or.inr hp.2) hx
  have hv := BusStable.rdS_view x x.pc
  simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
  refine ⟨r.1, ⟨r.2.1, ?_⟩, r.2.2⟩
  show 0x8000 ≤ (rdS x x.pc).2.pc
  rw [hv.1.1]; exact hp.2

theorem T_weaken {P Q Q' : NES → Prop} {α : Type} {m : StateM NES α} (h : T B P Q m) (hw : ∀ x, Q x → Q' x) : T B P Q' m :=
  ⟨h.1, fun x hb hp hx => by
    obtain ⟨a, b, c⟩ := h.2 x hb hp hx
    exact ⟨a, hw _ b, c⟩⟩

theorem exec40_def : CPU.exec (σ := NES) 0x40 = (do
    CPU.dummyPc; CPU.dummyStack
    let v ← CPU.pull
    CPU.modRegs fun r => { r with p := (v &&& ~~~CPU.FB) ||| CPU.FU }
    let lo ← CPU.pull
    let hi ← CPU.pull
    CPU.modRegs fun r => { r with pc := lo.toUInt16 ||| (hi.toUInt16 <<< 8) }) := rfl

theorem T_rti {P0 P1 P2 P3 P4 P5 : NES → Prop} (hB : IsBase B) (t1 : TR B P0 P1) (t2 : TR B P1 P2) (t3 : TR B P2 P3) (t4 : TR B P3 P4) (t5 : TR B P4 P5)
    (f3 : RegFree P3) (f4 : RegFree P4) (f5 : RegFree P5) :
    T B (fun x => P0 x ∧ 0x8000 ≤ x.pc) P5 (CPU.exec (σ := NES) 0x40) := by
  rw [exec40_def]
  exact T_bind (T_weaken (T_dummyPc hB t1) (fun _ h => h.1)) fun _ => T_bind (T_dummyStack hB t2) fun _ => T_bind (T_pull hB t3 f3) fun v =>
    T_bind (T_regs hB f3 _) fun _ => T_bind (T_pull hB t4 f4) fun lo => T_bind (T_pull hB t5 f5) fun hi =>
    T_regs hB f5 _

/-- After an NMI's latch is cleared: vblank set, the line high, nothing pending. -/
def C (F : Nat) (x : NES) : Prop := x.vbl = true ∧ x.fpos.toNat ≤ F ∧ x.nmiLine = true ∧ x.nmiPending = false

theorem rf_c (F : Nat) : RegFree (C F) := fun _ _ h => h

theorem tr_c {F : Nat} (h2 : F ≤ 6000) : TR OnBase (C F) (C (F + 3)) := by
  rintro x r hb ⟨q1, q2, q3, q4⟩ ⟨y, hm, hv, rfl⟩ hu
  have oc : OnCyc x y := ⟨hb.sch, hb.on, hm, hv, hu⟩
  obtain ⟨_, s1, s2, s3, s4, s5, s6, _, s8⟩ := oc.base
  obtain ⟨r1, r2, r3, r4, r5, _⟩ := on_end s1 s2 hu
  obtain ⟨y1, y2⟩ := s8 q1 (by omega)
  obtain ⟨a1, a2, a3, a4⟩ := r5 y1 (by omega)
  refine ⟨⟨r1, by rw [r2, s3]; exact hb.on, by rw [r3, s4]; exact hb.dma⟩, a1, by omega, a3, ?_⟩
  rw [a4, s6, s5, q4, q3]; rfl

theorem T_push {P Q : NES → Prop} (hB : IsBase B) (h : TR B P Q) (fp : RegFree P) (v : UInt8) : T B P Q (CPU.push (σ := NES) v) := by
  refine ⟨uf_of fun x hx => wrS_mono _ _ _ hx, fun x hb hp hx => ?_⟩
  have e : (CPU.push (σ := NES) v |>.run x).2 = wrS (CPU.modRegs (σ := NES) (fun r => { r with s := x.s - 1 }) |>.run x).2 (0x100 ||| x.s.toUInt16) v := rfl
  rw [e] at hx ⊢
  have hb' := hB.regs x (fun r => { r with s := x.s - 1 }) hb
  have hp' := fp x (fun r => { r with s := x.s - 1 }) hp
  obtain ⟨o, q⟩ := h _ _ hb' hp' (onBus_wr _ _ v (stack_lt _)) hx
  have hv := BusStable.wrS_view (CPU.modRegs (σ := NES) (fun r => { r with s := x.s - 1 }) |>.run x).2 (0x100 ||| x.s.toUInt16) v
  simp only [BusStable.view, Prod.mk.injEq] at hv
  exact ⟨o, q, hv.2⟩

theorem T_rd {P Q : NES → Prop} (hB : IsBase B) (h : TR B P Q) (a : UInt16) (ha : a < 0x2000 ∨ 0x8000 ≤ a) : T B P Q (CPU.rd (σ := NES) a) :=
  ⟨uf_rd a, fun x hb hp hx => rd_tr hB h hb hp a ha hx⟩

theorem T_get {P : NES → Prop} : T B P P (CPU.getRegs (σ := NES)) := ⟨fun _ h => h, fun _ hb hp _ => ⟨hb, hp, rfl⟩⟩
theorem T_pend {P : NES → Prop} : T B P P (CPU.nmiPending (σ := NES)) := ⟨fun _ h => h, fun _ hb hp _ => ⟨hb, hp, rfl⟩⟩

theorem T_clear {F : Nat} : T OnBase (A3 F) (C F) (CPU.clearNmiPending (σ := NES)) :=
  ⟨fun _ h => h, fun x hb ⟨⟨q1, q2, q3, _⟩, _⟩ _ => ⟨⟨SchS.of_sv hb.sch ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, hb.on, hb.dma⟩, ⟨q1, q2, q3, rfl⟩, rfl⟩⟩

theorem T_interrupt {F : Nat} (hF : F ≤ 5000) : T OnBase (A3 F) (C (F + 15)) (CPU.interrupt (σ := NES) 0xFFFA false) := by
  have hv0 : ((0xFFFA : UInt16) < 0x2000 ∨ 0x8000 ≤ (0xFFFA : UInt16)) := Or.inr (by decide)
  have hv1 : ((0xFFFA : UInt16) + 1 < 0x2000 ∨ 0x8000 ≤ (0xFFFA : UInt16) + 1) := Or.inr (by decide)
  unfold CPU.interrupt
  simp only [ite_self]
  exact T_bind T_get fun _ => T_bind (T_push onIs (tr_a3 (F := F) (by omega)) (rf_a3 F) _) fun _ => T_bind (T_push onIs (tr_a3 (F := F + 3) (by omega)) (rf_a3 _) _) fun _ =>
    T_bind T_pend fun _ => T_bind T_clear fun _ => T_bind T_get fun _ => T_bind (T_push onIs (tr_c (F := F + 3 + 3) (by omega)) (rf_c _) _) fun _ =>
    T_bind (T_regs onIs (rf_c _) _) fun _ => T_bind (T_rd onIs (tr_c (by omega)) _ hv0) fun _ => T_bind (T_rd onIs (tr_c (by omega)) _ hv1) fun _ =>
    T_weaken (T_regs onIs (rf_c _) _) (fun x h => by
      obtain ⟨a, b, c, d⟩ := h
      exact ⟨a, by omega, c, d⟩)

theorem nmi_def : CPU.nmi (σ := NES) = (do CPU.dummyPc; CPU.dummyPc; CPU.interrupt 0xFFFA false) := rfl

theorem T_nmi {F : Nat} (hF : F ≤ 4000) : T OnBase (fun x => A3 F x ∧ 0x8000 ≤ x.pc) (C (F + 21)) (CPU.nmi (σ := NES)) := by
  rw [nmi_def]
  exact T_bind (T_dummyPc onIs (tr_a3 (F := F) (by omega))) fun _ =>
    T_bind (T_weaken (T_dummyPc onIs (tr_a3 (F := F + 3) (by omega))) (fun _ h => h.1)) fun _ => T_interrupt (F := F + 3 + 3) (by omega)

/-- Vblank has just started, or not: at an instruction boundary with the last poll clear. -/
def AF (F : Nat) (x : NES) : Prop := A0 x ∨ A1 F x ∨ A2 F x

theorem rf_af (F : Nat) : RegFree (AF F) := fun _ _ h => h

theorem any_of_af {F G : Nat} (hG : F ≤ G) {x : NES} (h : Any F x) (hp : x.nmiPolled = false) : AF G x := by
  rcases h with h | ⟨⟨a, b, c, d⟩, e⟩ | ⟨⟨a, b, c, d⟩, e⟩ | ⟨_, e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨⟨a, by omega, c, d⟩, e⟩)
  · exact Or.inr (Or.inr ⟨⟨a, by omega, c, d⟩, e⟩)
  · rw [hp] at e; cases e

/-- What's left of `stepTail` once the instruction has run. -/
theorem checks_cases {x : NES} (hu : (Smb.checks.run x).2.unmodelled = false) :
    x.p &&& 4 ≠ 0 ∧ x.unmodelled = false := by
  have hunf : UF (CPU.nmi (σ := NES)) := (T_nmi (F := 0) (by omega)).1
  by_cases hp : x.p &&& CPU.FI = 0
  · exfalso
    have hc : (x.p &&& CPU.FI == 0) = true := by simpa using hp
    cases hn : x.nmiPolled with
    | false =>
      have : (Smb.checks.run x).2 = { x with unmodelled := true } := by
        simp [Smb.checks, bind, StateT.bind, CPU.getRegs, CPU.nmiPolled, Bus.nmiPolled, Bus.regs, hn, hc, pure, StateT.pure, StateT.run, CPU.unsupported, Bus.unsupported]
      rw [this] at hu
      cases hu
    | true =>
      have : (Smb.checks.run x).2 = (CPU.nmi.run { x with unmodelled := true }).2 := by
        simp [Smb.checks, bind, StateT.bind, CPU.getRegs, CPU.nmiPolled, Bus.nmiPolled, Bus.regs, hn, hc, pure, StateT.pure, StateT.run, CPU.unsupported, Bus.unsupported]
      rw [this] at hu
      have := hunf _ hu
      cases this
  · refine ⟨by simpa [CPU.FI] using hp, ?_⟩
    cases hn : x.nmiPolled with
    | false =>
      rw [Abs.checks_nes_id (by simpa [CPU.FI] using hp) hn] at hu
      exact hu
    | true =>
      rw [Abs.checks_nes_nmi (by simpa [CPU.FI] using hp) hn] at hu
      exact hunf _ hu

/-- An instruction's tail, when no NMI was polled. -/
theorem step_of_clear {s : NES} (hu : (CPU.step.run s).2.unmodelled = false) (hp : (Abs.preChecks s).nmiPolled = false) : (CPU.step.run s).2 = Abs.preChecks s := by
  rw [Abs.step_eq] at hu ⊢
  exact Abs.checks_nes_id (checks_cases hu).1 hp

/-- An instruction's tail, when an NMI was polled. -/
theorem step_of_poll {s : NES} (hu : (CPU.step.run s).2.unmodelled = false) (hp : (Abs.preChecks s).nmiPolled = true) : (CPU.step.run s).2 = (CPU.nmi.run (Abs.preChecks s)).2 := by
  rw [Abs.step_eq] at hu ⊢
  exact Abs.checks_nes_nmi (checks_cases hu).1 hp

theorem pre_um {s : NES} (hu : (CPU.step.run s).2.unmodelled = false) : (Abs.preChecks s).unmodelled = false := by
  rw [Abs.step_eq] at hu
  exact (checks_cases hu).2

/-- The result of the idle loop's `jmp`. -/
theorem idle_stage {F : Nat} (hF : F ≤ 600) {s : NES} (hb : OnBase s) (hp : AF F s) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0x8057) (hu : (Abs.preChecks s).unmodelled = false) :
    OnBase (Abs.preChecks s) ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = 0x8057 ∧
      (((Abs.preChecks s).nmiPolled = false ∧ AF 600 (Abs.preChecks s)) ∨ A3 (F + 400) (Abs.preChecks s)) := by
  rcases hp with h0 | h1 | h2
  · obtain ⟨o, q, pr, c⟩ := jmp_stage (tr_any (F := 344) (by omega) (by omega)) (tr_any (F := 344 + 3) (by omega) (by omega)) (tr_any (F := 344 + 3 + 3) (by omega) (by omega))
      (rf_any _) (rf_any _) (rf_any _) (rf_any _) hb (Or.inl h0) hprg hpc hu
    refine ⟨o, pr, c, ?_⟩
    cases hn : (Abs.preChecks s).nmiPolled with
    | false => exact Or.inl ⟨rfl, any_of_af (F := 344 + 3 + 3 + 3) (by omega) q hn⟩
    | true =>
      refine Or.inr ?_
      rcases q with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨⟨a, b, c', d⟩, e⟩
      · rw [hn] at e; cases e
      · rw [hn] at e; cases e
      · rw [hn] at e; cases e
      · exact ⟨⟨a, by omega, c', d⟩, e⟩
  · obtain ⟨o, q, pr, c⟩ := jmp_stage (tr_l1 (F := F) (by omega)) (tr_l2 (F := F + 3) (by omega)) (tr_a3 (F := F + 3 + 3) (by omega))
      (rf_l1 _) (rf_l2 _) (rf_a3 _) (rf_a3 _) hb (Or.inl h1) hprg hpc hu
    obtain ⟨⟨a, b, c', d⟩, e⟩ := q
    exact ⟨o, pr, c, Or.inr ⟨⟨a, by omega, c', d⟩, e⟩⟩
  · obtain ⟨o, q, pr, c⟩ := jmp_stage (tr_l1 (F := F) (by omega)) (tr_l2 (F := F + 3) (by omega)) (tr_a3 (F := F + 3 + 3) (by omega))
      (rf_l1 _) (rf_l2 _) (rf_a3 _) (rf_a3 _) hb (Or.inr (Or.inl h2)) hprg hpc hu
    obtain ⟨⟨a, b, c', d⟩, e⟩ := q
    exact ⟨o, pr, c, Or.inr ⟨⟨a, by omega, c', d⟩, e⟩⟩

/-- `rti`, from a state where NMI generation is on. -/
theorem rti_stage {F : Nat} (hF : F ≤ 600) {s : NES} (hb : OnBase s) (hp : AF F s) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0x8181) (hu : (Abs.preChecks s).unmodelled = false) :
    OnBase (Abs.preChecks s) ∧ (Abs.preChecks s).prg = Smb.prg ∧
      (((Abs.preChecks s).nmiPolled = false ∧ AF 600 (Abs.preChecks s)) ∨ A3 (F + 400) (Abs.preChecks s)) := by
  have b0 : Smb.prg.get! ((0x8181 : UInt16) &&& 0x7FFF).toNat = 0x40 := by native_decide
  have e0 : (0x8000 : UInt16) ≤ s.pc := by rw [hpc]; decide
  have hop : (CPU.fetch.run s).1 = 0x40 := by
    rw [fetch_value s hb.dma e0, hprg, hpc]; exact b0
  have hpre : Abs.preChecks s = ((CPU.exec (σ := NES) 0x40).run (CPU.fetch.run s).2).2 := by
    rw [Abs.preChecks, hop]
  rw [hpre] at hu ⊢
  have hTa : T OnBase (fun x => Any (344 + 3) x ∧ 0x8000 ≤ x.pc) (Any (344 + 3 + 15)) (CPU.exec (σ := NES) 0x40) :=
    T_rti onIs (tr_any (F := 347) (by omega) (by omega)) (tr_any (F := 350) (by omega) (by omega)) (tr_any (F := 353) (by omega) (by omega)) (tr_any (F := 356) (by omega) (by omega)) (tr_any (F := 359) (by omega) (by omega)) (rf_any _) (rf_any _) (rf_any _)
  have hTl : T OnBase (fun x => L2 (F + 3) x ∧ 0x8000 ≤ x.pc) (A3 (F + 3 + 15)) (CPU.exec (σ := NES) 0x40) :=
    T_rti onIs (tr_l2 (F := F + 3) (by omega)) (tr_a3 (F := F + 3 + 3) (by omega)) (tr_a3 (F := F + 3 + 3 + 3) (by omega)) (tr_a3 (F := F + 3 + 3 + 3 + 3) (by omega)) (tr_a3 (F := F + 3 + 3 + 3 + 3 + 3) (by omega)) (rf_a3 _) (rf_a3 _) (rf_a3 _)
  have hu1 := hTa.1 _ hu
  rcases hp with h0 | h1 | h2
  · obtain ⟨o1, q1, c1, p1, -⟩ := fetch_tr onIs (tr_any (F := 344) (by omega) (by omega)) (rf_any _) hb (Or.inl h0) e0 hu1
    have e1 : (0x8000 : UInt16) ≤ (CPU.fetch.run s).2.pc := by rw [c1, hpc]; decide
    obtain ⟨o, q, pr⟩ := hTa.2 _ o1 ⟨q1, e1⟩ hu
    refine ⟨o, by rw [pr, p1, hprg], ?_⟩
    cases hn : ((CPU.exec (σ := NES) 0x40).run (CPU.fetch.run s).2).2.nmiPolled with
    | false => exact Or.inl ⟨rfl, any_of_af (F := 344 + 3 + 15) (G := 600) (by omega) q hn⟩
    | true =>
      refine Or.inr ?_
      rcases q with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨⟨a, b, c', d⟩, e⟩
      · rw [hn] at e; cases e
      · rw [hn] at e; cases e
      · rw [hn] at e; cases e
      · exact ⟨⟨a, by omega, c', d⟩, e⟩
  · obtain ⟨o1, q1, c1, p1, -⟩ := fetch_tr onIs (tr_l1 (F := F) (by omega)) (rf_l1 _) hb (Or.inl h1) e0 hu1
    have e1 : (0x8000 : UInt16) ≤ (CPU.fetch.run s).2.pc := by rw [c1, hpc]; decide
    obtain ⟨o, ⟨⟨a, b, c', d⟩, e⟩, pr⟩ := hTl.2 _ o1 ⟨q1, e1⟩ hu
    exact ⟨o, by rw [pr, p1, hprg], Or.inr ⟨⟨a, by omega, c', d⟩, e⟩⟩
  · obtain ⟨o1, q1, c1, p1, -⟩ := fetch_tr onIs (tr_l1 (F := F) (by omega)) (rf_l1 _) hb (Or.inr (Or.inl h2)) e0 hu1
    have e1 : (0x8000 : UInt16) ≤ (CPU.fetch.run s).2.pc := by rw [c1, hpc]; decide
    obtain ⟨o, ⟨⟨a, b, c', d⟩, e⟩, pr⟩ := hTl.2 _ o1 ⟨q1, e1⟩ hu
    exact ⟨o, by rw [pr, p1, hprg], Or.inr ⟨⟨a, by omega, c', d⟩, e⟩⟩

/-- The NMI's sequence, ending calm, far from the next event. -/
theorem nmi_calm {F : Nat} (hF : F ≤ 1000) {x : NES} (hb : OnBase x) (hp : A3 F x) (hpc : 0x8000 ≤ x.pc) (hu : (CPU.nmi.run x).2.unmodelled = false) :
    PpuCalm.Calm 48 (CPU.nmi.run x).2 ∧ (CPU.nmi.run x).2.prg = x.prg := by
  obtain ⟨o, ⟨a, b, c, d⟩, pr⟩ := (T_nmi (F := F) (by omega)).2 x hb ⟨hp, hpc⟩ hu
  exact ⟨⟨a, c, d, (nextEv_of_vbl o.sch.toSchW a).2, by omega, o.on, o.sch.dead, o.dma⟩, pr⟩

/-! ## NMI generation off -/

structure OffBase (x : NES) : Prop where
  sch : SchS x
  off : x.ctrl &&& 0x80 = 0
  dma : x.dmaPending = false

theorem offIs : IsBase OffBase := ⟨fun _ _ h => ⟨SchS.of_sv h.sch ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩, h.off, h.dma⟩, fun _ h => h.dma⟩

def OffP (F : Nat) (x : NES) : Prop := Off x F ∧ x.nmiPolled = false

theorem rf_off (F : Nat) : RegFree (OffP F) := fun _ _ h => h

theorem tr_off {F : Nat} (h1 : 344 ≤ F) (h2 : F ≤ 6000) : TR OffBase (OffP F) (OffP (F + 3)) := by
  rintro x r hb ⟨hO, _⟩ ⟨y, hm, _, rfl⟩ hu
  obtain ⟨a, b, c, d, e⟩ := off_cycle hb.sch hb.off hO h1 h2 hm hu
  exact ⟨⟨a, by rw [b]; exact hb.off, by rw [c]; exact hb.dma⟩, d, e⟩

theorem exec68_def : CPU.exec (σ := NES) 0x68 = (do CPU.dummyPc; CPU.dummyStack; CPU.setA (← CPU.pull)) := rfl

theorem T_setA {P : NES → Prop} (hB : IsBase B) (hP : RegFree P) (v : UInt8) : T B P P (CPU.setA (σ := NES) v) :=
  T_bind (T_regs hB hP _) fun _ => T_regs hB hP _

/-- `pla`, with NMI generation off. -/
theorem T_pla {F : Nat} (h1 : 344 ≤ F) (h2 : F ≤ 5000) : T OffBase (fun x => OffP F x ∧ 0x8000 ≤ x.pc) (OffP (F + 9)) (CPU.exec (σ := NES) 0x68) := by
  rw [exec68_def]
  exact T_bind (T_weaken (T_dummyPc offIs (tr_off h1 (by omega))) (fun _ h => h.1)) fun _ =>
    T_bind (T_dummyStack offIs (tr_off (F := F + 3) (by omega) (by omega))) fun _ =>
    T_bind (T_pull offIs (tr_off (F := F + 3 + 3) (by omega) (by omega)) (rf_off _)) fun v => T_setA offIs (rf_off _) v

theorem ora_eq (u : NES) : ((CPU.exec (σ := NES) 0x09).run u).2 =
    ((CPU.setA ((Bus.regs (CPU.fetch.run u).2).a ||| (CPU.fetch.run u).1)).run (CPU.fetch.run u).2).2 := rfl

theorem wr_view' (x : NES) (a : UInt16) (b : UInt8) : (wrS x a b).prg = x.prg ∧ (wrS x a b).pc = x.pc := PpuCalm.wr_view x a b

/-- The closing `sta $2000`, with bit 7 set: NMI generation turns on. A vblank already set latches an NMI, and the instruction's own last poll still reads false. -/
theorem sta_on {F : Nat} (hF : 344 ≤ F) (hF2 : F ≤ 5000) {x : NES} (hb : OffBase x) (hp : OffP F x) (v : UInt8) (hv : v &&& 0x80 ≠ 0) (hu : (wrS x 0x2000 v).unmodelled = false) :
    OnBase (wrS x 0x2000 v) ∧ AF (F + 3) (wrS x 0x2000 v) ∧ (wrS x 0x2000 v).prg = x.prg := by
  rw [wrS_eq] at hu ⊢
  obtain ⟨Y, hY⟩ : ∃ Y, Y = { beginCycle x with bus := v, padRead := 0 } := ⟨_, rfl⟩
  have hm : wrMid Y 0x2000 v = ppuRegWrite Y 0x2000 v := by simp [wrMid]
  rw [← hY, hm] at hu ⊢
  have hsv : SV Y (ppuRegWrite Y 0x2000 v) := sv_regWrite Y 0x2000 v (by decide)
  have hyu : (ppuRegWrite Y 0x2000 v).unmodelled = false := by
    cases h : (ppuRegWrite Y 0x2000 v).unmodelled with
    | false => rfl
    | true => rw [end_mono _ h] at hu; cases hu
  have hYu : Y.unmodelled = false := by
    cases h : Y.unmodelled with
    | false => rfl
    | true => rw [hsv.unm h] at hyu; cases hyu
  have hYu0 : Y.unmodelled = (beginCycle x).unmodelled := by rw [hY]
  have hbu : (beginCycle x).unmodelled = false := hYu0.symm.trans hYu
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := begin_cycle x hb.sch hbu
  have hSY : SchS Y := by
    rw [hY]; exact SchS.of_sv b1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  have hYd : Y.dead = 0 := hSY.dead
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := PpuCalm.reg0 Y v hYd
  have hSy := SchS.of_sv hSY hsv
  have hYf : Y.fpos = (beginCycle x).fpos := by rw [hY]
  have hYv : Y.vbl = (beginCycle x).vbl := by rw [hY]
  have hYl : Y.nmiLine = (beginCycle x).nmiLine := by rw [hY]
  have hYp : Y.nmiPending = (beginCycle x).nmiPending := by rw [hY]
  have hYdma : Y.dmaPending = (beginCycle x).dmaPending := by rw [hY]
  have hc' := cf (show core (ppuRegWrite Y 0x2000 v) = core { Y with ctrl := (ppuRegWrite Y 0x2000 v).ctrl } from (core_ppuRegWrite Y 0x2000 v).1)
  generalize hR : ppuRegWrite Y 0x2000 v = y at *
  have hcy : y.ctrl &&& 0x80 ≠ 0 := by rw [r1]; exact hv
  obtain ⟨hO1, hO2, hO3⟩ := hp.1
  have hly : y.nmiLine = false := by rw [r6, hYl, b2]; exact hO1
  have hpy : y.nmiPending = false := by rw [r2, hYp, b3]; exact hO2
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := on_end hSy hcy hu
  have hdm : y.dmaPending = false := by
    have : y.dmaPending = Y.dmaPending := hc'.2.2.2.2.2.2.2.2.2.1
    rw [this, hYdma, b6]; exact hb.dma
  refine ⟨⟨e1, by rw [e2]; exact hcy, by rw [e3]; exact hdm⟩, ?_, ?_⟩
  · have hpol : (endCycle y).nmiPolled = false := by rw [e4]; exact hpy
    cases hyv : y.vbl with
    | true =>
      have hbv : (beginCycle x).vbl = true := by rw [← hYv, ← r3]; exact hyv
      have hfy : y.fpos.toNat ≤ F + 1 := by
        rw [r5, hYf]
        cases hxv : x.vbl with
        | true =>
          have hb' := hO3 hxv
          rw [(b8 hxv (by omega)).2]; omega
        | false =>
          rw [b7 hxv hbv]
          have : (342 : UInt32).toNat = 342 := rfl
          omega
      obtain ⟨a1, a2, a3, a4⟩ := e5 hyv (by omega)
      exact Or.inr (Or.inr ⟨⟨a1, by omega, a3, by rw [a4, hpy, hly]; rfl⟩, hpol⟩)
    | false =>
      rcases e6 hyv hly hpy with g | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
      · exact Or.inl ⟨g, hpol⟩
      · exact Or.inr (Or.inl ⟨⟨a, by omega, c, d⟩, hpol⟩)
      · exact Or.inr (Or.inr ⟨⟨a, by omega, c, d⟩, hpol⟩)
  · have g1 : (endCycle y).prg = y.prg := (cf (core_endCycle_any y)).2.2.2.2.2.2.2.1
    have g2 : y.prg = Y.prg := hc'.2.2.2.2.2.2.2.1
    have g3 : Y.prg = (beginCycle x).prg := by rw [hY]
    have g4 : (beginCycle x).prg = x.prg := (cf (core_beginCycle x)).2.2.2.2.2.2.2.1
    rw [g1, g2, g3, g4]

/-- A cycle with nothing latched, and the line low, whatever vblank is doing. -/
def W (x : NES) : Prop := x.nmiLine = false ∧ x.nmiPending = false ∧ x.nmiPolled = false

theorem rf_w : RegFree W := fun _ _ h => h

theorem tr_w : TR OffBase W W := by
  rintro x r hb ⟨_, q, _⟩ ⟨y, hm, _, rfl⟩ hu
  obtain ⟨a, b, c, d, e, f⟩ := off_weak hb.sch hb.off q hm hu
  exact ⟨⟨a, by rw [b]; exact hb.off, by rw [c]; exact hb.dma⟩, d, e, f⟩

/-- A state with NMI generation off and nothing pending, perhaps with a DMA latched: the first fetch runs the DMA. -/
theorem first_fetch {x : NES} (hs : SchS x) (hoff : x.ctrl &&& 0x80 = 0) (hp : x.nmiPending = false) (hpc : 0x8000 ≤ x.pc) (hu : (CPU.fetch.run x).2.unmodelled = false) :
    OffBase (CPU.fetch.run x).2 ∧ W (CPU.fetch.run x).2 ∧ (CPU.fetch.run x).2.pc = x.pc + 1 ∧ (CPU.fetch.run x).2.prg = x.prg ∧ (CPU.fetch.run x).1 = x.prg.get! (x.pc &&& 0x7FFF).toNat := by
  have e : CPU.fetch.run x = rdS (CPU.modRegs (σ := NES) (fun r => { r with pc := x.pc + 1 }) |>.run x).2 x.pc := rfl
  rw [e] at hu ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = (CPU.modRegs (σ := NES) (fun r => { r with pc := x.pc + 1 }) |>.run x).2 := ⟨_, rfl⟩
  rw [← hX] at hu ⊢
  have hXpc : X.pc = x.pc + 1 := by rw [hX]; rfl
  have hXprg : X.prg = x.prg := by rw [hX]; rfl
  have hXs : SchS X := by rw [hX]; exact SchS.of_sv hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id, id⟩
  have hXc : X.ctrl &&& 0x80 = 0 := by rw [hX]; exact hoff
  have hXp : X.nmiPending = false := by rw [hX]; exact hp
  have key : ∀ Z : NES, SchS Z → Z.ctrl &&& 0x80 = 0 → Z.nmiPending = false → Z.dmaPending = false → Z.prg = x.prg → Z.pc = x.pc + 1 → (readCycle Z x.pc).2.unmodelled = false →
      OffBase (readCycle Z x.pc).2 ∧ W (readCycle Z x.pc).2 ∧ (readCycle Z x.pc).2.pc = x.pc + 1 ∧ (readCycle Z x.pc).2.prg = x.prg ∧ (readCycle Z x.pc).1 = x.prg.get! (x.pc &&& 0x7FFF).toNat := by
    intro Z z1 z2 z3 z4 z5 z6 z7
    obtain ⟨y, hm, _, hr⟩ := read_mid Z x.pc (Or.inr hpc)
    rw [hr] at z7 ⊢
    obtain ⟨a, b, c, d, e, f⟩ := off_weak z1 z2 z3 hm z7
    have hv := BusStable.readCycle_view Z x.pc
    simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
    rw [hr] at hv
    refine ⟨⟨a, by rw [b]; exact z2, by rw [c]; exact z4⟩, ⟨d, e, f⟩, by rw [hv.1.1]; exact z6, by rw [hv.2]; exact z5, ?_⟩
    rw [readCycle_rom' Z x.pc hpc, z5]
  simp only [rdS]
  simp only [rdS] at hu
  split at hu
  · rename_i hd
    rw [if_pos hd]
    have hu0 : (oamDma X x.pc).unmodelled = false := by
      cases h : (oamDma X x.pc).unmodelled with
      | false => rfl
      | true => rw [read_mono _ _ h] at hu; cases hu
    obtain ⟨c, hc⟩ := core_oamDma X x.pc hXp hXc
    have hc' := cf hc
    have hSd : SchS (oamDma X x.pc) := by
      rcases sch_oamDma X x.pc (Or.inr hXs) with h | h
      · rw [hu0] at h; cases h
      · exact h
    exact key _ hSd (by rw [hc'.2.2.2.2.2.2.2.2.1]; exact hXc) (by rw [hc'.2.2.2.2.2.2.2.2.2.2.1]; exact hXp) hc'.2.2.2.2.2.2.2.2.2.1
      (by rw [hc'.2.2.2.2.2.2.2.1]; exact hXprg) (by rw [hc'.1]; exact hXpc) hu
  · rename_i hd
    rw [if_neg hd]
    exact key X hXs hXc hXp (by simpa using hd) hXprg hXpc hu

theorem setA_view (x : NES) (v : UInt8) : ((CPU.setA v).run x).2.prg = x.prg ∧ ((CPU.setA v).run x).2.pc = x.pc ∧ ((CPU.setA v).run x).2.a = v := ⟨rfl, rfl, rfl⟩

theorem setA_unm (x : NES) (v : UInt8) : ((CPU.setA v).run x).2.unmodelled = x.unmodelled := rfl

theorem fetch_value2 (x : NES) (hpc : 0x8000 ≤ x.pc) : (CPU.fetch.run x).1 = x.prg.get! (x.pc &&& 0x7FFF).toNat := by
  have hv1 : (CPU.fetch.run x).1 = (rdS (CPU.modRegs (σ := NES) (fun r => { r with pc := x.pc + 1 }) |>.run x).2 x.pc).1 := rfl
  rw [hv1]
  simp only [rdS]
  rw [readCycle_rom' _ _ hpc]
  split
  · have hv := BusStable.oamDma_view (CPU.modRegs (σ := NES) (fun r => { r with pc := x.pc + 1 }) |>.run x).2 x.pc
    simp only [BusStable.view, Prod.mk.injEq] at hv
    rw [hv.2]
    rfl
  · rfl

theorem ad_mono (x : NES) (h : x.unmodelled = true) : ((CPU.exec (σ := NES) 0xAD).run x).2.unmodelled = true := by
  rw [PpuCalm.ad_eq]
  have e := PpuCalm.fetch16_eq x
  have h1 : (CPU.fetch16.run x).2.unmodelled = true := by
    have := uf_fetch16 x
    cases hc : (CPU.fetch16.run x).2.unmodelled with
    | true => rfl
    | false => rw [this hc] at h; cases h
  exact rdS_mono _ _ h1

theorem lda_core {u : NES} (o : OffBase u) (w : W u) (hpc : u.pc = 0x8179) (hprg : u.prg = Smb.prg) (hu : ((CPU.exec (σ := NES) 0xAD).run u).2.unmodelled = false) :
    OffBase ((CPU.exec (σ := NES) 0xAD).run u).2 ∧ OffP 344 ((CPU.exec (σ := NES) 0xAD).run u).2 ∧ ((CPU.exec (σ := NES) 0xAD).run u).2.prg = Smb.prg ∧ ((CPU.exec (σ := NES) 0xAD).run u).2.pc = 0x817B := by
  have b0 : Smb.prg.get! ((0x8179 : UInt16) &&& 0x7FFF).toNat = 0x02 ∧ Smb.prg.get! ((0x817A : UInt16) &&& 0x7FFF).toNat = 0x20 := by native_decide
  rw [PpuCalm.ad_eq] at hu ⊢
  have e := PpuCalm.fetch16_eq u
  generalize hF : CPU.fetch16.run u = F at hu ⊢
  rw [hF] at e
  generalize hv1 : CPU.fetch.run u = v1 at e
  generalize hv2 : CPU.fetch.run v1.2 = v2 at e
  subst e
  simp only at hu ⊢
  generalize hR : rdS v2.2 (Abs.base v1.1 v2.1) = R at hu ⊢
  have hu3 : v2.2.unmodelled = false := by
    cases h : v2.2.unmodelled with
    | false => rfl
    | true => rw [← hR] at hu; rw [show ((CPU.setA (rdS v2.2 (Abs.base v1.1 v2.1)).1).run (rdS v2.2 (Abs.base v1.1 v2.1)).2).2.unmodelled = (rdS v2.2 (Abs.base v1.1 v2.1)).2.unmodelled from rfl, rdS_mono _ _ h] at hu; cases hu
  have hu2 : v1.2.unmodelled = false := by
    have := uf_fetch v1.2 (by rw [hv2]; exact hu3)
    exact this
  have hu1 : (CPU.fetch.run u).2.unmodelled = false := by rw [hv1]; exact hu2
  have e1 : (0x8000 : UInt16) ≤ u.pc := by rw [hpc]; decide
  obtain ⟨o2, q2, c2, p2, v2'⟩ := fetch_tr offIs tr_w rf_w o w e1 hu1
  rw [hv1] at o2 q2 c2 p2 v2'
  have e2 : (0x8000 : UInt16) ≤ v1.2.pc := by rw [c2, hpc]; decide
  obtain ⟨o3, q3, c3, p3, v3'⟩ := fetch_tr offIs tr_w rf_w o2 q2 e2 (by rw [hv2]; exact hu3)
  rw [hv2] at o3 q3 c3 p3 v3'
  have hval : Abs.base v1.1 v2.1 = 0x2002 := by
    rw [v2', v3', p2, c2, hprg, hpc]
    have g2 : ((0x8179 : UInt16) + 1 &&& 0x7FFF) = ((0x817A : UInt16) &&& 0x7FFF) := by decide
    rw [g2, b0.1, b0.2]
    decide
  rw [hval, rdS_nodma _ _ o3.dma] at hR
  subst hR
  have hU : (readCycle v2.2 0x2002).2.unmodelled = false := by
    have e' := setA_unm (readCycle v2.2 0x2002).2 (readCycle v2.2 0x2002).1
    rw [e'] at hu; exact hu
  obtain ⟨r1, r2, r3, r4, r5⟩ := read2002 o3.sch o3.off q3.2.1 hU
  have hv := BusStable.readCycle_view v2.2 0x2002
  simp only [BusStable.view, Prod.mk.injEq, Regs.mk.injEq] at hv
  obtain ⟨sv1, sv2, sv3⟩ := setA_view (readCycle v2.2 0x2002).2 (readCycle v2.2 0x2002).1
  have T1 := (T_setA offIs (rf_off 344) (readCycle v2.2 0x2002).1).2 (readCycle v2.2 0x2002).2 ⟨r1, by rw [r2]; exact o3.off, by rw [r3]; exact o3.dma⟩ ⟨r4, r5⟩ hu
  refine ⟨T1.1, T1.2.1, ?_, ?_⟩
  · rw [sv1, hv.2, p3, p2, hprg]
  · rw [sv2, hv.1.1, c3, c2, hpc]; decide

/-- `lda $2002`: vblank is cleared, so any vblank set afterwards is a fresh one. -/
theorem z8178 {s : NES} (hs : SchS s) (hoff : s.ctrl &&& 0x80 = 0) (hp : s.nmiPending = false) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0x8178) (hu : (Abs.preChecks s).unmodelled = false) :
    OffBase (Abs.preChecks s) ∧ OffP 344 (Abs.preChecks s) ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = 0x817B := by
  have b0 : Smb.prg.get! ((0x8178 : UInt16) &&& 0x7FFF).toNat = 0xAD := by native_decide
  have e0 : (0x8000 : UInt16) ≤ s.pc := by rw [hpc]; decide
  have hop : (CPU.fetch.run s).1 = 0xAD := by
    rw [fetch_value2 s e0, hprg, hpc]; exact b0
  have hpre : Abs.preChecks s = ((CPU.exec (σ := NES) 0xAD).run (CPU.fetch.run s).2).2 := by
    rw [Abs.preChecks, hop]
  rw [hpre] at hu ⊢
  have hu1 : (CPU.fetch.run s).2.unmodelled = false := by
    cases h : (CPU.fetch.run s).2.unmodelled with
    | false => rfl
    | true =>
      have := ad_mono (CPU.fetch.run s).2 h
      rw [this] at hu; cases hu
  obtain ⟨o1, q1, c1, p1, _⟩ := first_fetch hs hoff hp e0 hu1
  exact lda_core o1 q1 (by rw [c1, hpc]; decide) (by rw [p1, hprg]) hu

/-- A program that keeps the program counter. -/
def KP {α : Type} (m : StateM NES α) : Prop := ∀ x, (m.run x).2.pc = x.pc

theorem KP_bind {α β : Type} {m : StateM NES α} {f : α → StateM NES β} (hm : KP m) (hf : ∀ a, KP (f a)) : KP (m >>= f) := by
  intro x
  rw [Sim.run_bind, hf, hm]

theorem kp_pla : KP (CPU.exec (σ := NES) 0x68) := by
  rw [exec68_def]
  refine KP_bind (fun x => (PpuCalm.rd_view x x.pc).2) fun _ => KP_bind (fun x => (PpuCalm.rd_view x _).2) fun _ => KP_bind ?_ fun v => fun _ => rfl
  intro x
  rw [pull_snd]
  exact (PpuCalm.rd_view x _).2

theorem off_fetch {F : Nat} (h1 : 344 ≤ F) (h2 : F ≤ 6000) {x : NES} (hb : OffBase x) (hp : OffP F x) (hpc : 0x8000 ≤ x.pc) (hu : (CPU.fetch.run x).2.unmodelled = false) :
    OffBase (CPU.fetch.run x).2 ∧ OffP (F + 3) (CPU.fetch.run x).2 ∧ (CPU.fetch.run x).2.pc = x.pc + 1 ∧ (CPU.fetch.run x).2.prg = x.prg ∧
      (CPU.fetch.run x).1 = x.prg.get! (x.pc &&& 0x7FFF).toNat :=
  fetch_tr offIs (tr_off h1 h2) (rf_off _) hb hp hpc hu

/-- `pla`. -/
theorem z817B {s : NES} (hb : OffBase s) (hp : OffP 344 s) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0x817B) (hu : (Abs.preChecks s).unmodelled = false) :
    OffBase (Abs.preChecks s) ∧ OffP 356 (Abs.preChecks s) ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = 0x817C := by
  have b0 : Smb.prg.get! ((0x817B : UInt16) &&& 0x7FFF).toNat = 0x68 := by native_decide
  have e0 : (0x8000 : UInt16) ≤ s.pc := by rw [hpc]; decide
  have hop : (CPU.fetch.run s).1 = 0x68 := by
    rw [fetch_value2 s e0, hprg, hpc]; exact b0
  have hpre : Abs.preChecks s = ((CPU.exec (σ := NES) 0x68).run (CPU.fetch.run s).2).2 := by
    rw [Abs.preChecks, hop]
  rw [hpre] at hu ⊢
  have Tp := T_pla (F := 344 + 3) (by omega) (by omega)
  obtain ⟨o1, q1, c1, p1, _⟩ := off_fetch (by omega) (by omega) hb hp e0 (Tp.1 _ hu)
  have e1 : (0x8000 : UInt16) ≤ (CPU.fetch.run s).2.pc := by rw [c1, hpc]; decide
  obtain ⟨a, b, c⟩ := Tp.2 _ o1 ⟨q1, e1⟩ hu
  refine ⟨a, b, by rw [c, p1, hprg], ?_⟩
  rw [kp_pla, c1, hpc]; decide

theorem ora_bit (a : UInt8) : (a ||| 0x80) &&& 0x80 ≠ 0 := by bv_decide (config := { enums := false })

theorem ora_core {u : NES} (o : OffBase u) (w : OffP 359 u) (hpc : u.pc = 0x817D) (hprg : u.prg = Smb.prg) (hu : ((CPU.exec (σ := NES) 0x09).run u).2.unmodelled = false) :
    OffBase ((CPU.exec (σ := NES) 0x09).run u).2 ∧ OffP 362 ((CPU.exec (σ := NES) 0x09).run u).2 ∧ ((CPU.exec (σ := NES) 0x09).run u).2.prg = Smb.prg ∧ ((CPU.exec (σ := NES) 0x09).run u).2.pc = 0x817E ∧
      ((CPU.exec (σ := NES) 0x09).run u).2.a &&& 0x80 ≠ 0 := by
  have b0 : Smb.prg.get! ((0x817D : UInt16) &&& 0x7FFF).toNat = 0x80 := by native_decide
  rw [ora_eq] at hu ⊢
  generalize hv : CPU.fetch.run u = v at hu ⊢
  have hu1 : v.2.unmodelled = false := by rw [setA_unm] at hu; exact hu
  have e0 : (0x8000 : UInt16) ≤ u.pc := by rw [hpc]; decide
  obtain ⟨o1, q1, c1, p1, val⟩ := off_fetch (by omega) (by omega) o w e0 (by rw [hv]; exact hu1)
  rw [hv] at o1 q1 c1 p1 val
  obtain ⟨sv1, sv2, sv3⟩ := setA_view v.2 ((Bus.regs v.2).a ||| v.1)
  have T1 := (T_setA offIs (rf_off (359 + 3)) ((Bus.regs v.2).a ||| v.1)).2 v.2 o1 q1 hu
  refine ⟨T1.1, T1.2.1, ?_, ?_, ?_⟩
  · rw [sv1, p1, hprg]
  · rw [sv2, c1, hpc]; decide
  · rw [sv3, val, hprg, hpc, b0]; exact ora_bit _

theorem ora_mono (x : NES) (h : x.unmodelled = true) : ((CPU.exec (σ := NES) 0x09).run x).2.unmodelled = true := by
  rw [ora_eq, setA_unm]
  cases hc : (CPU.fetch.run x).2.unmodelled with
  | true => rfl
  | false => rw [uf_fetch x hc] at h; cases h

/-- `ora #$80`. -/
theorem z817C {s : NES} (hb : OffBase s) (hp : OffP 356 s) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0x817C) (hu : (Abs.preChecks s).unmodelled = false) :
    OffBase (Abs.preChecks s) ∧ OffP 362 (Abs.preChecks s) ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = 0x817E ∧ (Abs.preChecks s).a &&& 0x80 ≠ 0 := by
  have b0 : Smb.prg.get! ((0x817C : UInt16) &&& 0x7FFF).toNat = 0x09 := by native_decide
  have e0 : (0x8000 : UInt16) ≤ s.pc := by rw [hpc]; decide
  have hop : (CPU.fetch.run s).1 = 0x09 := by
    rw [fetch_value2 s e0, hprg, hpc]; exact b0
  have hpre : Abs.preChecks s = ((CPU.exec (σ := NES) 0x09).run (CPU.fetch.run s).2).2 := by
    rw [Abs.preChecks, hop]
  rw [hpre] at hu ⊢
  have hu1 : (CPU.fetch.run s).2.unmodelled = false := by
    cases h : (CPU.fetch.run s).2.unmodelled with
    | false => rfl
    | true => rw [ora_mono _ h] at hu; cases hu
  obtain ⟨o1, q1, c1, p1, _⟩ := off_fetch (by omega) (by omega) hb hp e0 hu1
  exact ora_core o1 q1 (by rw [c1, hpc]; decide) (by rw [p1, hprg]) hu

theorem sta_core {u : NES} (o : OffBase u) (w : OffP 365 u) (hpc : u.pc = 0x817F) (hprg : u.prg = Smb.prg) (ha : u.a &&& 0x80 ≠ 0) (hu : ((CPU.exec (σ := NES) 0x8D).run u).2.unmodelled = false) :
    OnBase ((CPU.exec (σ := NES) 0x8D).run u).2 ∧ AF 374 ((CPU.exec (σ := NES) 0x8D).run u).2 ∧ ((CPU.exec (σ := NES) 0x8D).run u).2.prg = Smb.prg ∧ ((CPU.exec (σ := NES) 0x8D).run u).2.pc = 0x8181 := by
  have b0 : Smb.prg.get! ((0x817F : UInt16) &&& 0x7FFF).toNat = 0x00 ∧ Smb.prg.get! ((0x8180 : UInt16) &&& 0x7FFF).toNat = 0x20 := by native_decide
  rw [Abs.exec8d_eq] at hu ⊢
  have e := PpuCalm.fetch16_eq u
  have ea1 := PpuCalm.fetch_a u
  generalize hF : CPU.fetch16.run u = F at hu ⊢
  rw [hF] at e
  generalize hv1 : CPU.fetch.run u = v1 at e ea1
  have ea2 := PpuCalm.fetch_a v1.2
  generalize hv2 : CPU.fetch.run v1.2 = v2 at e ea2
  subst e
  simp only at hu ⊢
  have hu3 : v2.2.unmodelled = false := by
    cases h : v2.2.unmodelled with
    | false => rfl
    | true => rw [wrS_mono _ _ _ h] at hu; cases hu
  have hu2 : v1.2.unmodelled = false := uf_fetch v1.2 (by rw [hv2]; exact hu3)
  have e1 : (0x8000 : UInt16) ≤ u.pc := by rw [hpc]; decide
  obtain ⟨o2, q2, c2, p2, v2'⟩ := off_fetch (by omega) (by omega) o w e1 (by rw [hv1]; exact hu2)
  rw [hv1] at o2 q2 c2 p2 v2'
  have e2 : (0x8000 : UInt16) ≤ v1.2.pc := by rw [c2, hpc]; decide
  obtain ⟨o3, q3, c3, p3, v3'⟩ := off_fetch (by omega) (by omega) o2 q2 e2 (by rw [hv2]; exact hu3)
  rw [hv2] at o3 q3 c3 p3 v3'
  have hval : Abs.base v1.1 v2.1 = 0x2000 := by
    rw [v2', v3', p2, c2, hprg, hpc]
    have g2 : ((0x817F : UInt16) + 1 &&& 0x7FFF) = ((0x8180 : UInt16) &&& 0x7FFF) := by decide
    rw [g2, b0.1, b0.2]
    decide
  rw [hval] at hu ⊢
  have hA : (Bus.regs v2.2).a = u.a := by rw [PpuCalm.regs_a, ea2, ea1]
  rw [hA] at hu ⊢
  obtain ⟨a, b, c⟩ := sta_on (F := 365 + 3 + 3) (by omega) (by omega) o3 q3 u.a ha hu
  obtain ⟨v1', v2''⟩ := wr_view' v2.2 0x2000 u.a
  refine ⟨a, b, ?_, ?_⟩
  · rw [v1', p3, p2, hprg]
  · rw [v2'', c3, c2, hpc]; decide

theorem sta_mono (x : NES) (h : x.unmodelled = true) : ((CPU.exec (σ := NES) 0x8D).run x).2.unmodelled = true := by
  rw [Abs.exec8d_eq]
  apply wrS_mono
  cases hc : (CPU.fetch16.run x).2.unmodelled with
  | true => rfl
  | false => rw [uf_fetch16 x hc] at h; cases h

/-- `sta $2000`, NMI generation on. -/
theorem z817E {s : NES} (hb : OffBase s) (hp : OffP 362 s) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0x817E) (ha : s.a &&& 0x80 ≠ 0) (hu : (Abs.preChecks s).unmodelled = false) :
    OnBase (Abs.preChecks s) ∧ AF 374 (Abs.preChecks s) ∧ (Abs.preChecks s).prg = Smb.prg ∧ (Abs.preChecks s).pc = 0x8181 := by
  have b0 : Smb.prg.get! ((0x817E : UInt16) &&& 0x7FFF).toNat = 0x8D := by native_decide
  have e0 : (0x8000 : UInt16) ≤ s.pc := by rw [hpc]; decide
  have hop : (CPU.fetch.run s).1 = 0x8D := by
    rw [fetch_value2 s e0, hprg, hpc]; exact b0
  have hpre : Abs.preChecks s = ((CPU.exec (σ := NES) 0x8D).run (CPU.fetch.run s).2).2 := by
    rw [Abs.preChecks, hop]
  rw [hpre] at hu ⊢
  have hu1 : (CPU.fetch.run s).2.unmodelled = false := by
    cases h : (CPU.fetch.run s).2.unmodelled with
    | false => rfl
    | true => rw [sta_mono _ h] at hu; cases hu
  obtain ⟨o1, q1, c1, p1, _⟩ := off_fetch (by omega) (by omega) hb hp e0 hu1
  exact sta_core o1 q1 (by rw [c1, hpc]; decide) (by rw [p1, hprg]) (by rw [PpuCalm.fetch_a]; exact ha) hu

/-! ## The NMI's target -/

theorem T_bind_v {α β : Type} {P Q R : NES → Prop} {m : StateM NES α} {f : α → StateM NES β} {v : α} (hm : T B P Q m) (hv : ∀ x, B x → P x → (m.run x).1 = v)
    (hu : ∀ a, UF (f a)) (hf : T B Q R (f v)) : T B P R (m >>= f) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Sim.run_bind] at hx
    exact hm.1 x (hu _ _ hx)
  · intro x hb hp hx
    rw [Sim.run_bind] at hx ⊢
    obtain ⟨o, q, pr⟩ := hm.2 x hb hp (hu _ _ hx)
    rw [hv x hb hp] at hx ⊢
    obtain ⟨o2, q2, pr2⟩ := hf.2 _ o q hx
    exact ⟨o2, q2, pr2.trans pr⟩

/-- `T`, with the ROM in the predicates. -/
theorem T_prg {α : Type} {P Q : NES → Prop} {m : StateM NES α} (h : T B P Q m) : T B (fun x => P x ∧ x.prg = Smb.prg) (fun x => Q x ∧ x.prg = Smb.prg) m :=
  ⟨h.1, fun x hb hp hx => by
    obtain ⟨a, b, c⟩ := h.2 x hb hp.1 hx
    exact ⟨a, ⟨b, c.trans hp.2⟩, c⟩⟩

theorem rd_val {x : NES} (hd : x.dmaPending = false) (a : UInt16) (h : 0x8000 ≤ a) : (rdS x a).1 = x.prg.get! (a &&& 0x7FFF).toNat := by
  rw [rdS_nodma _ _ hd]
  exact readCycle_rom' _ _ h

theorem vec_bytes : Smb.prg.get! ((0xFFFA : UInt16) &&& 0x7FFF).toNat = 0x82 ∧ Smb.prg.get! (((0xFFFA : UInt16) + 1) &&& 0x7FFF).toNat = 0x80 := by native_decide

theorem T_interrupt_pc {F : Nat} (hF : F ≤ 5000) : T OnBase (fun x => A3 F x ∧ x.prg = Smb.prg) (fun x => C (F + 15) x ∧ x.pc = 0x8082) (CPU.interrupt (σ := NES) 0xFFFA false) := by
  have hv0 : ((0xFFFA : UInt16) < 0x2000 ∨ 0x8000 ≤ (0xFFFA : UInt16)) := Or.inr (by decide)
  have hv1 : ((0xFFFA : UInt16) + 1 < 0x2000 ∨ 0x8000 ≤ (0xFFFA : UInt16) + 1) := Or.inr (by decide)
  have rf_cp : ∀ G, RegFree (fun x => C G x ∧ x.prg = Smb.prg) := fun _ _ _ h => h
  unfold CPU.interrupt
  simp only [ite_self]
  exact T_bind (T_prg T_get) fun _ => T_bind (T_prg (T_push onIs (tr_a3 (F := F) (by omega)) (rf_a3 F) _)) fun _ => T_bind (T_prg (T_push onIs (tr_a3 (F := F + 3) (by omega)) (rf_a3 _) _)) fun _ =>
    T_bind (T_prg T_pend) fun _ => T_bind (T_prg T_clear) fun _ => T_bind (T_prg T_get) fun _ => T_bind (T_prg (T_push onIs (tr_c (F := F + 3 + 3) (by omega)) (rf_c _) _)) fun _ =>
    T_bind (T_regs onIs (rf_cp _) _) fun _ =>
    T_bind_v (v := 0x82) (T_prg (T_rd onIs (tr_c (F := F + 3 + 3 + 3) (by omega)) _ hv0))
      (fun x hb hp => by
        have := rd_val hb.dma 0xFFFA (by decide)
        rw [hp.2, vec_bytes.1] at this
        exact this)
      (fun _ => (T_bind (T_rd onIs (tr_c (F := 0) (by omega)) _ hv1) fun _ => T_regs onIs (rf_c _) _).1)
      (T_bind_v (v := 0x80) (T_prg (T_rd onIs (tr_c (F := F + 3 + 3 + 3 + 3) (by omega)) _ hv1))
        (fun x hb hp => by
          have := rd_val hb.dma ((0xFFFA : UInt16) + 1) (by decide)
          rw [hp.2, vec_bytes.2] at this
          exact this)
        (fun _ _ h => h)
        ⟨fun _ h => h, fun x hb hp _ => ⟨onIs.regs x _ hb, ⟨hp.1, rfl⟩, rfl⟩⟩)

theorem nmi_pc {F : Nat} (hF : F ≤ 1000) {x : NES} (hb : OnBase x) (hp : A3 F x) (hpc : 0x8000 ≤ x.pc) (hprg : x.prg = Smb.prg) (hu : (CPU.nmi.run x).2.unmodelled = false) :
    (CPU.nmi.run x).2.pc = 0x8082 := by
  have Tn : T OnBase (fun x => (A3 F x ∧ 0x8000 ≤ x.pc) ∧ x.prg = Smb.prg) (fun x => C (F + 3 + 3 + 15) x ∧ x.pc = 0x8082) (CPU.nmi (σ := NES)) := by
    rw [nmi_def]
    exact T_bind (T_prg (T_dummyPc onIs (tr_a3 (F := F) (by omega)))) fun _ =>
      T_bind (T_weaken (T_prg (T_dummyPc onIs (tr_a3 (F := F + 3) (by omega)))) (fun _ h => ⟨h.1.1, h.2⟩)) fun _ => T_interrupt_pc (F := F + 3 + 3) (by omega)
  exact (Tn.2 x hb ⟨⟨hp, hpc⟩, hprg⟩ hu).2.1.2

/-! ## From the game logic's return to the handler's entry -/

/-- Where the machine can be between the game logic's return and the next `$808F`. -/
def ZStage (s : NES) : Prop :=
  s.prg = Smb.prg ∧
    ((s.pc = 0x8178 ∧ SchS s ∧ s.ctrl &&& 0x80 = 0 ∧ s.nmiPending = false) ∨
     (s.pc = 0x817B ∧ OffBase s ∧ OffP 344 s) ∨
     (s.pc = 0x817C ∧ OffBase s ∧ OffP 356 s) ∨
     (s.pc = 0x817E ∧ OffBase s ∧ OffP 362 s ∧ s.a &&& 0x80 ≠ 0) ∨
     (s.pc = 0x8181 ∧ OnBase s ∧ AF 374 s) ∨
     (s.pc = 0x8057 ∧ OnBase s ∧ AF 600 s) ∨
     PpuCalm.PreCalm s)

theorem af_polled {F : Nat} {x : NES} (h : AF F x) : x.nmiPolled = false := by
  rcases h with h | h | h
  · exact h.2
  · exact h.2
  · exact h.2

theorem A3_polled {F : Nat} {x : NES} (h : A3 F x) : x.nmiPolled = true := h.2

theorem guard_not {s : NES} {pc : UInt16} (hpc : s.pc = pc) (h : Abs.preamblePC pc = false) : Abs.Guard s := by
  intro hg
  rw [hpc, h] at hg
  cases hg

theorem zs_on {F : Nat} (hF : F ≤ 1000) {s : NES} (hu : (CPU.step.run s).2.unmodelled = false) (hb : OnBase (Abs.preChecks s)) (hprg : (Abs.preChecks s).prg = Smb.prg) (hpc : (Abs.preChecks s).pc = 0x8057)
    (h : ((Abs.preChecks s).nmiPolled = false ∧ AF 600 (Abs.preChecks s)) ∨ A3 F (Abs.preChecks s)) : ZStage (CPU.step.run s).2 := by
  rcases h with ⟨h1, h2⟩ | h
  · rw [step_of_clear hu h1]
    exact ⟨hprg, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpc, hb, h2⟩)))))⟩
  · have hP : (Abs.preChecks s).nmiPolled = true := A3_polled h
    have es := step_of_poll hu hP
    rw [es] at hu ⊢
    have e0 : (0x8000 : UInt16) ≤ (Abs.preChecks s).pc := by rw [hpc]; decide
    generalize Abs.preChecks s = x at hb hprg hpc h e0 hu ⊢
    obtain ⟨c, p⟩ := nmi_calm hF hb h e0 hu
    have pr : (CPU.nmi.run x).2.prg = Smb.prg := p.trans hprg
    exact ⟨pr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨pr, Or.inl ⟨nmi_pc hF hb h e0 hprg hu, c⟩⟩)))))⟩

/-- One step of the closing sequence: `Guard` holds at every state of it, and the next state is
still in it unless the handler's body has been reached. The `rti`'s target is a hypothesis, since
it depends on the stack, which the checker's table knows about. -/
theorem zs_step {s : NES} (hz : ZStage s) (hu : (CPU.step.run s).2.unmodelled = false) (hrti : s.pc = 0x8181 → (Abs.preChecks s).pc = 0x8057) :
    Abs.Guard s ∧ (ZStage (CPU.step.run s).2 ∨ (CPU.step.run s).2.pc = 0x808F) := by
  have hu' := pre_um hu
  obtain ⟨hprg, h0 | h1 | h2 | h3 | h4 | h5 | h6⟩ := hz
  · obtain ⟨hpc, hs, hoff, hp⟩ := h0
    obtain ⟨a, b, c, d⟩ := z8178 hs hoff hp hprg hpc hu'
    refine ⟨guard_not hpc (by decide), Or.inl ?_⟩
    rw [step_of_clear hu b.2]
    exact ⟨c, Or.inr (Or.inl ⟨d, a, b⟩)⟩
  · obtain ⟨hpc, hb, hO⟩ := h1
    obtain ⟨a, b, c, d⟩ := z817B hb hO hprg hpc hu'
    refine ⟨guard_not hpc (by decide), Or.inl ?_⟩
    rw [step_of_clear hu b.2]
    exact ⟨c, Or.inr (Or.inr (Or.inl ⟨d, a, b⟩))⟩
  · obtain ⟨hpc, hb, hO⟩ := h2
    obtain ⟨a, b, c, d, e⟩ := z817C hb hO hprg hpc hu'
    refine ⟨guard_not hpc (by decide), Or.inl ?_⟩
    rw [step_of_clear hu b.2]
    exact ⟨c, Or.inr (Or.inr (Or.inr (Or.inl ⟨d, a, b, e⟩)))⟩
  · obtain ⟨hpc, hb, hO, ha⟩ := h3
    obtain ⟨a, b, c, d⟩ := z817E hb hO hprg hpc ha hu'
    refine ⟨guard_not hpc (by decide), Or.inl ?_⟩
    rw [step_of_clear hu (af_polled b)]
    exact ⟨c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, a, b⟩))))⟩
  · obtain ⟨hpc, hb, hO⟩ := h4
    obtain ⟨a, b, c⟩ := rti_stage (by omega) hb hO hprg hpc hu'
    exact ⟨guard_not hpc (by decide), Or.inl (zs_on (F := 374 + 400) (by omega) hu a b (hrti hpc) c)⟩
  · obtain ⟨hpc, hb, hO⟩ := h5
    obtain ⟨a, b, d, c⟩ := idle_stage (by omega) hb hO hprg hpc hu'
    exact ⟨guard_not hpc (by decide), Or.inl (zs_on (F := 600 + 400) (by omega) hu a b d c)⟩
  · have hG := PpuCalm.guard_of_preCalm h6
    refine ⟨hG, ?_⟩
    obtain ⟨_, h0 | h1 | h2 | h3 | h4⟩ := h6
    · obtain ⟨hpc, hc⟩ := h0
      obtain ⟨c, pol, pr, pc⟩ := PpuCalm.stage0 hc hprg hpc
      rw [step_of_clear hu pol]
      exact Or.inl ⟨pr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨pr, Or.inr (Or.inl ⟨pc, c⟩)⟩)))))⟩
    · obtain ⟨hpc, hc⟩ := h1
      obtain ⟨c, pol, pr, pc⟩ := PpuCalm.stage1 30 hc hprg _ hpc (by decide) (by decide) PpuCalm.b1
      rw [step_of_clear hu pol]
      exact Or.inl ⟨pr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨pr, Or.inr (Or.inr (Or.inl ⟨pc, c⟩))⟩)))))⟩
    · obtain ⟨hpc, hc⟩ := h2
      obtain ⟨c, pol, pr, pc⟩ := PpuCalm.stage2 hc hprg hpc
      rw [step_of_clear hu pol]
      exact Or.inl ⟨pr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨pr, Or.inr (Or.inr (Or.inr (Or.inl ⟨pc, c⟩)))⟩)))))⟩
    · obtain ⟨hpc, hc⟩ := h3
      obtain ⟨c, pol, pr, pc⟩ := PpuCalm.stage1 12 hc hprg _ hpc (by decide) (by decide) PpuCalm.b3
      rw [step_of_clear hu pol]
      exact Or.inl ⟨pr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨pr, Or.inr (Or.inr (Or.inr (Or.inr ⟨pc, c⟩)))⟩)))))⟩
    · obtain ⟨hpc, hc⟩ := h4
      obtain ⟨pol, _, _, pc⟩ := PpuCalm.stage4 hc hprg hpc
      rw [step_of_clear hu pol]
      exact Or.inr pc

end Smb.Routine.PpuFrame
