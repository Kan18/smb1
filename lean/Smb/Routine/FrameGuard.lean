import Smb.Routine.PpuFrame
import Smb.Routine.PpuSchedExec

/-!
# Regions without `Guard`

`Guard` asks that no NMI arrives during the handler's first instructions. It follows from the machine itself: the regions' invariant, carried with the PPU's event schedule, the ROM, and
the closing sequence of `PpuFrame`, gives `Guard` at every step, for any controller input and any PPU timing.

The hypothesis left in its place: the run never sets `unmodelled`, the flag for hardware the model doesn't cover. That can be read off any given run. The ROM's own timing isn't assumed.

One region, `Z`, has to hold the closing sequence: it's entered only at `$8178`, it's left at `$808F`, and no other region has a box at a preamble address.
-/
namespace Smb.Routine.FrameGuard
open Smb NES Smb.Abs Smb.Routine.PpuFrame

/-- With NMI generation on, the `rti`'s target is the one the box's stack says. -/
theorem ginv_rti_pc {rom : UInt16 → UInt8} {exit prot : UInt16 → Bool} {g : Global} {T : Table} {ram0 : UInt16 → UInt8} {s : NES}
    (hchk : checkF rom exit prot g T = true) (hx : exit s.pc = false) (hi : GInv rom prot g ram0 T s) (hpc : s.pc = rtiPC) (hctl : s.ctrl &&& 0x80 ≠ 0) :
    (preChecks s).pc = idlePC := by
  obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := hi
  have hr : RelOn s t := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact absurd h1.ctrl hctl
    · exact h1
  have hspc : s.pc = t.regs.pc := congrArg Regs.pc hr.regs
  have hbpc : b.pc = t.regs.pc := hb.pc.symm
  have h3 : b.pc = rtiPC := by rw [hbpc, ← hspc, hpc]
  have hbx := check_box hchk hbm
  unfold boxF checkAny at hbx
  have hxb : exit b.pc = false := by rw [hbpc, ← hspc]; exact hx
  rw [hxb, Bool.false_or] at hbx
  have ne1 : (rtiPC == onEnter) = false := by decide
  have ne2 : (rtiPC == onExit) = false := by decide
  rw [h3] at hbx
  simp only [ne1, ne2, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true, Bool.and_eq_true] at hbx
  obtain ⟨hck, hr2⟩ := hbx
  simp only [rtiToIdle, Bool.and_eq_true] at hr2
  obtain ⟨⟨hop, hlo⟩, hhi⟩ := hr2
  have h0 : 0x8000 ≤ t.regs.pc := by rw [← hbpc, h3]; decide
  have hop' : t.prg (t.regs.pc &&& 0x7FFF) = 0x40 := by
    rw [hc _ h0, ← hbpc]; simpa using hop
  obtain ⟨_, _, _, hcb⟩ := inv_step_box hck hc hb
  obtain ⟨hrel', _, _⟩ := on_plain hr h0 (Or.inl hop') hcb.bad
  have e : (preChecks s).pc = (plainExec t).regs.pc := congrArg Regs.pc hrel'.regs
  rw [e, plainExec_op h0 hop', pc_40]
  show base (Plain.memRead t.ram t.prg (0x100 ||| (t.regs.s + 1 + 1).toUInt16)) (Plain.memRead t.ram t.prg (0x100 ||| (t.regs.s + 1 + 1 + 1).toUInt16)) = _
  have e1 : t.regs.s + 1 + 1 = b.s + 2 := by rw [hb.sp]; bv_decide (config := { enums := false })
  have e2 : t.regs.s + 1 + 1 + 1 = b.s + 3 := by rw [hb.sp]; bv_decide (config := { enums := false })
  rw [e2, e1]
  have v1 := elems_single hlo (readVS_sound hc hb (stack (b.s + 2)))
  have v2 := elems_single hhi (readVS_sound hc hb (stack (b.s + 3)))
  show base (Plain.memRead t.ram t.prg (stack (b.s + 2))) (Plain.memRead t.ram t.prg (stack (b.s + 3))) = _
  rw [v1, v2]
  decide

theorem zs_ctrl {s : NES} (h : ZStage s) (hpc : s.pc = 0x8181) : s.ctrl &&& 0x80 ≠ 0 := by
  have no : ∀ {q : UInt16}, s.pc = q → (0x8181 : UInt16) ≠ q → False := fun h1 h2 => h2 (hpc.symm.trans h1)
  obtain ⟨_, h0 | h1 | h2 | h3 | h4 | h5 | h6⟩ := h
  · exact (no h0.1 (by decide)).elim
  · exact (no h1.1 (by decide)).elim
  · exact (no h2.1 (by decide)).elim
  · exact (no h3.1 (by decide)).elim
  · exact h4.2.1.on
  · exact (no h5.1 (by decide)).elim
  · obtain ⟨_, a | a | a | a | a⟩ := h6
    all_goals exact (no a.1 (by decide)).elim

/-- The closing sequence's region. -/
structure ZFits (rs : List Region) (Z : Region) : Prop where
  entries : ∀ e ∈ Z.entries, e.pc = 0x8178
  exit : Z.exit 0x808F = true
  empty : ∀ r ∈ rs, r ≠ Z → ∀ pc, preamblePC pc = true → r.T.at pc = []

/-- The regions' invariant, carrying what `Guard` needs. -/
def FInv (rom : UInt16 → UInt8) (g : Global) (rs : List Region) (Z : Region) (s : NES) : Prop :=
  Sch s ∧ s.prg = Smb.prg ∧ ∃ r ∈ rs, ∃ ram0, GInv rom r.prot g ram0 r.T s ∧ (r = Z → ZStage s ∨ s.pc = 0x808F)

theorem FInv.rinv {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {s : NES} (h : FInv rom g rs Z s) : RInv rom g rs s := by
  obtain ⟨_, _, r, hr, ram0, hi, _⟩ := h
  exact ⟨r, hr, ram0, hi⟩

/-- A start outside the closing sequence's region. -/
theorem FInv.of_start {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z r : Region} {s : NES} (hs : Sch s) (hp : s.prg = Smb.prg) (hr : r ∈ rs) (hne : r ≠ Z) {ram0 : UInt16 → UInt8}
    (hi : GInv rom r.prot g ram0 r.T s) : FInv rom g rs Z s :=
  ⟨hs, hp, r, hr, ram0, hi, fun e => absurd e hne⟩

/-- A byte of RAM, in a state some region's invariant holds of, as its plain state has it. -/
theorem ginv_ram {rom : UInt16 → UInt8} {prot : UInt16 → Bool} {g : Global} {ram0 : UInt16 → UInt8} {T : Table} {s : NES} (h : GInv rom prot g ram0 T s)
    (i : UInt16) (hp : prot (i &&& 0x7FF) = true) : s.ram.get! (i &&& 0x7FF).toNat = ram0 (i &&& 0x7FF) := by
  obtain ⟨t, _, ⟨b, _, hb⟩, hrel⟩ := h
  have h1 : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hrel with hr | ⟨_, hr⟩
    · exact hr.ram i
    · exact hr.ram i
  rw [h1]
  exact hb.frame _ hp

/-- As `finv_step`, and which region the step is in. -/
theorem finv_step_region {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool} {s : NES}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (h : FInv rom g rs Z s) (hd : done s.pc = false) (hus : s.unmodelled = false)
    (hu : (CPU.step.run s).2.unmodelled = false)
    (hA : (∀ i : UInt16, (∀ r ∈ rs, r.prot (i &&& 0x7FF) = true) → 0x200 ≤ i &&& 0x7FF → (CPU.step.run s).2.ram.get! (i &&& 0x7FF).toNat = s.ram.get! (i &&& 0x7FF).toNat) → Clean g (CPU.step.run s).2) :
    Guard s ∧ FInv rom g rs Z (CPU.step.run s).2 ∧
      ∃ r1 ∈ rs, ∃ ram1, GInv rom r1.prot g ram1 r1.T s ∧ r1.exit s.pc = false ∧ GInv rom r1.prot g ram1 r1.T (CPU.step.run s).2 := by
  obtain ⟨hS, hP, r, hr, ram0, hi, hzs⟩ := h
  have hSS : SchS s := by
    rcases hS with h | h
    · rw [hus] at h; cases h
    · exact h
  have key : ∃ r1 ∈ rs, ∃ ram1, GInv rom r1.prot g ram1 r1.T s ∧ r1.exit s.pc = false ∧ (r1 = Z → ZStage s) := by
    cases hx : r.exit s.pc with
    | false =>
      refine ⟨r, hr, ram0, hi, hx, fun e => ?_⟩
      rcases hzs e with h | h
      · exact h
      · subst e
        rw [h, hz.exit] at hx
        cases hx
    | true =>
      rcases hf.link r hr s.pc hx with h1 | ⟨r', hr', hx', hl⟩
      · rw [hd] at h1; cases h1
      · obtain ⟨ram1, hi'⟩ := ginv_hop' (prot' := r'.prot) (T' := r'.T) hi hl (hf.entries r' hr')
        refine ⟨r', hr', ram1, hi', hx', fun e => ?_⟩
        obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := hi
        have hspc : s.pc = t.regs.pc := by
          rcases hrel with h1 | ⟨_, h1⟩
          · exact congrArg Regs.pc h1.regs
          · exact congrArg Regs.pc h1.regs
        have hb1 := List.all_eq_true.mp (by rw [hspc] at hl; exact hl) b hbm
        obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp hb1
        rw [e] at hq
        have hq8 := hz.entries q hq
        have hle2 : q.pc = b.pc := by
          simp only [Box.le, Bool.and_eq_true, beq_iff_eq] at hle
          exact hle.1.1.1.1.1.1
        have hpc : s.pc = 0x8178 := by
          rw [hspc, ← hb.pc.symm, ← hle2, hq8]
        rcases hrel with h1 | ⟨h2, _⟩
        · exact ⟨hP, Or.inl ⟨hpc, hSS, h1.ctrl, h1.nmiPending⟩⟩
        · rw [← hspc, hpc] at h2
          exact absurd h2 (by decide)
  obtain ⟨r1, hr1, ram1, hi1, hx1, hz1⟩ := key
  have hstep : Guard s ∧ (r1 = Z → ZStage (CPU.step.run s).2 ∨ (CPU.step.run s).2.pc = 0x808F) := by
    by_cases e : r1 = Z
    · have zs := hz1 e
      have rti : s.pc = 0x8181 → (preChecks s).pc = 0x8057 := fun hpc =>
        ginv_rti_pc (hf.chk r1 hr1) hx1 hi1 hpc (zs_ctrl zs hpc)
      obtain ⟨g1, g2⟩ := zs_step zs hu rti
      exact ⟨g1, fun _ => g2⟩
    · refine ⟨?_, fun e' => absurd e' e⟩
      intro hg
      obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := hi1
      have hspc : s.pc = t.regs.pc := by
        rcases hrel with h1 | ⟨_, h1⟩
        · exact congrArg Regs.pc h1.regs
        · exact congrArg Regs.pc h1.regs
      rw [hz.empty r1 hr1 e t.regs.pc (by rw [← hspc]; exact hg)] at hbm
      cases hbm
  have hnext := ginv_stepK (hf.chk r1 hr1) (hf.idle r1 hr1) hi1 hx1 hstep.1
    (fun hk => hA (fun i hi hl => (hk i (hi r1 hr1) hl).trans (ginv_ram hi1 i (hi r1 hr1)).symm))
  exact ⟨hstep.1, ⟨(Pres.step s).1 hS, by rw [(Pres.step s).2]; exact hP, r1, hr1, ram1, hnext, hstep.2⟩, r1, hr1, ram1, hi1, hx1, hnext⟩

/-- As `finv_step`, and a cell that every region protects keeps its value. -/
theorem finv_step_keep {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool} {s : NES}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (h : FInv rom g rs Z s) (hd : done s.pc = false) (hus : s.unmodelled = false)
    (hu : (CPU.step.run s).2.unmodelled = false) (hA : Clean g (CPU.step.run s).2) :
    Guard s ∧ FInv rom g rs Z (CPU.step.run s).2 ∧
      ∀ i : UInt16, (∀ r ∈ rs, r.prot (i &&& 0x7FF) = true) → (CPU.step.run s).2.ram.get! (i &&& 0x7FF).toNat = s.ram.get! (i &&& 0x7FF).toNat := by
  obtain ⟨hg, hn, r1, hr1, ram1, hi1, _, hnext⟩ := finv_step_region hf hz h hd hus hu (fun _ => hA)
  refine ⟨hg, hn, fun i hi => ?_⟩
  rw [ginv_ram hnext i (hi r1 hr1), ginv_ram hi1 i (hi r1 hr1)]

/-- `Clean` needn't be known ahead of the step: it can rest on the cells every region protects having kept their values, since the check shows the instruction can't change those. -/
theorem finv_clean {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool} {s : NES}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (h : FInv rom g rs Z s) (hd : done s.pc = false) (hus : s.unmodelled = false)
    (hu : (CPU.step.run s).2.unmodelled = false)
    (hA : (∀ i : UInt16, (∀ r ∈ rs, r.prot (i &&& 0x7FF) = true) → 0x200 ≤ i &&& 0x7FF → (CPU.step.run s).2.ram.get! (i &&& 0x7FF).toNat = s.ram.get! (i &&& 0x7FF).toNat) → Clean g (CPU.step.run s).2) :
    Clean g (CPU.step.run s).2 := by
  obtain ⟨_, ⟨_, _, r, _, ram0, ⟨t, _, ⟨b, _, hb⟩, hrel⟩, _⟩, _⟩ := finv_step_region hf hz h hd hus hu hA
  have hram (i : UInt16) : (CPU.step.run s).2.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact h1.ram i
    · exact h1.ram i
  constructor
  · have e := hram 0x300
    have e1 : (0x300 : UInt16) &&& 0x7FF = 0x300 := by decide
    rw [e1] at e
    show (gAt g 0x300).mem ((CPU.step.run s).2.ram.get! (0x300 : UInt16).toNat) = true
    rw [e]; exact hb.glob _
  · have e := hram 0x340
    have e1 : (0x340 : UInt16) &&& 0x7FF = 0x340 := by decide
    rw [e1] at e
    show (gAt g 0x340).mem ((CPU.step.run s).2.ram.get! (0x340 : UInt16).toNat) = true
    rw [e]; exact hb.glob _

/-- The invariant for more regions. -/
theorem FInv.mono {rom : UInt16 → UInt8} {g : Global} {rs rs' : List Region} {Z : Region} {s : NES} (hs : ∀ r ∈ rs, r ∈ rs') (h : FInv rom g rs Z s) : FInv rom g rs' Z s := by
  obtain ⟨hS, hP, r, hr, ram0, hi, hz⟩ := h
  exact ⟨hS, hP, r, hs r hr, ram0, hi, hz⟩

/-- A state at an exit of `r`, with a region to go on to, is in that region: one that isn't the closing sequence's, away from the closing sequence's entry. -/
theorem FInv.hop {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z r r' : Region} {s : NES} (hne : r' ≠ Z) (hr' : r' ∈ rs)
    (hl : (r.T.at s.pc).all (fun b => r'.entries.any (Box.le g b)) = true) (hE : r'.entries.all (entryIn g r'.T) = true)
    (hS : Sch s) (hP : s.prg = Smb.prg) {ram0 : UInt16 → UInt8} (hi : GInv rom r.prot g ram0 r.T s) : FInv rom g rs Z s := by
  obtain ⟨ram1, hi'⟩ := ginv_hop' (prot' := r'.prot) (T' := r'.T) hi hl hE
  exact FInv.of_start hS hP hr' hne hi'

theorem finv_step {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool} {s : NES}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (h : FInv rom g rs Z s) (hd : done s.pc = false) (hus : s.unmodelled = false)
    (hu : (CPU.step.run s).2.unmodelled = false) (hA : Clean g (CPU.step.run s).2) :
    Guard s ∧ FInv rom g rs Z (CPU.step.run s).2 :=
  ⟨(finv_step_keep hf hz h hd hus hu hA).1, (finv_step_keep hf hz h hd hus hu hA).2.1⟩

/-- The regions' invariant over any number of instructions, for any controller input and any PPU timing, lag included, until a `done` address comes up or the run leaves the model. Nothing
about NMI timing is assumed. -/
theorem finv_stepN {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (n : Nat) (s : NES)
    (hd : ∀ i, i < n → done (stepN i s).pc = false) (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hA : ∀ i, i < n → Clean g (stepN (i + 1) s))
    (h : FInv rom g rs Z s) : FInv rom g rs Z (stepN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    exact ih (CPU.step.run s).2 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi)) (fun i hi => hu (i + 1) (Nat.succ_le_succ hi))
      (fun i hi => hA (i + 1) (Nat.succ_lt_succ hi))
      (finv_step hf hz h (hd 0 (Nat.succ_pos _)) (hu 0 (Nat.zero_le _)) (hu 1 (by omega)) (hA 0 (Nat.succ_pos _))).2

/-- A cell that every region protects keeps its value over those instructions. -/
theorem finv_keepN {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (n : Nat) (s : NES)
    (hd : ∀ i, i < n → done (stepN i s).pc = false) (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hA : ∀ i, i < n → Clean g (stepN (i + 1) s))
    (h : FInv rom g rs Z s) (a : UInt16) (ha : ∀ r ∈ rs, r.prot (a &&& 0x7FF) = true) :
    (stepN n s).ram.get! (a &&& 0x7FF).toNat = s.ram.get! (a &&& 0x7FF).toNat := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hk := finv_step_keep hf hz h (hd 0 (Nat.succ_pos _)) (hu 0 (Nat.zero_le _)) (hu 1 (by omega)) (hA 0 (Nat.succ_pos _))
    exact (ih (CPU.step.run s).2 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi)) (fun i hi => hu (i + 1) (Nat.succ_le_succ hi))
      (fun i hi => hA (i + 1) (Nat.succ_lt_succ hi)) hk.2.1).trans (hk.2.2 a ha)

/-- And `Guard` at every step, so everything proved under it applies. -/
theorem finv_guard {rom : UInt16 → UInt8} {g : Global} {rs : List Region} {Z : Region} {done : UInt16 → Bool}
    (hf : Fits rom g rs done) (hz : ZFits rs Z) (n : Nat) (s : NES)
    (hd : ∀ i, i ≤ n → done (stepN i s).pc = false) (hu : ∀ i, i ≤ n + 1 → (stepN i s).unmodelled = false)
    (hA : ∀ i, i ≤ n → Clean g (stepN (i + 1) s))
    (h : FInv rom g rs Z s) : Guard (stepN n s) := by
  have hN := finv_stepN hf hz n s (fun i hi => hd i (Nat.le_of_lt hi)) (fun i hi => hu i (by omega)) (fun i hi => hA i (Nat.le_of_lt hi)) h
  have e : (CPU.step.run (stepN n s)).2 = stepN (n + 1) s := by
    clear hN hd hu hA h
    induction n generalizing s with
    | zero => rfl
    | succ n ih => exact ih (CPU.step.run s).2
  exact (finv_step hf hz hN (hd n (Nat.le_refl _)) (hu n (by omega)) (by rw [e]; exact hu (n + 1) (Nat.le_refl _)) (by rw [e]; exact hA n (Nat.le_refl _))).1

end Smb.Routine.FrameGuard
