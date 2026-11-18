import Smb.Routine.PlayerEnter
import Smb.Routine.RunSteps

/-!
# The player region's run on the full NES

From the instant the cycle hands over to the player region at `$8175` (`Entered`) to its first return into the
engine at `$AF01`, on the full NES:

* `to_routine`: the run reaches `PlayerCtrlRoutine` (`$B0E9`) first, quiet, with Mario's horizontal bytes, last
  frame's on-screen X and the side-collision timer as they were at `$8175`, and in `PlayerCtrl`'s entry box. The
  first step is the plain machine's (`plain_step`); from there `Sim` follows `PlayerPre`'s plain run.
* `routine_run`: from there to `$AF01`, `XStep` holds between the RAM at `$B0E9` and the RAM at `$AF01`, on ground,
  jumping and falling frames, unless the run passed an exit that ends normal play. `block_prefix` keeps every prefix
  of the plain run from being `bad`, so `refine_runTo` applies at the instant the NES gets to `$AF01`.
-/
namespace Smb.Routine.PlayerJoin
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle Smb.Routine.PlayKeep
open Smb.Routine.PlayerEnter Smb.Routine.BlockPrefix Smb.Routine.RunSteps Smb.Routine.HorizontalLimit

theorem runTo_stepN' (stop : UInt16) (n : Nat) (s : NES) :
    ∃ k, k ≤ n ∧ ((CPU.runTo (σ := NES) stop n).run s).2 = stepN k s ∧ (∀ i, i < k → (stepN i s).pc ≠ stop) ∧
      (k = n ∨ (stepN k s).pc = stop) := by
  induction n generalizing s with
  | zero => exact ⟨0, Nat.le_refl _, rfl, fun i hi => absurd hi (Nat.not_lt_zero i), Or.inl rfl⟩
  | succ n ih =>
    by_cases hp : s.pc = stop
    · refine ⟨0, Nat.zero_le _, ?_, fun i hi => absurd hi (Nat.not_lt_zero i), Or.inr hp⟩
      show ((if (CPU.getRegs (σ := NES) |>.run s).1.pc = stop then pure () else do CPU.step; CPU.runTo stop n : StateM NES Unit).run s).2 = s
      have : (CPU.getRegs (σ := NES) |>.run s).1.pc = s.pc := rfl
      simp [this, hp]
      rfl
    · obtain ⟨k, hk, h1, h2, h3⟩ := ih (CPU.step.run s).2
      refine ⟨k + 1, Nat.succ_le_succ hk, ?_, fun i hi => ?_, ?_⟩
      · rw [show stepN (k + 1) s = stepN k (CPU.step.run s).2 from rfl, ← h1]
        have : (CPU.getRegs (σ := NES) |>.run s).1.pc = s.pc := rfl
        show ((if (CPU.getRegs (σ := NES) |>.run s).1.pc = stop then pure () else do CPU.step; CPU.runTo stop n : StateM NES Unit).run s).2 = _
        simp [this, hp]
        rfl
      · cases i with
        | zero => exact hp
        | succ i => exact h2 i (Nat.lt_of_succ_lt_succ hi)
      · rcases h3 with h3 | h3
        · exact Or.inl (by omega)
        · exact Or.inr h3

/-- A run to `stop` that doesn't see it before `n` steps is `n` steps. -/
theorem runTo_eq_stepN (stop : UInt16) (n : Nat) (s : NES) (hd : ∀ i, i < n → (stepN i s).pc ≠ stop) :
    ((CPU.runTo (σ := NES) stop n).run s).2 = stepN n s := by
  obtain ⟨k, hk, h1, _, h3⟩ := runTo_stepN' stop n s
  rcases h3 with rfl | h3
  · exact h1
  · by_cases hkn : k = n
    · subst hkn; exact h1
    · exact absurd h3 (hd k (by omega))

theorem stepN_prg (n : Nat) (s : NES) : (stepN n s).prg = s.prg := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih _).trans (Pres.step s).2

theorem quiet_of_rel {s : NES} {t : Plain} (h : Rel s t) : s.Quiet := ⟨h.size, h.ctrl, h.nmiPending, h.nmiPolled, h.dma⟩

/-- A box that holds at a plain state related to `s` holds at `s`'s plain view, if its cells are RAM. -/
theorem holds_toPlain {prot prot' : UInt16 → Bool} {g : Global} {ram0 : UInt16 → UInt8} {b : Box} {s : NES} {t : Plain}
    (hr : Rel s t) (h : Holds prot g ram0 b t) (hcell : b.cells.all (fun c => c.1 < 0x800) = true)
    (hg : g.size = 0x800) : Holds prot' g s.toPlain.ram b s.toPlain := by
  have hreg : s.toPlain.regs = t.regs := hr.regs
  have hram (i : UInt16) (hi : i < 0x800) : s.toPlain.ram i = t.ram i := by
    have := hr.ram i
    rw [and7ff_of_lt i hi] at this
    show s.ram.get! (i &&& 0x7FF).toNat = t.ram i
    rw [and7ff_of_lt i hi]; exact this
  refine { pc := by rw [hreg]; exact h.pc, sp := by rw [hreg]; exact h.sp, a := by rw [hreg]; exact h.a,
           x := by rw [hreg]; exact h.x, y := by rw [hreg]; exact h.y, p := by rw [hreg]; exact h.p,
           i := by rw [hreg]; exact h.i, bad := rfl, cells := fun c hc => ?_, glob := fun i => ?_, frame := fun _ _ => rfl }
  · have hl := List.all_eq_true.mp hcell c hc
    rw [hram _ (by simpa using hl)]
    exact h.cells c hc
  · by_cases hi : i < 0x800
    · rw [hram i hi]; exact h.glob i
    · have : gAt g i = .top := by
        have hn : ¬ i.toNat < g.size := by
          rw [hg]; intro h'; exact hi (UInt16.lt_iff_toNat_lt.mpr (by simpa using h'))
        simp [gAt, Array.getD, hn]
      rw [this]; rfl

theorem toPlain_eq {s : NES} (hpc : s.pc = 0xB0E9) (hs : s.s = 0xF7) (hprg : s.prg = Smb.prg) :
    s.toPlain = ⟨⟨0xB0E9, s.a, s.x, s.y, 0xF7, s.p⟩, ramAt s, romFn, s.cyc, false⟩ := by
  unfold NES.toPlain
  rw [hpc, hs, hprg]
  rfl

theorem pre_prot : [0x57, 0x86, 0x6D, 0x400, 0x71A, 0x71B, 0x71C, 0x71D, 0x3A1, 0x755, 0x785, 0x705].all
    (fun i : UInt16 => PlayerPre.conf.protFn i) = true := by native_decide

/-- Mario's horizontal bytes, last frame's on-screen X and the side-collision timer. -/
def kbytes : List UInt16 := [0x57, 0x86, 0x6D, 0x400, 0x71A, 0x71B, 0x71C, 0x71D, 0x3A1, 0x755, 0x785, 0x705]

theorem pre_prot_of {a : UInt16} (ha : a ∈ kbytes) : PlayerPre.conf.protFn a = true :=
  List.all_eq_true.mp pre_prot a ha

theorem kbytes_low {a : UInt16} (ha : a ∈ kbytes) : a &&& 0x7FF = a := by
  simp only [kbytes, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem state_vals : (List.range 256).all (fun n => !(gAt PlayerCtrl.conf.globals 0x1D).mem (UInt8.ofNat n) ||
    (n == 0 || n == 1 || n == 2)) = true := by native_decide

theorem zero_vals : [0x704, 0x70B, 0x70E].all (fun a : UInt16 => (List.range 256).all (fun n =>
    !(gAt PlayerCtrl.conf.globals a).mem (UInt8.ofNat n) || n == 0)) = true := by native_decide

/-- The routine region's bounds leave swimming, a size change and a jumpspring out. -/
theorem zero_of_glob {a : UInt16} (ha : a ∈ [(0x704 : UInt16), 0x70B, 0x70E]) (v : UInt8)
    (h : (gAt PlayerCtrl.conf.globals a).mem v = true) : v = 0 := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp zero_vals a ha) v.toNat (List.mem_range.mpr v.toNat_lt)
  simp only [UInt8.ofNat_toNat, h, Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  exact UInt8.toNat_inj.mp (by simpa using h1)

/-- The routine region's bounds allow only the ground, jumping and falling states. -/
theorem state_of_glob (v : UInt8) (h : (gAt PlayerCtrl.conf.globals 0x1D).mem v = true) : v = 0 ∨ v = 1 ∨ v = 2 := by
  have h1 := List.all_eq_true.mp state_vals v.toNat (List.mem_range.mpr v.toNat_lt)
  simp only [UInt8.ofNat_toNat, h, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · left; exact UInt8.toNat_inj.mp (by simpa using h1)
  · right; left; exact UInt8.toNat_inj.mp (by simpa using h1)
  · right; right; exact UInt8.toNat_inj.mp (by simpa using h1)

theorem stop_B1E5 : stop 0xB1E5 = true := by native_decide

/-- A stop isn't `VerticalPipeEntry`'s address unless it is. -/
theorem ne_B1E5 {pc : UInt16} (h : stop pc = false) : pc ≠ 0xB1E5 := by
  intro e; subst e; rw [stop_B1E5] at h; cases h

/-- What the routine's entry has, on the NES. -/
structure AtRoutine (s : NES) : Prop where
  pc : s.pc = 0xB0E9
  sp : s.s = 0xF7
  i : (s.p &&& 4 == 0) = false
  quiet : s.Quiet
  prg : s.prg = Smb.prg
  ctrl : ∃ e ∈ PlayerCtrl.conf.entries, Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals s.toPlain.ram e s.toPlain

/-- **From the player region's entry to `PlayerCtrlRoutine`**, on the NES. -/
theorem to_routine (s0 : NES) (he : Entered s0) (j : Nat) (hj : (stepN j s0).pc = 0xAF01)
    (hno : ∀ i, i ≤ j → (stepN i s0).pc ≠ 0xB1E5) :
    ∃ kB, kB < j ∧ AtRoutine (stepN kB s0) ∧ (∀ i, i < kB → (stepN i s0).pc ≠ 0xB0E9) ∧
      ∀ a ∈ kbytes, ramAt (stepN kB s0) a = ramAt s0 a := by
  obtain ⟨hpc0, c, hc, hn, hat, ram1, gi0, hx0, _⟩ := he
  obtain ⟨t0, c', b0, hb0m, hb0, htc, hrd, hrel1⟩ := plain_step hc hn gi0 hx0
  have ht0pc : t0.regs.pc = 0x8175 := (congrArg Regs.pc hrd.regs).symm.trans hpc0
  have hp := enter_ok hc hn
  simp only [enterOk, Bool.and_eq_true, List.all_eq_true] at hp
  rw [ht0pc] at hb0m
  obtain ⟨e1, he1, hle1⟩ := List.any_eq_true.mp (hp.2 b0 hb0m)
  have hq := pre_ok
  simp only [preOk, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨hlink, hnoAF'⟩, hw1⟩, hw2⟩, hent⟩ := hq
  have hnoAF := List.isEmpty_iff.mp hnoAF'
  have hh1 : Holds PlayerPre.conf.protFn PlayerPre.conf.globals t0.ram e1 t0 := hop hle1 hw1 pre_size hb0
  obtain ⟨t0', hT⟩ : ∃ t, t = ({ t0 with cyc := c' } : Plain) := ⟨_, rfl⟩
  rw [← hT] at hrel1
  have hc0' : Code (romOf Smb.prg) t0' := by subst hT; exact fun a ha => htc a ha
  have hram0 : t0'.ram = t0.ram := by subst hT; rfl
  have hh1' : Holds PlayerPre.conf.protFn PlayerPre.conf.globals t0'.ram e1 t0' := by
    subst hT
    exact { pc := hh1.pc, sp := hh1.sp, a := hh1.a, x := hh1.x, y := hh1.y, p := hh1.p, i := hh1.i, bad := hh1.bad,
            cells := hh1.cells, glob := hh1.glob, frame := hh1.frame }
  have hacc := PlayerSplit.pre_accepted
  simp only [PlayerPre.accepted, Bool.and_eq_true, List.all_eq_true] at hacc
  have hI0 : Inv PlayerPre.conf.protFn PlayerPre.conf.globals t0'.ram (PlayerPre.conf.table Smb.prg) t0' :=
    inv_of_entry (hacc.2 e1 he1) hh1'
  have hne : t0'.regs.pc ≠ 0xB0E9 := by subst hT; show t0.regs.pc ≠ _; rw [ht0pc]; decide
  have hne2 : t0'.regs.pc ≠ 0xB1E5 := by subst hT; show t0.regs.pc ≠ _; rw [ht0pc]; decide
  -- The plain run from the first step, and the NES run from it, until `$B0E9`: `PlayerPre`'s other exit,
  -- `VerticalPipeEntry`, would be a visit the NES run doesn't make.
  have hboth (N : Nat) (hN : N + 1 ≤ j) (hd0 : ∀ i, i < N → (stepN i (CPU.step.run s0).2).pc ≠ 0xB0E9) :
      Inv PlayerPre.conf.protFn PlayerPre.conf.globals t0'.ram (PlayerPre.conf.table Smb.prg)
        ((CPU.runTo (σ := Plain) 0xB0E9 N).run (CPU.step.run t0').2).2 ∧
      Rel ((CPU.runTo (σ := NES) 0xB0E9 N).run (CPU.step.run s0).2).2
        ((CPU.runTo (σ := Plain) 0xB0E9 N).run (CPU.step.run t0').2).2 := by
    rcases runTo_exits hacc.1 PlayerSplit.pre_top PlayerSplit.pre_top2 0xB0E9 (N + 1) t0' hc0' hI0 with
      ⟨_, hi⟩ | ⟨m, k, hm, _, hx, hn, _, hi, _⟩
    · rw [runTo_succ 0xB0E9 N t0' hne] at hi
      refine ⟨hi, ?_⟩
      obtain ⟨_, _, hb⟩ := hi
      exact ((Sim.runTo 0xB0E9 N).2 _ _ hrel1 hb.bad).2
    · exfalso
      have hpc : ((CPU.runTo (σ := Plain) 0xB0E9 m).run t0').2.regs.pc = 0xB1E5 := by
        simp only [Config.C.exitFn, PlayerSplit.pre_exit_eq, List.contains_cons, List.contains_nil, Bool.or_false,
          Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with h | h
        · exact h
        · exact absurd h hn
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        cases m with
        | zero => rw [runTo_zero] at hpc; exact absurd hpc hne2
        | succ m' => exact ⟨m', rfl⟩
      rw [runTo_succ 0xB0E9 m' t0' hne] at hpc hi
      obtain ⟨_, _, hb⟩ := hi
      have hr := ((Sim.runTo 0xB0E9 m').2 _ _ hrel1 hb.bad).2
      rw [runTo_eq_stepN _ _ _ (fun i hi => hd0 i (by omega))] at hr
      have hp := (congrArg Regs.pc hr.regs).trans hpc
      exact hno (m' + 1) (by omega) hp
  have hj0 : j ≠ 0 := by intro h; subst h; rw [show stepN 0 s0 = s0 from rfl, hpc0] at hj; exact absurd hj (by decide)
  have hshift (k : Nat) (hk : k ≠ 0) : stepN (k - 1) (CPU.step.run s0).2 = stepN k s0 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]; rfl
  rcases first_hit (fun x => x.pc == 0xB0E9) j s0 with hnone | ⟨kB, hkB, hhit, hbefore⟩
  · -- No `PlayerCtrlRoutine` before `$AF01`: the plain run would be at `$AF01`, where `PlayerPre` has no box.
    exfalso
    have hd : ∀ i, i < j - 1 → (stepN i (CPU.step.run s0).2).pc ≠ 0xB0E9 := by
      intro i hi e
      have := hnone (i + 1) (by omega)
      rw [show stepN (i + 1) s0 = stepN i (CPU.step.run s0).2 from rfl] at this
      simp [e] at this
    have hr := (hboth (j - 1) (by omega) hd).2
    rw [runTo_eq_stepN _ _ _ hd, hshift j hj0] at hr
    obtain ⟨b, hbm, hb⟩ := (hboth (j - 1) (by omega) hd).1
    have hpc : ((CPU.runTo (σ := Plain) 0xB0E9 (j - 1)).run (CPU.step.run t0').2).2.regs.pc = 0xAF01 :=
      (congrArg Regs.pc hr.regs).symm.trans hj
    rw [hpc, hnoAF] at hbm
    cases hbm
  · have hpcB : (stepN kB s0).pc = 0xB0E9 := by simpa using hhit
    have hk0 : kB ≠ 0 := by intro h; subst h; rw [show stepN 0 s0 = s0 from rfl, hpc0] at hpcB; exact absurd hpcB (by decide)
    have hkj : kB < j := by
      rcases Nat.lt_or_eq_of_le hkB with h | h
      · exact h
      · subst h; rw [hj] at hpcB; exact absurd hpcB (by decide)
    have hd : ∀ i, i < kB - 1 → (stepN i (CPU.step.run s0).2).pc ≠ 0xB0E9 := by
      intro i hi e
      have := hbefore (i + 1) (by omega)
      rw [show stepN (i + 1) s0 = stepN i (CPU.step.run s0).2 from rfl] at this
      simp [e] at this
    have hr := (hboth (kB - 1) (by omega) hd).2
    rw [runTo_eq_stepN _ _ _ hd, hshift kB hk0] at hr
    generalize hyB : ((CPU.runTo (σ := Plain) 0xB0E9 (kB - 1)).run (CPU.step.run t0').2).2 = yB at hr
    have hiB := (hboth (kB - 1) (by omega) hd).1
    rw [hyB] at hiB
    obtain ⟨bB, hbBm, hhB⟩ := hiB
    have hyBpc : yB.regs.pc = 0xB0E9 := (congrArg Regs.pc hr.regs).symm.trans hpcB
    rw [hyBpc] at hbBm
    obtain ⟨e2, he2, hle2⟩ := List.any_eq_true.mp (List.all_eq_true.mp hlink bB hbBm)
    have hh2 : Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals yB.ram e2 yB := hop hle2 hw2 ctrl_size hhB
    have hent2 := List.all_eq_true.mp hent e2 he2
    simp only [Bool.and_eq_true, beq_iff_eq] at hent2
    obtain ⟨⟨⟨hs2, _⟩, hcells2⟩, hp2⟩ := hent2
    have hh3 : Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals (stepN kB s0).toPlain.ram e2 (stepN kB s0).toPlain :=
      holds_toPlain hr hh2 hcells2 ctrl_size
    have hprg : (stepN kB s0).prg = Smb.prg := by
      rw [← hshift kB hk0, stepN_prg]; exact hat.2.1
    refine ⟨kB, hkj, ⟨hpcB, ?_, ?_, quiet_of_rel hr, hprg, e2, he2, hh3⟩, fun i hi e => ?_, fun a ha => ?_⟩
    · have := hh3.sp
      rw [hs2] at this
      exact this
    · exact beq_false_of_ne hh3.i
    · have := hbefore i hi
      simp [e] at this
    · -- The kept bytes: through the plain run, which `PlayerPre` keeps them along, back to the NES at `$8175`.
      have e1 := ramAt_of_rel hr a
      rw [kbytes_low ha] at e1
      have e2' := hhB.frame a (pre_prot_of ha)
      rw [hram0] at e2'
      have e3 : ramAt s0 a = t0.ram a := by
        show s0.ram.get! (a &&& 0x7FF).toNat = t0.ram a
        have := hrd.ram a
        rw [kbytes_low ha] at this ⊢
        exact this
      rw [e1, e2', e3]

/-- **From `PlayerCtrlRoutine` to the return into the engine**, on the NES: with the Y speed in range, `XStep` from
the RAM at `$B0E9` to the RAM at `$AF01`, or the run passed an exit that ends normal play. The routine region's bounds
leave only the ground, jumping and falling states, with no swimming, size change or jumpspring. -/
theorem routine_run (sB : NES) (hB : AtRoutine sB) (d : Nat) (hd : (stepN d sB).pc = 0xAF01)
    (hfirst : ∀ i, i < d → (stepN i sB).pc ≠ 0xAF01)
    (hinv : XInv (ramAt sB))
    (hspd : ramAt sB 0x9F + 0x40 < 0x80) :
    (XStep (ramAt sB) (ramAt (stepN d sB)) ∧ (Launch.Far (ramAt sB) → Launch.LStep (ramAt sB) (ramAt (stepN d sB)))) ∨
      (∃ m, m ≤ d ∧ EndExit (stepN m sB).pc) ∨
      ∃ k u, EndExit u.regs.pc ∧
        ((CPU.runTo (σ := Plain) 0xAF01 d).run sB.toPlain).2 = ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  obtain ⟨hpc, hsp, hI, hq, hprg, e, he, hh⟩ := hB
  have ht : ramAt sB 0x1D = 0 ∨ ramAt sB 0x1D = 1 ∨ ramAt sB 0x1D = 2 := state_of_glob _ (hh.glob 0x1D)
  have hs : ramAt sB 0x704 = 0 := zero_of_glob (by simp) _ (hh.glob 0x704)
  have hz : ramAt sB 0x70B = 0 := zero_of_glob (by simp) _ (hh.glob 0x70B)
  have hjs : ramAt sB 0x70E = 0 := zero_of_glob (by simp) _ (hh.glob 0x70E)
  have heq := toPlain_eq hpc hsp hprg
  have hcode : Code (romOf Smb.prg) sB.toPlain := by rw [heq]; exact PlayerCtrlLink.code_st _ _ _ _ _ _ _
  rcases block_prefix sB.toPlain hcode e he hh d with hb | ⟨m, hm, hend, hbm⟩
  · have hr := refine_runTo sB hq 0xAF01 d hb
    rw [runTo_eq_stepN _ _ _ hfirst] at hr
    have hreach : ((CPU.runTo (σ := Plain) 0xAF01 d).run sB.toPlain).2.regs.pc = 0xAF01 :=
      (congrArg Regs.pc hr.regs).symm.trans hd
    rw [heq] at hreach hh hr ⊢
    have key : (XStep (ramAt sB) ((CPU.runTo (σ := Plain) 0xAF01 d).run
          ⟨⟨0xB0E9, sB.a, sB.x, sB.y, 0xF7, sB.p⟩, ramAt sB, romFn, sB.cyc, false⟩).2.ram ∧
        (Launch.Far (ramAt sB) → Launch.LStep (ramAt sB) ((CPU.runTo (σ := Plain) 0xAF01 d).run
          ⟨⟨0xB0E9, sB.a, sB.x, sB.y, 0xF7, sB.p⟩, ramAt sB, romFn, sB.cyc, false⟩).2.ram) ∧
        ((CPU.runTo (σ := Plain) 0xAF01 d).run ⟨⟨0xB0E9, sB.a, sB.x, sB.y, 0xF7, sB.p⟩, ramAt sB, romFn, sB.cyc, false⟩).2.bad = false) ∨
        ∃ k u, EndExit u.regs.pc ∧ ((CPU.runTo (σ := Plain) 0xAF01 d).run
          ⟨⟨0xB0E9, sB.a, sB.x, sB.y, 0xF7, sB.p⟩, ramAt sB, romFn, sB.cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
      rcases ht with h0 | h1 | h2
      · exact PlayerCtrlLink.block0c sB.a sB.x sB.y sB.p (ramAt sB) sB.cyc hinv h0 hs hz hjs hspd hI ⟨e, he, hh⟩ d hreach
      · exact PlayerCtrlLink.block1c sB.a sB.x sB.y sB.p (ramAt sB) sB.cyc hinv h1 hs hz hjs hspd hI ⟨e, he, hh⟩ d hreach
      · exact PlayerCtrlLink.block2c sB.a sB.x sB.y sB.p (ramAt sB) sB.cyc hinv h2 hs hz hjs hspd hI ⟨e, he, hh⟩ d hreach
    rcases key with ⟨hX, hLs, _⟩ | ⟨k, u, hu, he'⟩
    · left
      have q (a : UInt16) (ha : a &&& 0x7FF = a) : ramAt (stepN d sB) a =
          ((CPU.runTo (σ := Plain) 0xAF01 d).run ⟨⟨0xB0E9, sB.a, sB.x, sB.y, 0xF7, sB.p⟩, ramAt sB, romFn, sB.cyc, false⟩).2.ram a := by
        have := ramAt_of_rel hr a
        rwa [ha] at this
      exact ⟨PlayerBlock.xstep_congr _ _ _ hX (q _ rfl) (q _ rfl) (q _ rfl) (q _ rfl) (q _ rfl) (q _ rfl) (q _ rfl)
        (q _ rfl) (q _ rfl) (q _ rfl),
        fun hf => PlayerBlock.lstep_congr _ _ _ (hLs hf) (q _ rfl) (q _ rfl) (q _ rfl) (q _ rfl) (q _ rfl) (q _ rfl) (q _ rfl)⟩
    · exact Or.inr (Or.inr ⟨k, u, hu, he'⟩)
  · have hr := refine_runTo sB hq 0xAF01 m hbm
    rw [runTo_eq_stepN _ _ _ (fun i hi => hfirst i (by omega))] at hr
    refine Or.inr (Or.inl ⟨m, hm, ?_⟩)
    rw [show (stepN m sB).pc = _ from congrArg Regs.pc hr.regs]
    exact hend

/-- **The player region's run on a frame of normal play**, on the NES: from the cycle's handover at `$8175` to the
first return into the engine, the horizontal bytes reach `PlayerCtrlRoutine` as they were, and with the Y speed in
range the run from there keeps the 2.5-pixel limit (`XStep`), unless it passed an exit that ends
normal play. -/
theorem player_frame (s0 : NES) (he : Entered s0) (j : Nat) (hj : (stepN j s0).pc = 0xAF01)
    (hfirst : ∀ i, i < j → (stepN i s0).pc ≠ 0xAF01) (hno : ∀ i, i ≤ j → (stepN i s0).pc ≠ 0xB1E5) :
    ∃ kB, kB < j ∧ (stepN kB s0).pc = 0xB0E9 ∧ (∀ a ∈ kbytes, ramAt (stepN kB s0) a = ramAt s0 a) ∧
      (XInv (ramAt (stepN kB s0)) → 
        ramAt (stepN kB s0) 0x9F + 0x40 < 0x80 →
        (XStep (ramAt (stepN kB s0)) (ramAt (stepN j s0)) ∧
          (Launch.Far (ramAt (stepN kB s0)) → Launch.LStep (ramAt (stepN kB s0)) (ramAt (stepN j s0)))) ∨
          (∃ m, kB ≤ m ∧ m ≤ j ∧ EndExit (stepN m s0).pc) ∨
          ∃ k u, EndExit u.regs.pc ∧ ((CPU.runTo (σ := Plain) 0xAF01 (j - kB)).run (stepN kB s0).toPlain).2 =
            ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2) := by
  obtain ⟨kB, hkj, hB, _, hkeep⟩ := to_routine s0 he j hj hno
  have hback : stepN (j - kB) (stepN kB s0) = stepN j s0 := by
    rw [← stepN_add]; congr 1; omega
  refine ⟨kB, hkj, hB.pc, hkeep, fun hinv hspd => ?_⟩
  have hd : (stepN (j - kB) (stepN kB s0)).pc = 0xAF01 := by rw [hback]; exact hj
  have hf : ∀ i, i < j - kB → (stepN i (stepN kB s0)).pc ≠ 0xAF01 := by
    intro i hi
    rw [← stepN_add]
    exact hfirst _ (by omega)
  rcases routine_run (stepN kB s0) hB (j - kB) hd hf hinv hspd with h | ⟨m, hm, hend⟩ | h
  · rw [hback] at h; exact Or.inl h
  · refine Or.inr (Or.inl ⟨kB + m, by omega, by omega, ?_⟩)
    rw [stepN_add]; exact hend
  · exact Or.inr (Or.inr h)

/-- **One frame of the cycle, from one return into the engine to the next.** From a cycle state at `$AF01` to the
next visit to `$AF01`, either Mario's horizontal bytes are all kept, or the cycle hands over to the player region,
which reaches `PlayerCtrlRoutine` with them as they were at the start, and from there, with the Y speed in range,
keeps the 2.5-pixel limit to the end (`XStep`), unless the run passed an exit that ends normal play. -/
theorem cycle_frame (s : NES) (hc : CycleInv s) (hs : s.pc = 0xAF01) (n : Nat) (hn : (stepN n s).pc = 0xAF01)
    (hfirst : ∀ i, 0 < i → i < n → (stepN i s).pc ≠ 0xAF01)
    (hd : ∀ i, i < n → stop (stepN i s).pc = false)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hcl : ∀ i, i < n → CleanIf (stepN (i + 1) s)) :
    Kept (stepN n s) s ∨
    ∃ kB, kB < n ∧ (stepN kB s).pc = 0xB0E9 ∧ (∀ a ∈ hbytes, ramAt (stepN kB s) a = ramAt s a) ∧
      (XInv (ramAt (stepN kB s)) → 
        ramAt (stepN kB s) 0x9F + 0x40 < 0x80 →
        (XStep (ramAt (stepN kB s)) (ramAt (stepN n s)) ∧
          (Launch.Far (ramAt (stepN kB s)) → Launch.LStep (ramAt (stepN kB s)) (ramAt (stepN n s)))) ∨
          (∃ m, kB ≤ m ∧ m ≤ n ∧ EndExit (stepN m s).pc) ∨
          ∃ k u, EndExit u.regs.pc ∧ ((CPU.runTo (σ := Plain) 0xAF01 (n - kB)).run (stepN kB s).toPlain).2 =
            ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2) := by
  obtain ⟨r, hr, hat⟩ := rest_of_exit hc hs
  rcases rest_run n s r hr hat hd hu hcl with ⟨_, _, _, hk⟩ | ⟨kE, hkE, hkept, hent⟩
  · exact Or.inl hk
  · right
    have hkE0 : kE ≠ 0 := by
      intro h; subst h
      have := hent.1
      rw [show stepN 0 s = s from rfl, hs] at this
      exact absurd this (by decide)
    have hback : stepN (n - kE) (stepN kE s) = stepN n s := by
      rw [← stepN_add]; congr 1; omega
    obtain ⟨kB, hkB, hpcB, hkb, hrest⟩ := player_frame (stepN kE s) hent (n - kE) (by rw [hback]; exact hn)
      (fun i hi => by rw [← stepN_add]; exact hfirst _ (by omega) (by omega))
      (fun i hi => by
        rw [← stepN_add]
        rcases Nat.lt_or_ge (kE + i) n with h | h
        · exact ne_B1E5 (hd _ h)
        · rw [show kE + i = n by omega, hn]; decide)
    have e1 : stepN kB (stepN kE s) = stepN (kE + kB) s := (stepN_add _ _ _).symm
    rw [e1] at hpcB hkb hrest
    refine ⟨kE + kB, by omega, hpcB, fun a ha => ?_, fun hinv h4 => ?_⟩
    · have ha' : a ∈ kbytes := by
        simp only [hbytes, List.mem_cons, List.not_mem_nil, or_false] at ha
        simp only [kbytes, List.mem_cons, List.not_mem_nil, or_false]
        rcases ha with h | h | h | h | h | h | h | h | h | h <;> simp [h]
      exact (hkb a ha').trans (hkept a ha)
    · rcases hrest hinv h4 with h | ⟨m, hm1, hm2, hend⟩ | h
      · rw [hback] at h; exact Or.inl h
      · refine Or.inr (Or.inl ⟨kE + m, by omega, by omega, ?_⟩)
        rw [stepN_add]; exact hend
      · refine Or.inr (Or.inr ?_)
        rw [show n - (kE + kB) = n - kE - kB by omega]
        exact h

end Smb.Routine.PlayerJoin
