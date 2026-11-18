import Smb.Routine.LaunchFrame
import Smb.Routine.LaunchExit
import Smb.Routine.RunSteps
import Smb.Routine.PlayerFrameNes

/-!
# A whole launch frame

`LaunchFrame` has the regions' three runs, and `LaunchExit` what the routine does to their bounds. `frame_run` joins them: from a frame's start in the idle loop to the next, either the routine doesn't run and the cells the regions protect are as they were, or it runs once, and they end as it leaves them.

These are assumed of the frame, and are the theorem's hypotheses:

* the frame's end doesn't cut the routine in two, and the frame ends in the idle loop (no lag)
* the NMI doesn't come again before the frame ends
* the timer doesn't run out
* no instruction sets `unmodelled`
* `CleanIf`, which `NoOverflow` gives
-/
namespace Smb.Routine.LaunchPhase
open Smb NES Smb.Abs Smb.Abs.LaunchPhase Smb.Routine.FrameGuard Smb.Routine.RunSteps Smb.Routine.LaunchExit

abbrev rom : UInt16 → UInt8 := romOf Smb.prg

theorem forall_u8 (p : UInt8 → Bool) (h : (List.range 256).all (fun n => p (UInt8.ofNat n)) = true) (v : UInt8) : p v = true := by
  have := List.all_eq_true.mp h v.toNat (List.mem_range.mpr v.toNat_lt)
  simpa using this

theorem forall_u16 (p : UInt16 → Bool) (h : (List.range 0x10000).all (fun n => p (UInt16.ofNat n)) = true) (v : UInt16) : p v = true := by
  have := List.all_eq_true.mp h v.toNat (List.mem_range.mpr v.toNat_lt)
  simpa using this

/-! ## From the routine's end into `R` -/

/-- The cells the routine writes that have a bound. -/
def special (i : UInt16) : Bool :=
  i == 0x714 || i == 0xB5 || i == 0x3A1 || i == 0x71A || i == 0x71B || i == 0x71C || i == 0x71D || i == 0x73D || i == 0x778 || i == 0x490 || i == 0x70E || i == 0x3AD || i == 0x86 || i == 0x6D

theorem written_top : (List.range 0x10000).all (fun n => !written (UInt16.ofNat n) || special (UInt16.ofNat n) || topB (gAt G (UInt16.ofNat n))) = true := by native_decide

theorem g714 : (gAt G 0x714).mem 0 = true := by native_decide
theorem gB5 : (gAt G 0xB5).mem 1 = true := by native_decide
theorem g3A1 : (gAt G 0x3A1).mem 0 = true := by native_decide
theorem g490 : (gAt G 0x490).mem 0xFF = true := by native_decide
theorem g70E : (gAt G 0x70E).mem 0 = true := by native_decide
theorem g6D : (gAt G 0x6D).mem 0 = true := by native_decide
theorem g86 : (List.range 256).all (fun n => !(decide (UInt8.ofNat n < 0x50)) || (gAt G 0x86).mem (UInt8.ofNat n)) = true := by native_decide
theorem g3AD : (List.range 256).all (fun n => !(decide (UInt8.ofNat n < 0x50)) || (gAt G 0x3AD).mem (UInt8.ofNat n)) = true := by native_decide
theorem g71C : (List.range 256).all (fun n => !((gAt G 0x71C).mem (UInt8.ofNat n)) || UInt8.ofNat n == 0) = true := by native_decide
theorem gsize : G.size = 0x800 := by native_decide

theorem exit_glob {ram F : UInt16 → UInt8} (hG : ∀ i, (gAt G i).mem (ram i) = true) (hx : Exit ram F) (hlow : F 0x86 < 0x50) (hpage : F 0x6D = 0) (i : UInt16) :
    (gAt G i).mem (F i) = true := by
  cases hw : written i with
  | false => rw [hx.keep i hw]; exact hG i
  | true =>
    have h := forall_u16 (fun i => !written i || special i || topB (gAt G i)) written_top i
    simp only [hw, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
    rcases h with hs | ht
    · simp only [special, Bool.or_eq_true, beq_iff_eq, or_assoc] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hx.crouch]; exact g714
      · rw [hx.high]; exact gB5
      · rw [hx.plat]; exact g3A1
      · rw [hx.left1]; exact hG _
      · rw [hx.right1]; exact hG _
      · rw [hx.left2]; exact hG _
      · rw [hx.right2]; exact hG _
      · rw [hx.scroll]; exact hG _
      · rw [hx.mirror]; exact hG _
      · rw [hx.coll]; exact g490
      · rw [hx.spring]; exact g70E
      · have h0 : ram 0x71C = 0 := by
          have := forall_u8 (fun v => !((gAt G 0x71C).mem v) || v == 0) g71C (ram 0x71C)
          simpa [hG 0x71C] using this
        have e0 : F 0x86 - 0 = F 0x86 := by simp
        rw [hx.rel, h0, e0]
        have := forall_u8 (fun v => !(decide (v < 0x50)) || (gAt G 0x3AD).mem v) g3AD (F 0x86)
        simpa [hlow] using this
      · have := forall_u8 (fun v => !(decide (v < 0x50)) || (gAt G 0x86).mem v) g86 (F 0x86)
        simpa [hlow] using this
      · rw [hpage]; exact g6D
    · rw [eq_top_of_topB ht]; rfl

/-- The stack and the frame's other cells, at `$B0E9`, are what `R`'s entry asks of them. -/
theorem q_boxes : ((Q.tableWith G Smb.prg).at 0xB0E9).all (fun b => b.pc == 0xB0E9 && b.s == 0xF7 && R.entries.all fun e => e.cells.all fun c => !written c.1 && decide (c.1 < 0x800) && cellCovered G b [] c) = true := by native_decide

theorem r_entry : R.entries.all (fun e => e.pc == 0xB179 && e.s == 0xF7 && topB e.a && topB e.x && topB e.y &&
    (List.range 256).all fun n => (UInt8.ofNat n &&& 4 == 0) || e.p.mem (UInt8.ofNat n)) = true := by native_decide

theorem r_ne : R.entries ≠ [] := by native_decide

theorem top_mem (v : VS) (h : topB v = true) (x : UInt8) : v.mem x = true := by
  rw [eq_top_of_topB h]; rfl

/-- The routine's end is in `R`'s entry box, given the box `Q` left it at `$B0E9`. -/
theorem exit_holds {s : NES} {t F : Plain} {b e : Box} {ram0 : UInt16 → UInt8} (hb : Holds Q.protFn G ram0 b t) (hbm : b ∈ (Q.tableWith G Smb.prg).at 0xB0E9)
    (hrel : RelD s t) (he : e ∈ R.entries) (hx : Exit (ramAt s) F.ram) (hlow : F.ram 0x86 < 0x50) (hpage : F.ram 0x6D = 0) (hpc : F.regs.pc = 0xB179) (hsp : F.regs.s = 0xF7)
    (hi : F.regs.p &&& 4 ≠ 0) (hbad : F.bad = false) : Holds R.protFn G F.ram e F := by
  have hre := List.all_eq_true.mp r_entry e he
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hre
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, ha⟩, hx'⟩, hy⟩, hp⟩ := hre
  have hram : ∀ i : UInt16, i < 0x800 → ramAt s i = t.ram i := fun i hi => by
    have := hrel.ram i
    rw [Smb.Routine.and7ff_of_lt i hi] at this
    simpa [ramAt, Smb.Routine.and7ff_of_lt i hi] using this
  have hG : ∀ i, (gAt G i).mem (ramAt s i) = true := fun i => by
    by_cases hl : i < 0x800
    · rw [hram i hl]; exact hb.glob i
    · have : gAt G i = .top := by
        have hn : ¬ i.toNat < G.size := by
          rw [gsize]; intro h; exact hl (by simpa [UInt16.lt_iff_toNat_lt] using h)
        simp [gAt, Array.getD, hn]
      rw [this]; rfl
  refine ⟨hpc.trans h1.symm, hsp.trans h2.symm, top_mem _ ha _, top_mem _ hx' _, top_mem _ hy _, ?_, hi, hbad, fun c hc => ?_, exit_glob hG hx hlow hpage, fun _ _ => rfl⟩
  · have := forall_u8 (fun v => (v &&& 4 == 0) || e.p.mem v) (by simpa using hp) F.regs.p
    simpa [hi] using this
  · have hq := List.all_eq_true.mp q_boxes b hbm
    simp only [Bool.and_eq_true, List.all_eq_true] at hq
    have hc2 := hq.2 e he c hc
    simp only [Bool.not_eq_true', decide_eq_true_eq] at hc2
    obtain ⟨⟨hw, hl⟩, hcv⟩ := hc2
    rw [hx.keep _ hw, hram _ hl]
    exact cellCovered_sound hb hcv

/-! ## Reaching the routine -/

theorem no_box {c : Config.C} {pc : UInt16} {b : Box} (he : (c.tableWith G Smb.prg).at pc = []) (hb : b ∈ (reg c).T.at pc) : False := by
  have : (reg c).T.at pc = [] := he
  rw [this] at hb
  cases hb

theorem stop_rsP {s : NES} (h : FInv rom G rsP (reg Z) s) (hs : stop s.pc = true) : s.pc = 0xB0E9 := by
  obtain ⟨_, _, r, hr, ram0, ⟨t, _, ⟨b, hb, _⟩, hrel⟩, _⟩ := h
  have hpc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  rw [← hpc] at hb
  simp only [stop, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with (h1 | h1) | h1
  · exact h1
  · rw [h1] at hb
    simp only [rsP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (no_box (pH.2.2.2 _ (by simp [timeList])) hb).elim
    · exact (no_box (pQ.2.2.2 _ (by simp [timeList])) hb).elim
    · exact (no_box (pZ.2.2.2 _ (by simp [timeList])) hb).elim
  · have hd := List.contains_iff_mem.mp h1
    simp only [rsP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (no_box (pH.2.2.2 _ (by simp [hd])) hb).elim
    · exact (no_box (pQ.2.2.2 _ (by simp [hd])) hb).elim
    · exact (no_box (pZ.2.2.2 _ (by simp [hd])) hb).elim

theorem stop_rsM {s : NES} (h : FInv rom G rsM (reg Z) s) (hs : stopM s.pc = true) : s.pc = 0xAF67 ∨ s.pc = 0xB79A := by
  obtain ⟨_, _, r, hr, ram0, ⟨t, _, ⟨b, hb, _⟩, hrel⟩, _⟩ := h
  have hpc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  rw [← hpc] at hb
  simp only [stopM, stop, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with ((h1 | h1) | h1) | h1
  · rw [h1] at hb
    simp only [rsM, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (no_box (pR.2.2.2 _ (by simp [entryList])) hb).elim
    · exact (no_box (pE.2.2.2 _ (by simp [entryList])) hb).elim
    · exact (no_box (pT.2.2.2 _ (by simp [entryList])) hb).elim
  · exact Or.inr h1
  · have hd := List.contains_iff_mem.mp h1
    simp only [rsM, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (no_box (pR.2.2.2 _ (by simp [hd])) hb).elim
    · exact (no_box (pE.2.2.2 _ (by simp [hd])) hb).elim
    · exact (no_box (pT.2.2.2 _ (by simp [hd])) hb).elim
  · exact Or.inl h1

theorem stop_rsT {s : NES} (h : FInv rom G rsT (reg Z) s) (hs : stopT s.pc = true) : s.pc = 0x808F := by
  obtain ⟨_, _, r, hr, ram0, ⟨t, _, ⟨b, hb, _⟩, hrel⟩, _⟩ := h
  have hpc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  rw [← hpc] at hb
  simp only [stopT, stop, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with ((h1 | h1) | h1) | h1
  · rw [h1] at hb
    simp only [rsT, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (no_box (pB.2.2.2 _ (by simp [entryList])) hb).elim
    · exact (no_box (pZ.2.2.2 _ (by simp [entryList])) hb).elim
  · rw [h1] at hb
    simp only [rsT, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (no_box (pB.2.2.2 _ (by simp [timeList])) hb).elim
    · exact (no_box (pZ.2.2.2 _ (by simp [timeList])) hb).elim
  · have hd := List.contains_iff_mem.mp h1
    simp only [rsT, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (no_box (pB.2.2.2 _ (by simp [hd])) hb).elim
    · exact (no_box (pZ.2.2.2 _ (by simp [hd])) hb).elim
  · exact h1

/-- In the idle loop, the last run's state is in the region that holds it. -/
theorem idle_rsT {s : NES} (h : FInv rom G rsT (reg Z) s) (hs : s.pc = 0x8057) : FInv rom G rsP (reg Z) s := by
  obtain ⟨hS, hP, r, hr, ram0, hi, hz⟩ := h
  refine ⟨hS, hP, reg Z, by simp [rsP], ram0, ?_, fun _ => hz ?_⟩
  all_goals
    simp only [rsT, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exfalso
      obtain ⟨t, _, ⟨b, hb, _⟩, hrel⟩ := hi
      have hpc : s.pc = t.regs.pc := by
        rcases hrel with h1 | ⟨_, h1⟩
        · exact congrArg Regs.pc h1.regs
        · exact congrArg Regs.pc h1.regs
      rw [← hpc, hs] at hb
      exact no_box (pB.2.2.2 _ (by simp [idleList])) hb
    · first | exact hi | rfl

/-- At the routine's entry, the state's in `Q`, on a box with its stack pointer at `$F7`. -/
theorem at_routine {s : NES} (h : FInv rom G rsP (reg Z) s) (hs : s.pc = 0xB0E9) :
    ∃ ram0 t b, Code rom t ∧ b ∈ (Q.tableWith G Smb.prg).at 0xB0E9 ∧ Holds Q.protFn G ram0 b t ∧ RelD s t ∧ t.regs.s = 0xF7 ∧ t.regs.p &&& 4 ≠ 0 := by
  obtain ⟨_, _, r, hr, ram0, ⟨t, hc, ⟨b, hb, hh⟩, hrel⟩, _⟩ := h
  have hpc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  rw [← hpc, hs] at hb
  have hrel' : RelD s t := by
    rcases hrel with h1 | ⟨h2, _⟩
    · exact h1
    · rw [← hpc, hs] at h2; exact absurd h2 (by decide)
  simp only [rsP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (no_box (pH.2.2.2 _ (by simp [entryList])) hb).elim
  · have hq := List.all_eq_true.mp q_boxes b hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    exact ⟨ram0, t, b, hc, hb, hh, hrel', hh.sp.trans hq.1.2, hh.i⟩
  · exact (no_box (pZ.2.2.2 _ (by simp [entryList])) hb).elim

/-! ## `Clean` during play

`NoOverflow` limits `$0340` by whether the game is in play after the instruction. The regions say `$770` and `$772` are as play has them before it, and that it can't change them. So all a run needs is `CleanIf`. -/

/-- The buffers are within the limits, when the state is in play. -/
def CleanIf (x : NES) : Prop := ramAt x 0x770 = 1 → ramAt x 0x772 = 3 → Clean G x

theorem g770 : (List.range 256).all (fun n => !((gAt G 0x770).mem (UInt8.ofNat n)) || UInt8.ofNat n == 1) = true := by native_decide
theorem g772 : (List.range 256).all (fun n => !((gAt G 0x772).mem (UInt8.ofNat n)) || UInt8.ofNat n == 3) = true := by native_decide
theorem play_prot : [H, Q, R, E, T, A, B, Z].all (fun c => c.protFn (0x770 &&& 0x7FF) && c.protFn (0x772 &&& 0x7FF)) = true := by native_decide

theorem regs_play (r : Region) (hr : r ∈ regions) : r.prot (0x770 &&& 0x7FF) = true ∧ r.prot (0x772 &&& 0x7FF) = true := by
  have h := play_prot
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [reg]

/-- A state in a region has the shared bounds. -/
theorem glob_of_finv {rs : List Region} {s : NES} (h : FInv rom G rs (reg Z) s) (i : UInt16) : (gAt G i).mem (ramAt s i) = true := by
  obtain ⟨_, _, r, _, ram0, ⟨t, _, ⟨b, _, hb⟩, hrel⟩, _⟩ := h
  by_cases hl : i < 0x800
  · have e : ramAt s i = t.ram i := by
      have e1 : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
        rcases hrel with h1 | ⟨_, h1⟩
        · exact h1.ram i
        · exact h1.ram i
      rw [Smb.Routine.and7ff_of_lt i hl] at e1
      simpa [ramAt, Smb.Routine.and7ff_of_lt i hl] using e1
    rw [e]; exact hb.glob i
  · have : gAt G i = .top := by
      have hn : ¬ i.toNat < G.size := by
        rw [gsize]; intro h; exact hl (by simpa [UInt16.lt_iff_toNat_lt] using h)
      simp [gAt, Array.getD, hn]
    rw [this]; rfl

/-- `Clean` after a step, from `NoOverflow`'s form of it. -/
theorem cleanIf_step {rs : List Region} {done : UInt16 → Bool} (hf : Fits rom G rs done) (hz : ZFits rs (reg Z)) (hs : ∀ r ∈ rs, r ∈ regions) {x : NES}
    (h : FInv rom G rs (reg Z) x) (hd : done x.pc = false) (hus : x.unmodelled = false) (hu : (CPU.step.run x).2.unmodelled = false)
    (hc : CleanIf (CPU.step.run x).2) : Clean G (CPU.step.run x).2 := by
  refine finv_clean hf hz h hd hus hu (fun hk => hc ?_ ?_)
  · have e : ramAt (CPU.step.run x).2 0x770 = ramAt x 0x770 := hk 0x770 (fun r hr => (regs_play r (hs r hr)).1) (by decide)
    have := forall_u8 (fun v => !((gAt G 0x770).mem v) || v == 1) g770 (ramAt x 0x770)
    rw [e]
    simpa [glob_of_finv h 0x770] using this
  · have e : ramAt (CPU.step.run x).2 0x772 = ramAt x 0x772 := hk 0x772 (fun r hr => (regs_play r (hs r hr)).2) (by decide)
    have := forall_u8 (fun v => !((gAt G 0x772).mem v) || v == 3) g772 (ramAt x 0x772)
    rw [e]
    simpa [glob_of_finv h 0x772] using this

/-! ## No DMA at the routine's entry -/

theorem q_plain : (List.range 0x8000).all (fun n => ((Q.tableWith G Smb.prg).getD n []).all fun b =>
    Q.exitFn b.pc || (checkBox rom Q.protFn G (Q.tableWith G Smb.prg) b && !onPC b.pc)) = true := by native_decide

theorem a_plain : (List.range 0x8000).all (fun n => ((A.tableWith G Smb.prg).getD n []).all fun b =>
    A.exitFn b.pc || (checkBox rom A.protFn G (A.tableWith G Smb.prg) b && !onPC b.pc)) = true := by native_decide

/-- A step that stays in a region whose boxes all pass `checkBox` is the plain machine's. -/
theorem plain_of_check {c : Config.C} (hp : (List.range 0x8000).all (fun n => ((c.tableWith G Smb.prg).getD n []).all fun b =>
      c.exitFn b.pc || (checkBox rom c.protFn G (c.tableWith G Smb.prg) b && !onPC b.pc)) = true)
    {s : NES} {ram0 : UInt16 → UInt8} (h : GInv rom c.protFn G ram0 (c.tableWith G Smb.prg) s) (hx : c.exitFn s.pc = false) :
    ∃ t c', Code rom t ∧ RelD s t ∧ t.regs.p &&& 4 ≠ 0 ∧ t.bad = false ∧ Rel (CPU.step.run s).2 (CPU.step.run ({ t with cyc := c' } : Plain)).2 := by
  obtain ⟨t, hc, ⟨b, hbm, hb⟩, hrel⟩ := h
  have hq := List.all_eq_true.mp hp (t.regs.pc &&& 0x7FFF).toNat (List.mem_range.mpr (table_at_lt _))
  have hq2 := List.all_eq_true.mp hq b hbm
  have hspc : s.pc = t.regs.pc := by
    rcases hrel with h1 | ⟨_, h1⟩
    · exact congrArg Regs.pc h1.regs
    · exact congrArg Regs.pc h1.regs
  have hbpc : b.pc = t.regs.pc := hb.pc.symm
  rw [hbpc, ← hspc, hx, Bool.false_or] at hq2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq2
  obtain ⟨hck, hon⟩ := hq2
  have hrel' : RelD s t := by
    rcases hrel with h1 | ⟨h2, _⟩
    · exact h1
    · rw [← hspc, hon] at h2; cases h2
  obtain ⟨c', hr⟩ := plain_box_rel hrel' hc hb (by rw [hbpc, ← hspc] at *; exact hck)
  exact ⟨t, c', hc, hrel', hb.i, hb.bad, hr⟩

/-- The step into the routine's entry is one of `Q`'s, so it leaves nothing latched, and the routine's refinement applies. -/
theorem routine_quiet {s : NES} (h : FInv rom G rsP (reg Z) s) (hd : stopP s.pc = false) (hus : s.unmodelled = false)
    (hu : (CPU.step.run s).2.unmodelled = false) (hA : CleanIf (CPU.step.run s).2) (hpc : (CPU.step.run s).2.pc = 0xB0E9) :
    (CPU.step.run s).2.Quiet := by
  have hC := cleanIf_step fits_rsP (zfits_of rsP_sub) rsP_sub h hd hus hu hA
  obtain ⟨_, _, r1, hr1, ram1, hi1, hx1, hi2⟩ := finv_step_region fits_rsP (zfits_of rsP_sub) h hd hus hu (fun _ => hC)
  have box {c : Config.C} (he : (c.tableWith G Smb.prg).at 0xB0E9 = []) (hg : GInv rom (reg c).prot G ram1 (reg c).T (CPU.step.run s).2) : False := by
    obtain ⟨t, _, ⟨b, hb, _⟩, hrel⟩ := hg
    have hp : (CPU.step.run s).2.pc = t.regs.pc := by
      rcases hrel with h1 | ⟨_, h1⟩
      · exact congrArg Regs.pc h1.regs
      · exact congrArg Regs.pc h1.regs
    rw [← hp, hpc] at hb
    exact no_box he hb
  simp only [rsP, List.mem_cons, List.not_mem_nil, or_false] at hr1
  rcases hr1 with rfl | rfl | rfl
  · exact (box (pH.2.2.2 _ (by simp [entryList])) hi2).elim
  · obtain ⟨t, c', _, _, _, _, hr⟩ := plain_of_check q_plain hi1 hx1
    exact ⟨hr.size, hr.ctrl, hr.nmiPending, hr.nmiPolled, hr.dma⟩
  · exact (box (pZ.2.2.2 _ (by simp [entryList])) hi2).elim

/-! ## Into `R` -/

theorem xR808F : R.exitFn 0x808F = false := by native_decide

theorem reg_R_ne : reg R ≠ reg Z := by
  intro e
  have e1 : R.exitFn = Z.exitFn := congrArg Region.exit e
  have e2 := congrFun e1 0x808F
  rw [xR808F, x808F] at e2
  cases e2

theorem sch_stepN (n : Nat) (s : NES) (h : Sch s) : Sch (stepN n s) ∧ (stepN n s).prg = s.prg := by
  induction n generalizing s with
  | zero => exact ⟨h, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih _ ((Pres.step s).1 h)
    exact ⟨h1, h2.trans ((Pres.step s).2)⟩

/-- The routine's end, as a plain state, puts the machine in `R`. -/
theorem enter_r {s r : NES} {F : Plain} (hq : FInv rom G rsP (reg Z) s) (hs : s.pc = 0xB0E9) (hS : Sch r) (hP : r.prg = Smb.prg) (hrel : Rel r F) (hcode : Code rom F)
    (hx : Exit (ramAt s) F.ram) (hlow : F.ram 0x86 < 0x50) (hpage : F.ram 0x6D = 0) (hpc : F.regs.pc = 0xB179) (hsp : F.regs.s = 0xF7) (hi : F.regs.p &&& 4 ≠ 0) (hbad : F.bad = false) :
    FInv rom G rsM (reg Z) r := by
  obtain ⟨ram0, t, b, _, hbm, hb, hr, _, _⟩ := at_routine hq hs
  obtain ⟨e, he⟩ : ∃ e, e ∈ R.entries := List.exists_mem_of_ne_nil _ r_ne
  have hh := exit_holds hb hbm hr he hx hlow hpage hpc hsp hi hbad
  exact FInv.of_start hS hP (r := reg R) (by simp [rsM]) reg_R_ne (ram0 := F.ram)
    ⟨F, hcode, inv_of_entry (List.all_eq_true.mp pR.2.1 e he) hh, Or.inl (RelD.of_rel hrel)⟩

/-! ## `SaveAB` -/

theorem rom67 : rom 0xAF67 = 0xA5 ∧ rom 0xAF68 = 0x0A ∧ rom 0xAF69 = 0x85 ∧ rom 0xAF6A = 0x0D := by native_decide

theorem step_lda {t : Plain} (h0 : t.regs.pc = 0xAF67) (hc : Code rom t) (hi : t.regs.p &&& 4 ≠ 0) :
    (CPU.step.run t).2.regs.pc = 0xAF69 ∧ (CPU.step.run t).2.regs.a = t.ram 0x0A ∧ (CPU.step.run t).2.ram = t.ram ∧ (CPU.step.run t).2.prg = t.prg ∧
      (CPU.step.run t).2.bad = t.bad ∧ (CPU.step.run t).2.regs.p &&& 4 ≠ 0 := by
  have hop : t.prg (t.regs.pc &&& 0x7FFF) = 165 := by rw [h0, hc 0xAF67 (by decide)]; exact rom67.1
  have hb1 : b1Of t = 0x0A := by
    show t.prg (t.regs.pc + 1 &&& 0x7FFF) = _
    rw [h0, hc (0xAF67 + 1) (by decide)]; exact rom67.2.1
  have hgo : ∀ w : UInt8, nz t.regs.p w &&& 4 ≠ 0 := by
    intro w
    simp only [nz, CPU.FN, CPU.FZ]
    generalize t.regs.p = p at *
    clear hop hb1
    split <;> revert hi <;> bv_decide (config := { enums := false })
  have hok : accessOk (decode 165) (b1Of t) (b2Of t) t.regs (loOf t (decode 165)) (hiOf t (decode 165)) = true := by
    simp [decode, accessOk]
  have hi' : (evalS t (decode 165)).regs.p &&& 4 ≠ 0 := by
    simpa [evalS, decode, eval] using hgo _
  obtain ⟨h1, h2, h3, h4⟩ := t_a5 t (by rw [h0]; decide) (by rw [h0]; decide) hop hi hok hi'
  have hv : vOf t (decode 165) = t.ram 0x0A := by
    simp [vOf, decode, operandAddr, ea, hb1, Plain.memRead, Plain.inRam, mr, base]
  refine ⟨?_, ?_, ?_, h2, h4, by rw [h1]; exact hi'⟩
  · rw [h1]; simp [evalS, decode, eval, h0, Mode.size]
  · rw [h1]; simp [evalS, eval, decode] ; simpa [decode] using hv
  · rw [h3]; simp [evalS, eval, decode, applyW]

theorem step_sta {t : Plain} (h0 : t.regs.pc = 0xAF69) (hc : Code rom t) (hi : t.regs.p &&& 4 ≠ 0) :
    (CPU.step.run t).2.regs.pc = 0xAF6B ∧ (∀ i : UInt16, (CPU.step.run t).2.ram i = bif i == 0x0D then t.regs.a else t.ram i) := by
  have hop : t.prg (t.regs.pc &&& 0x7FFF) = 133 := by rw [h0, hc 0xAF69 (by decide)]; exact rom67.2.2.1
  have hb1 : b1Of t = 0x0D := by
    show t.prg (t.regs.pc + 1 &&& 0x7FFF) = _
    rw [h0, hc (0xAF69 + 1) (by decide)]; exact rom67.2.2.2
  have hok : accessOk (decode 133) (b1Of t) (b2Of t) t.regs (loOf t (decode 133)) (hiOf t (decode 133)) = true := by
    simp [decode, accessOk, ea, hb1]
  have hi' : (evalS t (decode 133)).regs.p &&& 4 ≠ 0 := by
    simpa [evalS, decode, eval] using hi
  obtain ⟨h1, _, h3, _⟩ := t_85 t (by rw [h0]; decide) (by rw [h0]; decide) hop hi hok hi'
  refine ⟨?_, fun i => ?_⟩
  · rw [h1]; simp [evalS, decode, eval, h0, Mode.size]
  · rw [h3]
    simp [evalS, eval, decode, applyW, ea, hb1, regOf]

/-- `SaveAB` alone, as a run. -/
def rsA : List Region := [reg A]

def stopS (pc : UInt16) : Bool := stop pc || pc == 0xAF6B

theorem rsA_sub (r : Region) (hr : r ∈ rsA) : r ∈ regions := by
  simp only [rsA, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  simp [regions]

theorem fits_rsA : Fits rom G rsA stopS := by
  refine ⟨fun r hr => reg_chk r (rsA_sub r hr), fun r hr => reg_idle r (rsA_sub r hr), fun r hr => reg_entries r (rsA_sub r hr), ?_⟩
  intro r hr pc hx
  simp only [rsA, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  have h := List.all_eq_true.mp exA pc (exit_mem hx)
  exact Or.inl h

theorem xA808F : A.exitFn 0x808F = false := by native_decide
theorem xB808F : B.exitFn 0x808F = false := by native_decide

theorem reg_ne_of {c : Config.C} (h : c.exitFn 0x808F = false) : reg c ≠ reg Z := by
  intro e
  have e1 : c.exitFn = Z.exitFn := congrArg Region.exit e
  have e2 := congrFun e1 0x808F
  rw [h, x808F] at e2
  cases e2

theorem stopS67 : stopS 0xAF67 = false := by native_decide
theorem stopS69 : stopS 0xAF69 = false := by native_decide
theorem xA67 : A.exitFn 0xAF67 = false := by native_decide
theorem xA69 : A.exitFn 0xAF69 = false := by native_decide

/-- `SaveAB`: two instructions copy `$0A` to `$0D`, and the machine goes on in `B`. -/
theorem save_ab {s : NES} (h : FInv rom G rsM (reg Z) s) (hpc : s.pc = 0xAF67) (hus : s.unmodelled = false) (hu1 : (stepN 1 s).unmodelled = false)
    (hA1 : CleanIf (stepN 1 s)) (hu2 : (stepN 1 s).pc = 0xAF69 → (stepN 2 s).unmodelled = false) (hA2 : (stepN 1 s).pc = 0xAF69 → CleanIf (stepN 2 s)) :
    (stepN 1 s).pc = 0xAF69 ∧ FInv rom G rsT (reg Z) (stepN 2 s) ∧ (stepN 2 s).pc = 0xAF6B ∧ ramAt (stepN 2 s) 0x0D = ramAt s 0x0A ∧
      ∀ a : UInt16, a < 0x800 → a ≠ 0x0D → ramAt (stepN 2 s) a = ramAt s a := by
  obtain ⟨hS, hP, r, hr, ram0, hi, _⟩ := h
  have hA0 : FInv rom G rsA (reg Z) s := by
    simp only [rsM, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨t, _, ⟨b, hb, _⟩, hrel⟩ := hi
      have hp : s.pc = t.regs.pc := by
        rcases hrel with h1 | ⟨_, h1⟩
        · exact congrArg Regs.pc h1.regs
        · exact congrArg Regs.pc h1.regs
      rw [← hp, hpc] at hb
      exact (no_box (pR.2.2.2 _ (by simp [saveList])) hb).elim
    · obtain ⟨t, _, ⟨b, hb, _⟩, hrel⟩ := hi
      have hp : s.pc = t.regs.pc := by
        rcases hrel with h1 | ⟨_, h1⟩
        · exact congrArg Regs.pc h1.regs
        · exact congrArg Regs.pc h1.regs
      rw [← hp, hpc] at hb
      exact (no_box (pE.2.2.2 _ (by simp [saveList])) hb).elim
    · exact FInv.hop (r' := reg A) (reg_ne_of xA808F) (by simp [rsA]) (by rw [hpc]; exact pT.2.2.1 (0xAF67, A.entries) (by simp)) pA.2.1 hS hP hi
  have one {x : NES} {q : UInt16} (hF : FInv rom G rsA (reg Z) x) (hq : x.pc = q) (hsq : stopS q = false) (hxq : A.exitFn q = false) (hux : x.unmodelled = false)
      (hun : (CPU.step.run x).2.unmodelled = false) (hAn : CleanIf (CPU.step.run x).2) :
      FInv rom G rsA (reg Z) (CPU.step.run x).2 ∧ ∃ t c, Code rom t ∧ RelD x t ∧ t.regs.p &&& 4 ≠ 0 ∧ t.bad = false ∧ Rel (CPU.step.run x).2 (CPU.step.run ({ t with cyc := c } : Plain)).2 := by
    have hC := cleanIf_step fits_rsA (zfits_of rsA_sub) rsA_sub hF (by rw [hq]; exact hsq) hux hun hAn
    obtain ⟨_, hn, r1, hr1, ram1, hi1, _, _⟩ := finv_step_region fits_rsA (zfits_of rsA_sub) hF (by rw [hq]; exact hsq) hux hun (fun _ => hC)
    simp only [rsA, List.mem_cons, List.not_mem_nil, or_false] at hr1
    subst hr1
    exact ⟨hn, plain_of_check a_plain hi1 (by rw [hq]; exact hxq)⟩
  obtain ⟨hF1, t, c, hc, hrel, hI, _, hR⟩ := one hA0 hpc stopS67 xA67 hus hu1 hA1
  have htpc : t.regs.pc = 0xAF67 := by rw [← hpc]; exact (congrArg Regs.pc hrel.regs).symm
  obtain ⟨l1, l2, l3, _, _, l6⟩ := step_lda (t := { t with cyc := c }) htpc (fun a ha => hc a ha) hI
  have h1pc : (stepN 1 s).pc = 0xAF69 := (congrArg Regs.pc hR.regs).trans l1
  obtain ⟨hF2, t2, c2, hc2, hrel2, hI2, _, hR2⟩ := one hF1 h1pc stopS69 xA69 hu1 (hu2 h1pc) (hA2 h1pc)
  have ht2pc : t2.regs.pc = 0xAF69 := by rw [← h1pc]; exact (congrArg Regs.pc hrel2.regs).symm
  obtain ⟨m1, m2⟩ := step_sta (t := { t2 with cyc := c2 }) ht2pc (fun a ha => hc2 a ha) hI2
  have hS2 : Sch (stepN 2 s) ∧ (stepN 2 s).prg = s.prg := sch_stepN 2 s hS
  have h2pc : (stepN 2 s).pc = 0xAF6B := (congrArg Regs.pc hR2.regs).trans m1
  have hka : t2.regs.a = t.ram 0x0A := by
    have e1 : (stepN 1 s).a = t2.regs.a := congrArg Regs.a hrel2.regs
    have e2 : (stepN 1 s).a = (CPU.step.run ({ t with cyc := c } : Plain)).2.regs.a := congrArg Regs.a hR.regs
    rw [← e1, e2, l2]
  have hr0 : ∀ a : UInt16, a < 0x800 → ramAt s a = t.ram a := fun a ha => by
    have := hrel.ram a
    rw [Smb.Routine.and7ff_of_lt a ha] at this
    simpa [ramAt, Smb.Routine.and7ff_of_lt a ha] using this
  have hr1 : ∀ a : UInt16, a < 0x800 → t2.ram a = t.ram a := fun a ha => by
    have e1 := hrel2.ram a
    have e2 := hR.ram a
    rw [Smb.Routine.and7ff_of_lt a ha] at e1 e2
    have e3 : t2.ram a = (CPU.step.run ({ t with cyc := c } : Plain)).2.ram a := e1.symm.trans e2
    rw [e3, l3]
  have hr2 : ∀ a : UInt16, a < 0x800 → ramAt (stepN 2 s) a = bif a == 0x0D then t2.regs.a else t2.ram a := fun a ha => by
    have e1 := hR2.ram a
    rw [Smb.Routine.and7ff_of_lt a ha] at e1
    have e2 : ramAt (stepN 2 s) a = (stepN 2 s).ram.get! a.toNat := by simp [ramAt, Smb.Routine.and7ff_of_lt a ha]
    rw [e2]
    exact e1.trans (m2 a)
  refine ⟨h1pc, ?_, h2pc, ?_, fun a ha hne => ?_⟩
  · obtain ⟨_, _, r3, hr3, ram3, hi3, _⟩ := hF2
    simp only [rsA, List.mem_cons, List.not_mem_nil, or_false] at hr3
    subst hr3
    exact FInv.hop (r' := reg B) (reg_ne_of xB808F) (by simp [rsT]) (by rw [h2pc]; exact pA.2.2.1 (0xAF6B, B.entries) (by simp)) pB.2.1 hS2.1 (hS2.2.trans hP) hi3
  · rw [hr2 _ (by decide), hr0 _ (by decide)]
    simp [hka]
  · rw [hr2 a ha, hr0 a ha, hr1 a ha]
    simp [hne]

/-! ## A whole frame -/

/-- The cells each run protects: the model's, the position, the screen's edges, and the two that carry the A button. -/
def keptAll : List UInt16 := [0x57, 0x705, 0x700, 0x33, 0x45, 0x1D, 0x703, 0xCE, 0x416, 0x9F, 0x433, 0x709, 0x70A, 0x708, 0x706, 0x86, 0x6D, 0x400, 0x71A, 0x71B, 0x71C, 0x71D, 0x0A, 0x0D]

theorem kept_prot : [H, Q, R, E, T, B, Z].all (fun c => keptAll.all fun a => c.protFn (a &&& 0x7FF)) = true := by native_decide

theorem kept_lt : keptAll.all (fun a => decide (a < 0x800)) = true := by native_decide

theorem kept_of {c : Config.C} (hc : c ∈ [H, Q, R, E, T, B, Z]) {a : UInt16} (ha : a ∈ keptAll) : (reg c).prot (a &&& 0x7FF) = true :=
  List.all_eq_true.mp (List.all_eq_true.mp kept_prot c hc) a ha

theorem keptP {a : UInt16} (ha : a ∈ keptAll) (r : Region) (hr : r ∈ rsP) : r.prot (a &&& 0x7FF) = true := by
  simp only [rsP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact kept_of (by simp) ha

theorem keptM {a : UInt16} (ha : a ∈ keptAll) (r : Region) (hr : r ∈ rsM) : r.prot (a &&& 0x7FF) = true := by
  simp only [rsM, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact kept_of (by simp) ha

theorem keptT {a : UInt16} (ha : a ∈ keptAll) (r : Region) (hr : r ∈ rsT) : r.prot (a &&& 0x7FF) = true := by
  simp only [rsT, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact kept_of (by simp) ha

/-- `$783` isn't protected before the routine, where the timers tick, only after. -/
theorem t783_prot : [R, E, T, B, Z].all (fun c => c.protFn (0x783 &&& 0x7FF)) = true := by native_decide

theorem t783_of {c : Config.C} (hc : c ∈ [R, E, T, B, Z]) : (reg c).prot (0x783 &&& 0x7FF) = true :=
  List.all_eq_true.mp t783_prot c hc

theorem t783M (r : Region) (hr : r ∈ rsM) : r.prot (0x783 &&& 0x7FF) = true := by
  simp only [rsM, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact t783_of (by simp)

theorem t783T (r : Region) (hr : r ∈ rsT) : r.prot (0x783 &&& 0x7FF) = true := by
  simp only [rsT, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact t783_of (by simp)

/-- The routine's run, ending as `ModelFrame` has it. -/
structure RoutineRun (s : NES) (m : Nat) (F : Plain) : Prop where
  rel : Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 F
  pc : F.regs.pc = 0xB179
  sp : F.regs.s = 0xF7
  i : F.regs.p &&& 4 ≠ 0
  bad : F.bad = false
  code : Code rom F
  exit : Exit (ramAt s) F.ram
  low : F.ram 0x86 < 0x50
  page : F.ram 0x6D = 0

/-- A run's invariant and kept cells, with `Clean` coming from `CleanIf` along the way. -/
theorem seg_x {rs : List Region} {done : UInt16 → Bool} (hf : Fits rom G rs done) (hz : ZFits rs (reg Z)) (hs : ∀ r ∈ rs, r ∈ regions) (n : Nat) (x : NES)
    (hd : ∀ i, i < n → done (stepN i x).pc = false) (hu : ∀ i, i ≤ n → (stepN i x).unmodelled = false) (hA : ∀ i, i < n → CleanIf (stepN (i + 1) x))
    (h : FInv rom G rs (reg Z) x) :
    FInv rom G rs (reg Z) (stepN n x) ∧ ∀ y : UInt16, (∀ r ∈ rs, r.prot (y &&& 0x7FF) = true) → ramAt (stepN n x) y = ramAt x y := by
  induction n generalizing x with
  | zero => exact ⟨h, fun _ _ => rfl⟩
  | succ n ih =>
    have hC := cleanIf_step hf hz hs h (hd 0 (Nat.succ_pos _)) (hu 0 (Nat.zero_le _)) (hu 1 (by omega)) (hA 0 (Nat.succ_pos _))
    obtain ⟨_, hn, hk⟩ := finv_step_keep hf hz h (hd 0 (Nat.succ_pos _)) (hu 0 (Nat.zero_le _)) (hu 1 (by omega)) hC
    obtain ⟨g1, g2⟩ := ih (CPU.step.run x).2 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi)) (fun i hi => hu (i + 1) (Nat.succ_le_succ hi))
      (fun i hi => hA (i + 1) (Nat.succ_lt_succ hi)) hn
    exact ⟨g1, fun y hy => (g2 y hy).trans (hk y hy)⟩

/-- What a run from `a` for `n` instructions gives, from what's known of the whole frame. -/
theorem seg {rs : List Region} {done : UInt16 → Bool} (hf : Fits rom G rs done) (hz : ZFits rs (reg Z)) (hs : ∀ r ∈ rs, r ∈ regions) {s0 : NES} {j a n : Nat}
    (hu : ∀ i, i ≤ j → (stepN i s0).unmodelled = false) (hA : ∀ i, i < j → CleanIf (stepN (i + 1) s0)) (ha : a + n ≤ j)
    (hd : ∀ i, i < n → done (stepN i (stepN a s0)).pc = false) (h : FInv rom G rs (reg Z) (stepN a s0)) :
    FInv rom G rs (reg Z) (stepN n (stepN a s0)) ∧
      ∀ x : UInt16, (∀ r ∈ rs, r.prot (x &&& 0x7FF) = true) → ramAt (stepN n (stepN a s0)) x = ramAt (stepN a s0) x := by
  have hu' : ∀ i, i ≤ n → (stepN i (stepN a s0)).unmodelled = false := fun i hi => by
    rw [← stepN_add]; exact hu _ (by omega)
  have hA' : ∀ i, i < n → CleanIf (stepN (i + 1) (stepN a s0)) := fun i hi => by
    rw [← stepN_add]; exact hA (a + i) (by omega)
  exact seg_x hf hz hs n _ hd hu' hA' h

/-- **A launch frame.** From the idle loop to the idle loop: the bounds and regions hold again at the end, and either the routine didn't run and the cells are as they were, or it ran once and they're as it left them. -/
theorem frame_run (s0 : NES) (j : Nat) (h0 : FInv rom G rsP (reg Z) s0)
    (hu : ∀ i, i ≤ j → (stepN i s0).unmodelled = false) (hA : ∀ i, i < j → CleanIf (stepN (i + 1) s0))
    (hstart : s0.pc ≠ 0xB0E9) (hend : (stepN j s0).pc = 0x8057)
    (hrun : ∀ s : NES, s.pc = 0xB0E9 → s.Quiet → s.prg = Smb.prg → s.s = 0xF7 → (s.p &&& 4 == 0) = false → (∀ i, (gAt G i).mem (ramAt s i) = true) →
      (∀ a ∈ keptAll, ramAt s a = ramAt s0 a) → ∃ m F, RoutineRun s m F)
    (hcut : ∀ k k2, k ≤ j → (stepN k s0).pc = 0xB0E9 → (stepN (k + k2) s0).pc = 0xB179 → k + k2 ≤ j)
    (hT : ∀ i, i ≤ j → (stepN i s0).pc ≠ 0xB79A)
    (hN : ∀ i i', i ≤ i' → i' ≤ j → (stepN i s0).pc = 0xAF6B → (stepN i' s0).pc ≠ 0x808F) :
    FInv rom G rsP (reg Z) (stepN j s0) ∧
      (((∀ a ∈ keptAll, ramAt (stepN j s0) a = ramAt s0 a) ∧ ∀ i, i ≤ j → (stepN i s0).pc ≠ 0xB0E9) ∨
       ∃ k m F, k ≤ j ∧ (stepN k s0).pc = 0xB0E9 ∧ (∀ a ∈ keptAll, ramAt (stepN k s0) a = ramAt s0 a) ∧ RoutineRun (stepN k s0) m F ∧
         (stepN k s0).Quiet ∧ (stepN k s0).prg = Smb.prg ∧ (stepN k s0).s = 0xF7 ∧ ((stepN k s0).p &&& 4 == 0) = false ∧ (∀ i, (gAt G i).mem (ramAt (stepN k s0) i) = true) ∧
         (∀ a ∈ keptAll, a ≠ 0x0D → ramAt (stepN j s0) a = F.ram a) ∧ ramAt (stepN j s0) 0x0D = F.ram 0x0A ∧ ramAt (stepN j s0) 0x783 = F.ram 0x783) := by
  have zP := zfits_of rsP_sub
  have zM := zfits_of rsM_sub
  have zT := zfits_of rsT_sub
  have seg0 : ∀ n, n ≤ j → (∀ i, i < n → stopP (stepN i s0).pc = false) → FInv rom G rsP (reg Z) (stepN n s0) ∧
      ∀ x : UInt16, (∀ r ∈ rsP, r.prot (x &&& 0x7FF) = true) → ramAt (stepN n s0) x = ramAt s0 x := fun n hn hd =>
    seg (a := 0) fits_rsP zP rsP_sub hu hA (by omega) hd h0
  have back : ∀ a n, stepN n (stepN a s0) = stepN (a + n) s0 := fun a n => (stepN_add a n s0).symm
  rcases first_hit (fun x => stop x.pc) j s0 with hn | ⟨k1, hk1, hs1, hb1⟩
  · obtain ⟨g1, g2⟩ := seg0 j (Nat.le_refl _) (fun i hi => hn i (Nat.le_of_lt hi))
    refine ⟨g1, Or.inl ⟨fun a ha => g2 a (keptP ha), fun i hi e => ?_⟩⟩
    have := hn i hi
    simp [stop, e] at this
  · obtain ⟨hF1, hk1m⟩ := seg0 k1 hk1 hb1
    have hpc1 : (stepN k1 s0).pc = 0xB0E9 := stop_rsP hF1 hs1
    obtain ⟨k0, rfl⟩ : ∃ k0, k1 = k0 + 1 := by
      cases k1 with
      | zero => exact absurd hpc1 hstart
      | succ k => exact ⟨k, rfl⟩
    have hFprev := (seg0 k0 (by omega) (fun i hi => hb1 i (by omega))).1
    have hq : (stepN (k0 + 1) s0).Quiet := by
      have hp := hpc1
      rw [stepN_succ] at hp ⊢
      refine routine_quiet hFprev (hb1 k0 (by omega)) (hu k0 (by omega)) ?_ ?_ hp
      · rw [← stepN_succ]; exact hu _ hk1
      · rw [← stepN_succ]; exact hA k0 (by omega)
    obtain ⟨s, hs⟩ : ∃ s, s = stepN (k0 + 1) s0 := ⟨_, rfl⟩
    rw [← hs] at hF1 hk1m hpc1 hq
    obtain ⟨ram0, t, b, hc, hbm, hb, hr, hsp, hI⟩ := at_routine hF1 hpc1
    have hsS : s.s = 0xF7 := (congrArg Regs.s hr.regs).trans hsp
    have hsP : s.p = t.regs.p := congrArg Regs.p hr.regs
    have hG : ∀ i, (gAt G i).mem (ramAt s i) = true := fun i => by
      by_cases hl : i < 0x800
      · have e := hr.ram i
        rw [Smb.Routine.and7ff_of_lt i hl] at e
        have e2 : ramAt s i = t.ram i := by simpa [ramAt, Smb.Routine.and7ff_of_lt i hl] using e
        rw [e2]; exact hb.glob i
      · have : gAt G i = .top := by
          have hn : ¬ i.toNat < G.size := by
            rw [gsize]; intro h; exact hl (by simpa [UInt16.lt_iff_toNat_lt] using h)
          simp [gAt, Array.getD, hn]
        rw [this]; rfl
    have hkeep1 : ∀ a ∈ keptAll, ramAt s a = ramAt s0 a := fun a ha => hk1m a (keptP ha)
    have hSs : Sch s := hF1.1
    have hPs : s.prg = Smb.prg := hF1.2.1
    obtain ⟨m, F, hR⟩ := hrun s hpc1 hq hPs hsS (by rw [hsP]; simpa using hI) hG hkeep1
    obtain ⟨k2, _, hrk, _⟩ := runTo_stepN 0xB179 (m + 3000) s
    have hrel : Rel (stepN k2 s) F := by rw [← hrk]; exact hR.rel
    have hrpc : (stepN k2 s).pc = 0xB179 := (congrArg Regs.pc hrel.regs).trans hR.pc
    have e2 : stepN (k0 + 1 + k2) s0 = stepN k2 s := by rw [hs, stepN_add]
    have ha2 : k0 + 1 + k2 ≤ j := hcut (k0 + 1) k2 hk1 (by rw [← hs]; exact hpc1) (by rw [e2]; exact hrpc)
    have hSch := sch_stepN k2 s hSs
    have hFM : FInv rom G rsM (reg Z) (stepN (k0 + 1 + k2) s0) := by
      rw [e2]
      exact enter_r hF1 hpc1 hSch.1 (hSch.2.trans hPs) hrel hR.code hR.exit hR.low hR.page hR.pc hR.sp hR.i hR.bad
    have hat2' : ∀ x : UInt16, x < 0x800 → ramAt (stepN (k0 + 1 + k2) s0) x = F.ram x := fun x hl => by
      rw [e2]
      have e := hrel.ram x
      rw [Smb.Routine.and7ff_of_lt x hl] at e
      simpa [ramAt, Smb.Routine.and7ff_of_lt x hl] using e
    have hat2 : ∀ x ∈ keptAll, ramAt (stepN (k0 + 1 + k2) s0) x = F.ram x := fun x hx =>
      hat2' x (by simpa using List.all_eq_true.mp kept_lt x hx)
    rcases first_hit (fun x => stopM x.pc) (j - (k0 + 1 + k2)) (stepN (k0 + 1 + k2) s0) with hn2 | ⟨k3, hk3, hs3, hb3⟩
    · exfalso
      have g1 := (seg (a := k0 + 1 + k2) (n := j - (k0 + 1 + k2)) fits_rsM zM rsM_sub hu hA (by omega) (fun i hi => hn2 i (Nat.le_of_lt hi)) hFM).1
      rw [back, show k0 + 1 + k2 + (j - (k0 + 1 + k2)) = j by omega] at g1
      obtain ⟨_, _, r, hr3, _, ⟨t3, _, ⟨b3, hb3, _⟩, hrel3⟩, _⟩ := g1
      have hp : (stepN j s0).pc = t3.regs.pc := by
        rcases hrel3 with h1 | ⟨_, h1⟩
        · exact congrArg Regs.pc h1.regs
        · exact congrArg Regs.pc h1.regs
      rw [← hp, hend] at hb3
      simp only [rsM, List.mem_cons, List.not_mem_nil, or_false] at hr3
      rcases hr3 with rfl | rfl | rfl
      · exact no_box (pR.2.2.2 _ (by simp [idleList])) hb3
      · exact no_box (pE.2.2.2 _ (by simp [idleList])) hb3
      · exact no_box (pT.2.2.2 _ (by simp [idleList])) hb3
    · obtain ⟨hF3, hk3m⟩ := seg (a := k0 + 1 + k2) (n := k3) fits_rsM zM rsM_sub hu hA (by omega) hb3 hFM
      have hpc3 : (stepN k3 (stepN (k0 + 1 + k2) s0)).pc = 0xAF67 := by
        rcases stop_rsM hF3 hs3 with h | h
        · exact h
        · exact absurd (by rw [← back]; exact h) (hT (k0 + 1 + k2 + k3) (by omega))
      rw [back] at hF3 hpc3 hk3m
      have hlt3 : k0 + 1 + k2 + k3 ≠ j := fun e => by
        rw [e, hend] at hpc3; exact absurd hpc3 (by decide)
      have b1 : stepN 1 (stepN (k0 + 1 + k2 + k3) s0) = stepN (k0 + 1 + k2 + k3 + 1) s0 := back _ 1
      have b2 : stepN 2 (stepN (k0 + 1 + k2 + k3) s0) = stepN (k0 + 1 + k2 + k3 + 2) s0 := back _ 2
      have hne1 : (stepN 1 (stepN (k0 + 1 + k2 + k3) s0)).pc = 0xAF69 → k0 + 1 + k2 + k3 + 1 ≠ j := fun hp e => by
        rw [b1, e, hend] at hp; exact absurd hp (by decide)
      obtain ⟨h1pc', hFT, h2pc, h0D, hk5⟩ := save_ab hF3 hpc3 (hu _ (by omega)) (by rw [b1]; exact hu _ (by omega)) (by rw [b1]; exact hA _ (by omega))
        (fun hp => by have := hne1 hp; rw [b2]; exact hu _ (by omega))
        (fun hp => by have := hne1 hp; rw [b2]; exact hA (k0 + 1 + k2 + k3 + 1) (by omega))
      have hle5 : k0 + 1 + k2 + k3 + 2 ≤ j := by have := hne1 h1pc'; omega
      rw [b2] at hFT h2pc h0D hk5
      rcases first_hit (fun x => stopT x.pc) (j - (k0 + 1 + k2 + k3 + 2)) (stepN (k0 + 1 + k2 + k3 + 2) s0) with hn5 | ⟨k6, hk6, hs6, hb6⟩
      · obtain ⟨g1, g2⟩ := seg (a := k0 + 1 + k2 + k3 + 2) (n := j - (k0 + 1 + k2 + k3 + 2)) fits_rsT zT rsT_sub hu hA (by omega) (fun i hi => hn5 i (Nat.le_of_lt hi)) hFT
        rw [back, show k0 + 1 + k2 + k3 + 2 + (j - (k0 + 1 + k2 + k3 + 2)) = j by omega] at g1 g2
        refine ⟨idle_rsT g1 hend, Or.inr ⟨k0 + 1, m, F, hk1, by rw [← hs]; exact hpc1, by rw [← hs]; exact hkeep1, by rw [← hs]; exact hR, by rw [← hs]; exact hq, by rw [← hs]; exact hPs, by rw [← hs]; exact hsS, by rw [← hs, hsP]; simpa using hI, by rw [← hs]; exact hG, fun a ha hne => ?_, ?_, ?_⟩⟩
        · have hl : a < 0x800 := by simpa using List.all_eq_true.mp kept_lt a ha
          rw [g2 a (keptT ha), hk5 a hl hne, hk3m a (keptM ha), hat2 a ha]
        · have hd : (0x0D : UInt16) ∈ keptAll := by simp [keptAll]
          have ha : (0x0A : UInt16) ∈ keptAll := by simp [keptAll]
          rw [g2 _ (keptT hd), h0D, hk3m _ (keptM ha), hat2 _ ha]
        · rw [g2 _ t783T, hk5 _ (by decide) (by decide), hk3m _ t783M, hat2' _ (by decide)]
      · exfalso
        have hF6 := (seg (a := k0 + 1 + k2 + k3 + 2) (n := k6) fits_rsT zT rsT_sub hu hA (by omega) hb6 hFT).1
        have h808 := stop_rsT hF6 hs6
        rw [back] at h808
        exact hN _ _ (Nat.le_add_right _ _) (by omega) h2pc h808

end Smb.Routine.LaunchPhase
