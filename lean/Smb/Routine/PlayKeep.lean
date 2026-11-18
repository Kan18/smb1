import Smb.Routine.PlayCycleFrames
import Smb.Routine.TrackStep
import Smb.Routine.Common

/-!
# Outside the player region, the cycle keeps Mario's horizontal state

The normal-play cycle's invariant (`CycleInv`) says only that *some* region's invariant holds at each instruction,
so on its own it says nothing about which cells survive a stretch of the run. Following the region along the run
(`savedFinv_step_track`) does: every region but the player region `PlayFrame.P` (`rest`) protects Mario's X speed,
position and sub-pixel, the screen edges and `Platform_X_Scroll`, and the player region is entered only at `$8175`.
So a run that starts in one of the other regions keeps those bytes until it hands over to the player region, at
`$8175` (`rest_run`).

`rest_of_exit` gets into the other regions: a cycle state at `$AF01`, where the player region returns to the
engine, is in one of them, since the player region hands over there.
-/
namespace Smb.Routine.PlayKeep
open Smb NES Smb.Abs Smb.Routine Smb.Routine.FrameGuard Smb.Routine.PlayCycle PlaySavedHandoffs

/-- The configurations that aren't entered only at `$8175`: all but the player region's. -/
def restConfigs : List Config.C := configs.filter (fun c => !c.entries.all (fun e => e.pc == 0x8175))
def rest : List Region := restConfigs.map reg

/-- The cycle's stops, and the player region's entry. -/
def doneP (pc : UInt16) : Bool := stop pc || pc == 0x8175

/-- Mario's horizontal bytes, with the speed's fraction (`$0705`), which the acceleration limit reads. -/
def hbytes : List UInt16 := [0x57, 0x86, 0x6D, 0x400, 0x71A, 0x71B, 0x71C, 0x71D, 0x3A1, 0x705]

theorem rest_protects : hbytes.all (fun a => restConfigs.all (fun c => c.protFn (a &&& 0x7FF))) = true := by
  native_decide

/-- What's left out is the player region, which exits at `$AF01`. -/
theorem left_out : configs.all (fun c => !c.entries.all (fun e => e.pc == 0x8175) || c.exitFn 0xAF01) = true := by
  native_decide

theorem rest_sub {r : Region} (hr : r ∈ rest) : r ∈ regions := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact List.mem_map.mpr ⟨c, (List.mem_filter.mp hc).1, rfl⟩

theorem rest_prot {a : UInt16} (ha : a ∈ hbytes) {r : Region} (hr : r ∈ rest) : r.prot (a &&& 0x7FF) = true := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact List.all_eq_true.mp (List.all_eq_true.mp rest_protects a ha) c hc

theorem rest_modes {r : Region} (hr : r ∈ rest) : r.prot 0x770 = true ∧ r.prot 0x772 = true := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (rest_sub hr)
  exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp modes_protected c hc)

/-- A region of the cycle whose entry box holds at a state away from `$8175` is one of the rest. -/
theorem into_rest {r' : Region} (hr' : r' ∈ regions) {e : Box} (he : e ∈ r'.entries) {t : Plain}
    {prot : UInt16 → Bool} {ram0 : UInt16 → UInt8} (hh : Holds prot PlayParser.G ram0 e t) (hpc : t.regs.pc ≠ 0x8175) :
    r' ∈ rest := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr'
  refine List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, rfl⟩
  cases hk : c.entries.all (fun e => e.pc == 0x8175) with
  | false => rfl
  | true => exact absurd (hh.pc.trans (beq_iff_eq.mp (List.all_eq_true.mp hk e he))) hpc


/-- `PlayFrame.P` and its like, the configurations entered only at `$8175`. -/
theorem p_entry {c : Config.C} (hc : c ∈ configs) (hn : c ∉ restConfigs) {q : Box} (hq : q ∈ c.entries) :
    q.pc = 0x8175 := by
  cases hk : c.entries.all (fun e => e.pc == 0x8175) with
  | true => exact beq_iff_eq.mp (List.all_eq_true.mp hk q hq)
  | false => exact absurd (List.mem_filter.mpr ⟨hc, by simp [hk]⟩) hn

/-- Mario's horizontal bytes are the same at two states. -/
def Kept (x y : NES) : Prop := ∀ a ∈ hbytes, ramAt x a = ramAt y a

theorem Kept.trans {x y z : NES} (h1 : Kept x y) (h2 : Kept y z) : Kept x z := fun a ha => (h1 a ha).trans (h2 a ha)

abbrev At (r : Region) (s : NES) : Prop := AtRegion (romOf Smb.prg) PlayParser.G (reg PlayFrame.Z) Saved r s

private theorem glob_at {r : Region} {s : NES} (h : At r s) (i : UInt16) (hi : i &&& 0x7FF = i) :
    (gAt PlayParser.G i).mem (s.ram.get! i.toNat) = true := by
  obtain ⟨_, _, ram0, ⟨t, _, ⟨b, _, hb⟩, hr⟩, _, _⟩ := h
  have he : s.ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hr with hr | ⟨_, hr⟩
    · exact hr.ram i
    · exact hr.ram i
  rw [hi] at he
  rw [he]
  exact hb.glob i

theorem modes_of {r : Region} (hr : r ∈ regions) : r.prot 0x770 = true ∧ r.prot 0x772 = true := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp modes_protected c hc)

/-- What the player region holds right after it's entered. -/
def Entered (s : NES) : Prop :=
  s.pc = 0x8175 ∧ ∃ c ∈ configs, c ∉ restConfigs ∧ At (reg c) (CPU.step.run s).2 ∧
    ∃ ram1, GInv (romOf Smb.prg) (reg c).prot PlayParser.G ram1 (reg c).T s ∧ (reg c).exit s.pc = false ∧
      GInv (romOf Smb.prg) (reg c).prot PlayParser.G ram1 (reg c).T (CPU.step.run s).2

/-- One step from one of the other regions keeps the horizontal bytes and stays among them, or is the player
region's first, at `$8175`. -/
theorem rest_step {r : Region} (hr : r ∈ rest) {s : NES} (h : At r s) (hd : stop s.pc = false)
    (hus : s.unmodelled = false) (hu : (CPU.step.run s).2.unmodelled = false) (hc : CleanIf (CPU.step.run s).2) :
    (∃ r1 ∈ rest, At r1 (CPU.step.run s).2 ∧ Kept (CPU.step.run s).2 s) ∨ Entered s := by
  obtain ⟨r1, hr1, hat, htr, ram1, hb, hx, ha⟩ := savedFinv_step_track (rest_sub hr) (fits checked)
    (zfits preambles_checked) h hd hus hu (by
      intro hk
      apply hc
      · have hkeep := hk 0x770 (fun r hr => (modes_of hr).1) (by decide)
        have hmode := elems_single mode770 (glob_at h 0x770 (by decide))
        exact hkeep.trans hmode
      · have hkeep := hk 0x772 (fun r hr => (modes_of hr).2) (by decide)
        have hmode := elems_single mode772 (glob_at h 0x772 (by decide))
        exact hkeep.trans hmode)
  by_cases hin : r1 ∈ rest
  · refine Or.inl ⟨r1, hin, hat, fun a ha' => ?_⟩
    have hp := rest_prot ha' hin
    exact (ginv_ram ha a hp).trans (ginv_ram hb a hp).symm
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr1
    have hnc : c ∉ restConfigs := fun h' => hin (List.mem_map.mpr ⟨c, h', rfl⟩)
    rcases htr with e | ⟨_, q, hq, hqpc⟩
    · rw [e] at hin; exact absurd hr hin
    · exact Or.inr ⟨hqpc.symm.trans (p_entry hc hnc hq), c, hc, hnc, hat, ram1, hb, hx, ha⟩

/-- **Along the other regions**, until the player region is entered, the horizontal bytes are kept. -/
theorem rest_run (n : Nat) (s : NES) (r : Region) (hr : r ∈ rest) (h : At r s)
    (hd : ∀ i, i < n → stop (stepN i s).pc = false)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hc : ∀ i, i < n → CleanIf (stepN (i + 1) s)) :
    (∃ r1 ∈ rest, At r1 (stepN n s) ∧ Kept (stepN n s) s) ∨
      ∃ k, k < n ∧ Kept (stepN k s) s ∧ Entered (stepN k s) := by
  induction n generalizing s r with
  | zero => exact Or.inl ⟨r, hr, h, fun _ _ => rfl⟩
  | succ n ih =>
    rcases rest_step hr h (hd 0 (Nat.succ_pos _)) (hu 0 (Nat.zero_le _)) (hu 1 (by omega)) (hc 0 (Nat.succ_pos _)) with
      ⟨r1, hr1, h1, k1⟩ | he
    · rcases ih (CPU.step.run s).2 r1 hr1 h1 (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi))
          (fun i hi => hu (i + 1) (Nat.succ_le_succ hi)) (fun i hi => hc (i + 1) (Nat.succ_lt_succ hi)) with
        ⟨r2, hr2, h2, k2⟩ | ⟨k, hk, k2, he⟩
      · exact Or.inl ⟨r2, hr2, h2, k2.trans k1⟩
      · exact Or.inr ⟨k + 1, by omega, k2.trans k1, he⟩
    · exact Or.inr ⟨0, Nat.succ_pos _, fun _ _ => rfl, he⟩

/-- **Into the other regions**: a cycle state at `$AF01`, where the player region returns to the engine, is in one
of them. -/
theorem rest_of_exit {s : NES} (h : CycleInv s) (hx : s.pc = 0xAF01) : ∃ r ∈ rest, At r s := by
  obtain ⟨hS, hP, r, hr, ram0, hi, hs, hz⟩ := h
  by_cases hrr : r ∈ rest
  · exact ⟨r, hrr, hS, hP, ram0, hi, hs, hz⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    have hk : c.entries.all (fun e => e.pc == 0x8175) = true := by
      cases hk : c.entries.all (fun e => e.pc == 0x8175) with
      | true => rfl
      | false => exact absurd (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simp [hk]⟩, rfl⟩) hrr
    have hex : c.exitFn 0xAF01 = true := by
      have := List.all_eq_true.mp left_out c hc
      simpa [hk] using this
    obtain ⟨t, htc, ⟨b, hbm, hb⟩, hrel⟩ := hi
    have hspc : s.pc = t.regs.pc := by
      rcases hrel with h1 | ⟨_, h1⟩
      · exact congrArg Regs.pc h1.regs
      · exact congrArg Regs.pc h1.regs
    have htpc : t.regs.pc = 0xAF01 := hspc.symm.trans hx
    rcases (fits checked).link (reg c) hr ram0 b t hbm hb hs (by simpa [reg, htpc] using hex) with
      hd | ⟨r', hr', e, he, hx', hh', hs'⟩
    · rw [htpc] at hd; exact absurd hd (by decide)
    · have hin := into_rest hr' he hh' (by rw [htpc]; decide)
      refine ⟨r', hin, hS, hP, t.ram,
        ⟨t, htc, inv_of_entry (List.all_eq_true.mp ((fits checked).entries r' hr') e he) hh', hrel⟩, hs', fun ez => ?_⟩
      subst ez
      have h8 := (zfits preambles_checked).entries e he
      have := hh'.pc.trans h8
      rw [htpc] at this
      exact absurd this (by decide)

end Smb.Routine.PlayKeep
