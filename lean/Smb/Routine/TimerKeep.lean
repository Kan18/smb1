import Smb.Routine.PlayCycleCore
import Smb.Routine.AbsBridge

/-!
# The side-collision timer through the NMI handler

`XInv`'s scroll clause is about `$0785`, the side-collision timer: when the player call leaves it at `$10`, it must
still be nonzero at the next call. Only the handler region `H` writes it in between (the frame timers' `dec Timers,x`
at `$8113`), so what's needed is that `H` doesn't take it from 2 or more to 0.

`H`'s own table doesn't track `$0785`. A variant does: its entries are `H`'s boxes at `$808F` with `$0785` narrowed to
`$02`–`$80` or `$81`–`$FF` (two runs, since a tracked set over 240 values counts as unknown), `$0785` tracked, and
without `H`'s fast widening of the sound engine, which would drop it. `timerOk` checks each run's table and that every
box at `H`'s exits has `$0785` nonzero; `timer_keeps` is what that gives a run.
-/
namespace Smb.Routine.TimerKeep
open Smb Smb.Abs Smb.Abs.Config Smb.Routine.PlayCycle

def rng (lo hi : Nat) : VS := .set ((List.range (hi + 1 - lo)).map (fun n => UInt8.ofNat (lo + n)))

def hvC : Config.C := { PlayFrame.H with widen := [], track := (0x785, 0x785) :: PlayFrame.H.track }

/-- `H`'s boxes at its entry, with `$0785` narrowed to `lo`–`hi`. -/
def hvEntries (lo hi : Nat) : List Box :=
  ((reg PlayFrame.H).T.at 0x808F).map fun b => { b with cells := Cells.set b.cells 0x785 (rng lo hi) }

def hvTable (lo hi : Nat) : Table := (fixpoint (hvC.cfg (romOf Smb.prg) PlayParser.G hvC.track) (hvEntries lo hi)).table

/-- The run's table checks, contains its entries, and has `$0785` tracked and nonzero at every exit. -/
def timerOk (lo hi : Nat) : Bool :=
  let T := hvTable lo hi
  checkF (romOf Smb.prg) hvC.exitFn hvC.protFn PlayParser.G T && (hvEntries lo hi).all (entryIn PlayParser.G T) &&
    (List.range 0x8000).all fun n => (T.getD n []).all fun b => !hvC.exitFn b.pc ||
      match cellVS b.cells 0x785 with
        | some v => !v.mem 0
        | none => false

theorem timer_lo : timerOk 2 0x80 = true := by native_decide
theorem timer_hi : timerOk 0x81 0xFF = true := by native_decide

theorem mem_cells_set {l : Cells} {i : UInt16} {v : VS} {c : UInt16 × VS} (h : c ∈ Cells.set l i v) :
    c = (i, v) ∨ c ∈ l := by
  induction l with
  | nil => simp [Cells.set] at h; exact Or.inl h
  | cons d l ih =>
    obtain ⟨j, w⟩ := d
    simp only [Cells.set] at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · split at h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (h ▸ List.mem_cons_self)
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_rng {lo hi : Nat} {v : UInt8} (h1 : lo ≤ v.toNat) (h2 : v.toNat ≤ hi) (hh : hi < 256) :
    (rng lo hi).mem v = true := by
  simp only [rng, VS.mem, List.contains_iff_mem, List.mem_map, List.mem_range]
  exact ⟨v.toNat - lo, by omega, by apply UInt8.toNat_inj.mp; simp; omega⟩

/-- **`H` keeps a side-collision timer of 2 or more nonzero**: from a cycle state at `H`'s entry with `$0785` ≥ 2,
running `H`'s instructions until one of its exits, `$0785` is nonzero there. -/
theorem timer_keeps {s : NES} {ram0 : UInt16 → UInt8}
    (h : GInv (romOf Smb.prg) (reg PlayFrame.H).prot PlayParser.G ram0 (reg PlayFrame.H).T s) (hpc : s.pc = 0x808F)
    (h785 : 2 ≤ (s.ram.get! 0x785).toNat) (n : Nat)
    (hx : ∀ i, i < n → hvC.exitFn (stepN i s).pc = false) (hg : ∀ i, i < n → Guard (stepN i s))
    (hA : ∀ i, i < n → Clean PlayParser.G (stepN (i + 1) s)) (hend : hvC.exitFn (stepN n s).pc = true) :
    (stepN n s).ram.get! 0x785 ≠ 0 := by
  obtain ⟨t, hcode, ⟨b, hbm, hb⟩, hrel⟩ := h
  have hr : s.ram.get! 0x785 = t.ram 0x785 := by
    rcases hrel with hr | ⟨_, hr⟩
    · exact hr.ram 0x785
    · exact hr.ram 0x785
  have htpc : t.regs.pc = 0x808F := by
    rcases hrel with hr | ⟨_, hr⟩
    · exact (congrArg Regs.pc hr.regs).symm.trans hpc
    · exact (congrArg Regs.pc hr.regs).symm.trans hpc
  -- Which half the timer is in, and that run's facts.
  have key : ∀ lo hi, timerOk lo hi = true → hi < 256 → lo ≤ (t.ram 0x785).toNat → (t.ram 0x785).toNat ≤ hi →
      (stepN n s).ram.get! 0x785 ≠ 0 := by
    intro lo hi hok hh hlo hhi
    simp only [timerOk, Bool.and_eq_true, List.all_eq_true] at hok
    obtain ⟨⟨hchk, hent⟩, hexit⟩ := hok
    let e : Box := { b with cells := Cells.set b.cells 0x785 (rng lo hi) }
    have he : e ∈ hvEntries lo hi := List.mem_map.mpr ⟨b, by rw [← htpc]; exact hbm, rfl⟩
    have hcells : ∀ c ∈ e.cells, c.2.mem (t.ram c.1) = true := by
      intro c hc
      rcases mem_cells_set hc with rfl | hc
      · exact mem_rng hlo hhi hh
      · exact hb.cells c hc
    have hhe : Holds hvC.protFn PlayParser.G ram0 e t := { hb with cells := hcells }
    have hinv := inv_of_entry (hent e he) hhe
    have hg0 : GInv (romOf Smb.prg) hvC.protFn PlayParser.G ram0 (hvTable lo hi) s := ⟨t, hcode, hinv, hrel⟩
    have hidle : hvC.exitFn idlePC = false := by
      show PlayFrame.H.exitFn idlePC = false
      have := List.all_eq_true.mp idle_go PlayFrame.H (by simp [PlaySavedHandoffs.normalConfigs])
      simpa using this
    obtain ⟨t', _, ⟨b', hbm', hb'⟩, hrel'⟩ := ginv_stepN hchk hidle n s hx hg hA hg0
    have hpc' : b'.pc = (stepN n s).pc := by
      rcases hrel' with hr | ⟨_, hr⟩
      · exact hb'.pc.symm.trans (congrArg Regs.pc hr.regs).symm
      · exact hb'.pc.symm.trans (congrArg Regs.pc hr.regs).symm
    rw [hb'.pc, hpc'] at hbm'
    have hcell := hexit _ (List.mem_range.mpr (table_at_lt (stepN n s).pc)) b' (by simpa [Table.at] using hbm')
    rw [hpc', hend, Bool.not_true, Bool.false_or] at hcell
    have hram : (stepN n s).ram.get! 0x785 = t'.ram 0x785 := by
      rcases hrel' with hr | ⟨_, hr⟩
      · exact hr.ram 0x785
      · exact hr.ram 0x785
    rw [hram]
    intro h0
    cases hv : cellVS b'.cells 0x785 with
    | none => rw [hv] at hcell; cases hcell
    | some v =>
      rw [hv] at hcell
      have hm := hb'.cells _ (cellVS_sound hv)
      simp only at hm
      rw [h0] at hm
      simp [hm] at hcell
  rw [hr] at h785
  by_cases hm : (t.ram 0x785).toNat ≤ 0x80
  · exact key 2 0x80 timer_lo (by decide) h785 hm
  · exact key 0x81 0xFF timer_hi (by decide) (by omega) (by have := (t.ram 0x785).toNat_lt; omega)

end Smb.Routine.TimerKeep
