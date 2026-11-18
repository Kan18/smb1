import Smb.Game
import Smb.RefineRun
import Smb.Routine.AbsCheck
import Smb.Routine.Common
import Smb.Routine.HorizontalLimit
import Smb.Abs.EngineTailData

/-!
# The engine's tail cannot disturb Mario's horizontal state

From `$AF10`, just after the enemy loop, to `SaveAB` `$AF67`: player graphics, block and misc objects, cannons, whirlpools, the
flagpole, the game timer and palettes, for the actual ROM. Every bounded prefix of the run keeps Mario's X position and
sub-pixel and the screen edges exactly as they were, stays within the global RAM bounds, including the X speed limit, and stays
on the plain machine. The checker accepted a computed table, and 1,225 instructions of the ROM were reached by it.

The entry conditions are hypotheses: `Holds` at the entry box and the 1,303 RAM bounds of `EngineTail.bounds`. The bounds are seeded from TAS
frames 194 to 1285 of 1-1 and were widened until the code in this region keeps them. They held at all 1,040 such entries of the movie,
but nothing here shows the enemy loop, the NMI or other inputs preserve them. It does not assert that `$AF67` is reached, and
the run involves no interrupts: on the full NES, `s.Quiet` is a hypothesis. Timing is not addressed.
-/
namespace Smb.Routine.EngineTail
open Smb.Abs Smb.Abs.EngineTail

theorem accepted_true : accepted Smb.prg = true := by native_decide

theorem speedBounded_true : speedBounded = true := by native_decide

/-- This contract doesn't bound the assumed cell, so a run needs no clean hypothesis here. -/
theorem bounds_topB : topB (gAt bounds 0x300) = true := by native_decide
theorem bounds_top : gAt bounds 0x300 = .top := eq_top_of_topB bounds_topB
theorem bounds_topB2 : topB (gAt bounds 0x340) = true := by native_decide
theorem bounds_top2 : gAt bounds 0x340 = .top := eq_top_of_topB bounds_topB2

theorem speed_of_bound {v : UInt8} (h : (gAt bounds 0x57).mem v = true) :
    HorizontalLimit.speedOk v = true := by
  have hs := speedBounded_true
  simp only [speedBounded, List.all_eq_true] at hs
  have := hs v (mem_allBytes v)
  simp only [h, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
  simpa [HorizontalLimit.speedOk] using this

/-- The tail on the plain machine. -/
theorem tail_plain (s : Plain) (hc : Code (romOf Smb.prg) s) (he : Holds prot bounds s.ram entry s) (n : Nat) :
    let t := ((CPU.runTo (σ := Plain) 0xAF67 n).run s).2
    t.bad = false ∧ (∀ i, prot i = true → t.ram i = s.ram i) ∧
      (∀ i, (gAt bounds i).mem (t.ram i) = true) ∧ HorizontalLimit.speedOk (t.ram 0x57) = true := by
  have hacc := accepted_true
  simp only [accepted, Bool.and_eq_true] at hacc
  obtain ⟨hchk, hin⟩ := hacc
  have hinv := inv_of_entry hin he
  have hrun := inv_runTo hchk bounds_top bounds_top2 0xAF67 (fun a ha => by simpa [exit] using ha) n s hc hinv
  obtain ⟨_, b, _, hb⟩ := hrun
  exact ⟨hb.bad, hb.frame, hb.glob, speed_of_bound (hb.glob 0x57)⟩

theorem code_toPlain (s : NES) (hprg : s.prg = Smb.prg) : Code (romOf Smb.prg) s.toPlain := by
  intro a _
  show s.prg.get! ((a &&& 0x7FFF) &&& 0x7FFF).toNat = Smb.prg.get! (a &&& 0x7FFF).toNat
  rw [hprg, and_idem]

/-- The tail on the full NES, for the actual ROM. -/
theorem tail_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (he : Holds prot bounds s.toPlain.ram entry s.toPlain) (n : Nat) :
    let out := ((CPU.runTo (σ := NES) 0xAF67 n).run s).2
    (∀ i : UInt16, i < 0x800 → prot i = true → ramAt out i = ramAt s i) ∧
      (∀ i : UInt16, i < 0x800 → (gAt bounds i).mem (ramAt out i) = true) ∧
      HorizontalLimit.speedOk (ramAt out 0x57) = true := by
  obtain ⟨hbad, hframe, hglob, hspeed⟩ := tail_plain s.toPlain (code_toPlain s hprg) he n
  have hrel := refine_runTo s hq 0xAF67 n hbad
  have hr0 := NES.rel_toPlain s hq
  have e (i : UInt16) (hi : i < 0x800) : ramAt ((CPU.runTo (σ := NES) 0xAF67 n).run s).2 i =
      ((CPU.runTo (σ := Plain) 0xAF67 n).run s.toPlain).2.ram i := by
    rw [ramAt_of_rel hrel, and7ff_of_lt i hi]
  have e0 (i : UInt16) (hi : i < 0x800) : ramAt s i = s.toPlain.ram i := by
    rw [ramAt_of_rel hr0, and7ff_of_lt i hi]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi hp
    rw [e i hi, e0 i hi]
    exact hframe i hp
  · intro i hi
    rw [e i hi]
    exact hglob i
  · rw [e 0x57 (by decide)]
    exact hspeed

end Smb.Routine.EngineTail
