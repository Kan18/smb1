import Smb.Game
import Smb.Routine.AbsBridge
import Smb.Abs.HandlerFrameData

/-!
# The NMI handler, over any number of frames

The handler's table for the actual ROM: from `$808F`, with the game logic's call at `$8175` as an exit. Every state it reaches, at every
instruction, for any controller input and any PPU timing, stays in the table: so RAM stays within the region's bounds and Mario's position and the
game mode are written only as the table allows, until the game logic is called. This covers paused frames in full, and in every other frame
the part before the game logic.

The entry conditions are hypotheses, and so is `Guard` at each step: no NMI edge during the handler's first instructions. Nothing here says the entry state
is reached.
-/
namespace Smb.Routine.HandlerFrame
open Smb.Abs Smb.Abs.HandlerFrame

theorem accepted_true : conf.acceptedF Smb.prg = true := by native_decide

theorem idle_not_exit : conf.exitFn idlePC = false := by native_decide

theorem code_toPlain (s : NES) (hprg : s.prg = Smb.prg) : Code (romOf Smb.prg) s.toPlain := by
  intro a _
  show s.prg.get! ((a &&& 0x7FFF) &&& 0x7FFF).toNat = Smb.prg.get! (a &&& 0x7FFF).toNat
  rw [hprg, and_idem]

/-- This region doesn't bound the assumed cell, so a run needs no clean hypothesis here. -/
theorem globals_topB : topB (gAt conf.globals 0x300) = true := by native_decide
theorem globals_top : gAt conf.globals 0x300 = .top := eq_top_of_topB globals_topB
theorem globals_topB2 : topB (gAt conf.globals 0x340) = true := by native_decide
theorem globals_top2 : gAt conf.globals 0x340 = .top := eq_top_of_topB globals_topB2

/-- The handler's invariant, over any number of instructions: until the game logic is called, for any input and PPU timing. -/
theorem frames (s : NES) (n : Nat) (hprg : s.prg = Smb.prg) (hq : s.Quiet)
    (he : ∃ e ∈ conf.entries, Holds conf.protFn conf.globals s.toPlain.ram e s.toPlain)
    (hx : ∀ i, i < n → conf.exitFn (stepN i s).pc = false) (hg : ∀ i, i < n → Guard (stepN i s)) :
    GInv (romOf Smb.prg) conf.protFn conf.globals s.toPlain.ram (conf.table Smb.prg) (stepN n s) := by
  have hacc := accepted_true
  simp only [Config.C.acceptedF, Bool.and_eq_true, List.all_eq_true] at hacc
  obtain ⟨hchk, hin⟩ := hacc
  obtain ⟨e, hem, hh⟩ := he
  refine ginv_stepN hchk idle_not_exit n s hx hg (fun _ _ => clean_of_top globals_top globals_top2 _) ⟨s.toPlain, code_toPlain s hprg, inv_of_entry (hin e hem) hh, Or.inl ?_⟩
  exact RelD.of_rel (NES.rel_toPlain s hq)

/-- So RAM stays within the region's bounds. -/
theorem frames_bounds (s : NES) (n : Nat) (hprg : s.prg = Smb.prg) (hq : s.Quiet)
    (he : ∃ e ∈ conf.entries, Holds conf.protFn conf.globals s.toPlain.ram e s.toPlain)
    (hx : ∀ i, i < n → conf.exitFn (stepN i s).pc = false) (hg : ∀ i, i < n → Guard (stepN i s)) (i : UInt16) (hi : i < 0x800) :
    (gAt conf.globals i).mem ((stepN n s).ram.get! i.toNat) = true := by
  obtain ⟨t, _, ⟨b, _, hb⟩, hr⟩ := frames s n hprg hq he hx hg
  have hm : i &&& 0x7FF = i := by revert hi; bv_decide (config := { enums := false })
  have h1 := hb.glob i
  have h2 : (stepN n s).ram.get! (i &&& 0x7FF).toNat = t.ram (i &&& 0x7FF) := by
    rcases hr with hr | ⟨_, hr⟩
    · exact hr.ram i
    · exact hr.ram i
  rw [hm] at h2
  rw [h2]
  exact h1

end Smb.Routine.HandlerFrame
