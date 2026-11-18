import Smb.Routine.PlayCycleCore
import Smb.Routine.SavedFrameGuard

/-! PPU scheduling for the saved-tuple normal-play cycle. The finite empty-table
facts are separate from the logical argument so no checker is repeated here. -/
namespace Smb.Routine.PlayCycle
open Smb Smb.Abs Smb.Routine.FrameGuard

/-- Only the closing region can contain the NMI preamble. -/
def PreambleChecks : Prop := ∀ c ∈ configs, reg c ≠ reg PlayFrame.Z →
  ∀ pc, preamblePC pc = true → (c.tableWith PlayParser.G Smb.prg).at pc = []

theorem zfits (hp : PreambleChecks) : ZFits regions (reg PlayFrame.Z) := by
  constructor
  · intro e he
    exact beq_iff_eq.mp (List.all_eq_true.mp closing_entries e he)
  · exact closing_exit
  · intro r hr hn pc hpc
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact hp c hc hn pc hpc

/-- Arbitrarily many normal-play instructions without a separate `Guard`
assumption. Initial schedule/entry, supported execution and clean buffers remain
explicit premises; exceptional phase exits remain explicit stops. -/
theorem scheduled_invariant (checks : Checks) (hp : PreambleChecks)
    {n : Nat} {s : NES}
    (hd : ∀ i, i < n → stop (stepN i s).pc = false)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hA : ∀ i, i < n → Clean PlayParser.G (stepN (i + 1) s))
    (h : SavedFInv (romOf Smb.prg) PlayParser.G regions (reg PlayFrame.Z) Saved s) :
    SavedFInv (romOf Smb.prg) PlayParser.G regions (reg PlayFrame.Z) Saved (stepN n s) :=
  savedFinv_stepN (fits checks) (zfits hp) n s hd hu hA h

end Smb.Routine.PlayCycle
