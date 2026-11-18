import Smb.Goal.OneOne
import Smb.Routine.PlayCycle

/-! Connect the normal-cycle invariant to the exact buffer condition used by
`NoOverflow`. Initial entry, supported execution and open phase exits remain
explicit; this is not a proof of a `Deps` field or the whole-level bound. -/
namespace Smb.Goal.OneOne
open Smb Smb.Abs Smb.Routine.FrameGuard

private theorem all_u8 (p : UInt8 → Bool)
    (h : (List.range 256).all (fun n => p (UInt8.ofNat n)) = true) (v : UInt8) :
    p v = true := by
  have hv := List.all_eq_true.mp h v.toNat (List.mem_range.mpr v.toNat_lt)
  simpa using hv

theorem play_cleanIf_of_cleanAt {s : NES} (h : cleanAt s = true) :
    Smb.Routine.PlayCycle.CleanIf s := by
  intro h770 h772
  apply clean_of_cleanAt (g := Smb.Abs.PlayParser.G) ?_ ?_ ?_ h
  · intro v hv
    have hv' := all_u8 (fun v => !(decide (v ≤ 0x34)) ||
      (gAt Smb.Abs.PlayParser.G 0x300).mem v) Smb.Routine.PlayCycle.buffer_limits.1 v
    simpa [show v ≤ 0x34 from hv] using hv'
  · intro v hv
    have hv' := all_u8 (fun v => !(decide (v ≤ 0x21)) ||
      (gAt Smb.Abs.PlayParser.G 0x340).mem v) Smb.Routine.PlayCycle.buffer_limits.2 v
    simpa [show v ≤ 0x21 from hv] using hv'
  · simp [inPlay, inGame, byte, h770, h772]

theorem play_cycle_cleanAt (n : Nat) (s : NES)
    (hd : ∀ i, i < n → Smb.Routine.PlayCycle.stop (stepN i s).pc = false)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hc : ∀ i, i < n → cleanAt (stepN (i + 1) s) = true)
    (h : SavedFInv (romOf Smb.prg) Smb.Abs.PlayParser.G Smb.Routine.PlayCycle.regions
      (Smb.Routine.PlayCycle.reg Smb.Abs.PlayFrame.Z) Smb.Routine.PlayCycle.Saved s) :
    SavedFInv (romOf Smb.prg) Smb.Abs.PlayParser.G Smb.Routine.PlayCycle.regions
      (Smb.Routine.PlayCycle.reg Smb.Abs.PlayFrame.Z) Smb.Routine.PlayCycle.Saved (stepN n s) :=
  Smb.Routine.PlayCycle.normal_play_run n s hd hu
    (fun i hi => play_cleanIf_of_cleanAt (hc i hi)) h

end Smb.Goal.OneOne
