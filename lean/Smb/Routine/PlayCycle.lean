import Smb.Routine.PlayCycleClean
import Smb.Routine.PlayFrame
import Smb.Routine.PlayEnemy
import Smb.Routine.PlayParser

/-! Supply every normal-play cycle certificate to its logical composition. -/
namespace Smb.Routine.PlayCycle
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open Smb Smb.Abs PlaySavedHandoffs

private theorem linked_of_linkedE {c : Config.C} {ns : List (UInt16 × List Box)}
    {ep : List UInt16} (h : c.linkedE PlayParser.G Smb.prg ns ep = true) :
    c.linked PlayParser.G Smb.prg ns = true := by
  simp only [Config.C.linkedE, Bool.and_eq_true] at h
  simpa only [Config.C.linked, Bool.and_eq_true] using h.1

theorem direct_checked {c : Config.C} {es : List (UInt16 × Config.C)}
    (hc : (c, es) ∈ directEdges) :
    c.linked PlayParser.G Smb.prg (es.map (fun (pc, d) => (pc, d.entries))) = true := by
  simp only [directEdges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h
  · exact linked_of_linkedE PlayFrame.acceptedH
  · exact linked_of_linkedE PlayFrame.acceptedP
  · exact linked_of_linkedE PlayEnemy.checkedFront
  · exact linked_of_linkedE PlayEnemy.checkedE0
  · exact linked_of_linkedE PlayEnemy.checkedM0
  · exact linked_of_linkedE PlayEnemy.checkedE1
  · exact linked_of_linkedE PlayEnemy.checkedM1
  · exact linked_of_linkedE PlayEnemy.checkedE2
  · exact linked_of_linkedE PlayEnemy.checkedM2
  · exact linked_of_linkedE PlayEnemy.checkedE3
  · exact linked_of_linkedE PlayEnemy.checkedM3
  · exact linked_of_linkedE PlayEnemy.checkedE4
  · exact linked_of_linkedE PlayEnemy.checkedM4
  · exact linked_of_linkedE PlayEnemy.checkedE5
  · simpa only [List.map_cons, List.map_nil, enemy_tail_entries] using
      linked_of_linkedE PlayEnemy.checkedM5
  · exact PlayFrame.acceptedZ

theorem checked : Checks where
  direct := fun {c} {es} h => direct_checked h
  parser := PlayParser.checked

theorem cycle_fits : SavedFits (romOf Smb.prg) PlayParser.G regions stop Saved :=
  fits checked

private theorem preamble_mem {pc : UInt16} (h : preamblePC pc = true) :
    pc ∈ [0x8082, 0x8085, 0x8087, 0x808A, 0x808C] := by
  simpa [preamblePC, onExit, Bool.or_eq_true_iff, beq_iff_eq, or_assoc] using h

private theorem empty_of_linkedE {c : Config.C} {ns : List (UInt16 × List Box)}
    (h : c.linkedE PlayParser.G Smb.prg ns [0x8082, 0x8085, 0x8087, 0x808A, 0x808C] = true)
    {pc : UInt16} (hp : preamblePC pc = true) :
    (c.tableWith PlayParser.G Smb.prg).at pc = [] := by
  simp only [Config.C.linkedE, Bool.and_eq_true] at h
  exact List.isEmpty_iff.mp (List.all_eq_true.mp h.2 pc (preamble_mem hp))

theorem preambles_checked : PreambleChecks := by
  intro c hc hn pc hp
  rcases List.mem_append.mp hc with hc | hc
  · simp only [PlaySavedHandoffs.normalConfigs, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact empty_of_linkedE PlayFrame.acceptedH hp
    · exact empty_of_linkedE PlayFrame.acceptedP hp
    · exact empty_of_linkedE PlayEnemy.checkedFront hp
    · exact empty_of_linkedE PlayEnemy.checkedE0 hp
    · exact empty_of_linkedE PlayEnemy.checkedM0 hp
    · exact empty_of_linkedE PlayEnemy.checkedE1 hp
    · exact empty_of_linkedE PlayEnemy.checkedM1 hp
    · exact empty_of_linkedE PlayEnemy.checkedE2 hp
    · exact empty_of_linkedE PlayEnemy.checkedM2 hp
    · exact empty_of_linkedE PlayEnemy.checkedE3 hp
    · exact empty_of_linkedE PlayEnemy.checkedM3 hp
    · exact empty_of_linkedE PlayEnemy.checkedE4 hp
    · exact empty_of_linkedE PlayEnemy.checkedM4 hp
    · exact empty_of_linkedE PlayEnemy.checkedE5 hp
    · exact empty_of_linkedE PlayEnemy.checkedM5 hp
    · have ht := PlayFrame.acceptedT
      simp only [Smb.Abs.PlayFrame.acceptedT, Bool.and_eq_true] at ht
      exact List.isEmpty_iff.mp (List.all_eq_true.mp ht.2 pc (preamble_mem hp))
    · exact (hn rfl).elim
  · have ha := List.all_eq_true.mp PlayParser.checked c hc
    simp only [Smb.Abs.PlayParser.accepted, Bool.and_eq_true] at ha
    exact List.isEmpty_iff.mp (List.all_eq_true.mp ha.2 pc (preamble_mem hp))

/-- The checked normal-play cycle, until an explicitly listed open exit. -/
theorem normal_play_run (n : Nat) (s : NES)
    (hd : ∀ i, i < n → stop (stepN i s).pc = false)
    (hu : ∀ i, i ≤ n → (stepN i s).unmodelled = false)
    (hc : ∀ i, i < n → CleanIf (stepN (i + 1) s))
    (h : Smb.Routine.FrameGuard.SavedFInv (romOf Smb.prg) PlayParser.G regions
      (reg PlayFrame.Z) Saved s) :
    Smb.Routine.FrameGuard.SavedFInv (romOf Smb.prg) PlayParser.G regions
      (reg PlayFrame.Z) Saved (stepN n s) :=
  cleanIf_invariant checked preambles_checked n s hd hu hc h

end Smb.Routine.PlayCycle
