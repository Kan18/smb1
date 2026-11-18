import Smb.Routine.PlayTailCommonFacts
import Smb.Routine.PlayParserClosure
import Smb.Routine.PlayFrameLinks

/-! The two state-dependent handoffs in normal play. Parser entries are chosen
from a saved chain tuple; closing entries are chosen from a saved object tuple.
Both transfers also produce the witness required for the next phase. -/
namespace Smb.Routine.PlaySavedHandoffs
open Smb Smb.Abs

/-- A realizable parser entry's protected chain cells. -/
def ChainSaved (ram : UInt16 → UInt8) : Prop :=
  ∃ e ∈ PlayParser.entryTuples, ∀ k ∈ e.cells,
    PlayParser.chainCells.contains k.1 = true → k.2.mem (ram k.1) = true

/-- A closing entry's two object cells. -/
def ObjectSaved (ram : UInt16 → UInt8) : Prop :=
  ∃ e ∈ PlayFrame.Z.entries, ∀ k ∈ e.cells,
    PlayFrameLinks.objectCells k.1 = true → k.2.mem (ram k.1) = true

theorem tail_to_parser {ram0 : UInt16 → UInt8} {b : Box} {s : Plain}
    (hb : b ∈ (PlayFrame.T.tableWith PlayParser.G Smb.prg).at 0xAF67)
    (h : Holds PlayFrame.T.protFn PlayParser.G ram0 b s)
    (saved : ChainSaved ram0) :
    ∃ c ∈ PlayParser.chunks, ∃ e ∈ c.entries,
      Holds c.protFn PlayParser.G s.ram e s ∧ ObjectSaved s.ram := by
  obtain ⟨e, he, hs⟩ := saved
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
  exact ⟨c, hc, e, he, PlayFrame.parser_entry hc he hb h hs,
    PlayFrame.return_object_tuple hb h⟩

theorem parser_to_closing {c : Config.C} {ram0 : UInt16 → UInt8}
    {b : Box} {s : Plain} (hc : c ∈ PlayParser.chunks)
    (ha : PlayParser.accepted Smb.prg c = true)
    (hb : b ∈ (c.tableWith PlayParser.G Smb.prg).at 0x8178)
    (h : Holds c.protFn PlayParser.G ram0 b s)
    (saved : ObjectSaved ram0) :
    ∃ e ∈ PlayFrame.Z.entries,
      Holds PlayFrame.Z.protFn PlayParser.G s.ram e s ∧ ChainSaved s.ram := by
  obtain ⟨e, he, hs⟩ := saved
  exact ⟨e, he, PlayFrameLinks.parser_closing_entry hc ha hb h he hs,
    PlayParser.return_tuple hc hb h⟩

/-- Normal phases between successive parser runs. -/
def normalConfigs : List Config.C :=
  [PlayFrame.H, PlayFrame.P, PlayEnemy.Front,
   PlayEnemy.E0, PlayEnemy.M0, PlayEnemy.E1, PlayEnemy.M1,
   PlayEnemy.E2, PlayEnemy.M2, PlayEnemy.E3, PlayEnemy.M3,
   PlayEnemy.E4, PlayEnemy.M4, PlayEnemy.E5, PlayEnemy.M5,
   PlayFrame.T, PlayFrame.Z]

theorem normal_chain_protected : normalConfigs.all (fun c =>
    PlayParser.chainCells.all c.protFn) = true := by native_decide

deriving instance DecidableEq for VS
deriving instance DecidableEq for Box

/-- The final enemy segment targets exactly the common tail's entries. -/
theorem enemy_tail_entries : PlayEnemy.tail.entries = PlayFrame.T.entries := by
  native_decide

/-- A witness depending only on protected cells survives to the handoff. -/
theorem chainSaved_current {prot : UInt16 → Bool} {g : Global}
    {ram0 : UInt16 → UInt8} {b : Box} {s : Plain}
    (h : Holds prot g ram0 b s)
    (hp : ∀ i, PlayParser.chainCells.contains i = true → prot i = true)
    (hs : ChainSaved ram0) : ChainSaved s.ram := by
  obtain ⟨e, he, hs⟩ := hs
  refine ⟨e, he, ?_⟩
  intro k hk hi
  rw [h.frame k.1 (hp k.1 hi)]
  exact hs k hk hi

theorem normal_chainSaved_current {c : Config.C} {ram0 : UInt16 → UInt8}
    {b : Box} {s : Plain} (hc : c ∈ normalConfigs)
    (h : Holds c.protFn PlayParser.G ram0 b s) (hs : ChainSaved ram0) :
    ChainSaved s.ram := by
  apply chainSaved_current h ?_ hs
  intro i hi
  exact List.all_eq_true.mp (List.all_eq_true.mp normal_chain_protected c hc)
    i (List.contains_iff_mem.mp hi)

end Smb.Routine.PlaySavedHandoffs
