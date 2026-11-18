import Smb.Game
import Smb.Routine.KeptEntry
import Smb.PlayFrameData

/-! Saved-tuple bridge for the common parser chunks. Each chunk's certificate
is an explicit premise here; entry-chain reachability is not assumed proved. -/
namespace Smb.Routine.PlayFrameLinks
open Smb Smb.Abs

def objectCells (i : UInt16) : Bool := i == 0x739 || i == 0x73B

/-- The closing region's object tuple is the only missing entry constraint. -/
theorem closing_compatible :
    PlayParser.closing.entries.all (fun u => PlayFrame.Z.entries.all (fun e =>
      Box.le PlayParser.G u (e.withoutProtected objectCells))) = true := by
  native_decide

theorem object_protected : PlayParser.chunks.all (fun c =>
    c.protFn 0x739 && c.protFn 0x73B) = true := by native_decide

/-- Restore the chosen closing entry from the object tuple saved before the
parser, then begin the closing region's own protected-memory frame. -/
theorem parser_closing_entry {c : Config.C} {ram0 : UInt16 → UInt8}
    {b e : Box} {s : Plain} (hc : c ∈ PlayParser.chunks)
    (ha : PlayParser.accepted Smb.prg c = true)
    (hb : b ∈ (c.tableWith PlayParser.G Smb.prg).at 0x8178)
    (h : Holds c.protFn PlayParser.G ram0 b s)
    (he : e ∈ PlayFrame.Z.entries)
    (saved : ∀ k ∈ e.cells, objectCells k.1 = true → k.2.mem (ram0 k.1) = true) :
    Holds PlayFrame.Z.protFn PlayParser.G s.ram e s := by
  simp only [PlayParser.accepted, Bool.and_eq_true] at ha
  have hl := List.all_eq_true.mp ha.1.2 b hb
  simp only [List.any_eq_true] at hl
  obtain ⟨u, hu, hbu⟩ := hl
  have hk : ∀ i, objectCells i = true → c.protFn i = true := by
    have hp := List.all_eq_true.mp object_protected c hc
    simp only [Bool.and_eq_true] at hp
    intro i hi
    simp only [objectCells, Bool.or_eq_true, beq_iff_eq] at hi
    rcases hi with rfl | rfl
    · exact hp.1
    · exact hp.2
  have hcu := List.all_eq_true.mp closing_compatible u hu
  have hue := List.all_eq_true.mp hcu e he
  exact ((h.of_le hbu).link_kept_subset hk hue saved).rebase PlayFrame.Z.protFn

end Smb.Routine.PlayFrameLinks
