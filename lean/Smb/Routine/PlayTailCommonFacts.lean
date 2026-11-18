import Smb.Routine.PlayFrameT
import Smb.Routine.KeptEntry

/-! Common-bound tail handoffs: carry the parser tuple and select the saved
object tuple. Neither theorem establishes initial entry reachability. -/
namespace Smb.Routine.PlayFrame
open Smb Smb.Abs Smb.Abs.PlayFrame

theorem chain_protected : PlayParser.chainCells.all T.protFn = true := by native_decide

theorem parser_entry {c : Config.C} {ram0 : UInt16 → UInt8} {b e : Box} {s : Plain}
    (hc : c ∈ PlayParser.chunks) (he : e ∈ c.entries)
    (hb : b ∈ (T.tableWith G Smb.prg).at 0xAF67)
    (h : Holds T.protFn G ram0 b s)
    (saved : ∀ k ∈ e.cells, chainKeep k.1 = true → k.2.mem (ram0 k.1) = true) :
    Holds c.protFn G s.ram e s := by
  have ha := acceptedT
  simp only [Smb.Abs.PlayFrame.acceptedT, Bool.and_eq_true] at ha
  have hentries : e ∈ parserEntries := List.mem_flatMap.mpr ⟨c, hc, he⟩
  have hl := List.all_eq_true.mp ha.1.1.2 b hb
  have hle := List.all_eq_true.mp hl e hentries
  change Box.le G b (e.withoutProtected chainKeep) = true at hle
  have hk : ∀ i, chainKeep i = true → T.protFn i = true := by
    intro i hi
    exact List.all_eq_true.mp chain_protected i (List.contains_iff_mem.mp hi)
  exact (h.link_kept_subset hk hle saved).rebase c.protFn

theorem return_object_tuple {ram0 : UInt16 → UInt8} {b : Box} {s : Plain}
    (hb : b ∈ (T.tableWith G Smb.prg).at 0xAF67)
    (h : Holds T.protFn G ram0 b s) :
    ∃ e ∈ Z.entries, ∀ k ∈ e.cells,
      (k.1 == 0x739 || k.1 == 0x73B) = true → k.2.mem (s.ram k.1) = true := by
  have ha := acceptedT
  simp only [Smb.Abs.PlayFrame.acceptedT, Bool.and_eq_true] at ha
  have hl := List.all_eq_true.mp ha.1.2 b hb
  simp only [List.any_eq_true] at hl
  obtain ⟨u, hu, hle⟩ := hl
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
  have ho := h.of_le hle
  refine ⟨e, he, ?_⟩
  intro k hk hi
  exact ho.cells k (List.mem_filter.mpr ⟨hk, hi⟩)

end Smb.Routine.PlayFrame
