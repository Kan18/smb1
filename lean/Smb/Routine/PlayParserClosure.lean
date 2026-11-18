import Smb.Game
import Smb.PlayParserData
import Smb.Routine.KeptEntry

/-! Ordinary parser returns remain in the finite parser-entry tuple set.
Flag-creation exits are not ordinary returns and are not closed here. -/
namespace Smb.Routine.PlayParser
open Smb Smb.Abs Smb.Abs.PlayParser

theorem chain_closed : chunks.all (chainClosed Smb.prg) = true := by
  native_decide

theorem return_tuple {c : Config.C} {ram0 : UInt16 → UInt8} {b : Box} {s : Plain}
    (hc : c ∈ chunks) (hb : b ∈ (c.tableWith G Smb.prg).at 0x8178)
    (h : Holds c.protFn G ram0 b s) :
    ∃ e ∈ entryTuples, ∀ k ∈ e.cells,
      chainCells.contains k.1 = true → k.2.mem (s.ram k.1) = true := by
  have hc' := List.all_eq_true.mp chain_closed c hc
  have hl := List.all_eq_true.mp hc' b hb
  simp only [List.any_eq_true] at hl
  obtain ⟨u, hu, hle⟩ := hl
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
  have ho := h.of_le hle
  refine ⟨e, he, ?_⟩
  intro k hk hi
  exact ho.cells k (List.mem_filter.mpr ⟨hk, hi⟩)

end Smb.Routine.PlayParser
