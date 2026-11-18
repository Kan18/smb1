import Smb.Routine.PlaySpeed
import Smb.Routine.KeptEntry

/-! The checked player region bounds speed at its ordinary return. This is
conditional on the table invariant, not a proof of its initial reachability. -/
namespace Smb.Routine.PlaySpeed
open Smb Smb.Abs Smb.Abs.PlaySpeed

/-- The byte encoding of signed speed between -40 and 40, inclusive. -/
def speedBound (v : UInt8) : Bool := v ≤ 0x28 || 0xD8 ≤ v

theorem entries_speed : enemy.entries.all (fun e => e.cells.any (fun c =>
    c.1 == 0x57 && c.2.elems.all speedBound)) = true := by native_decide

theorem enemy_entry_speed {prot : UInt16 → Bool} {ram0 : UInt16 → UInt8}
    {e : Box} {s : Plain} (he : e ∈ enemy.entries)
    (h : Holds prot G ram0 e s) : speedBound (s.ram 0x57) = true := by
  have hs := List.all_eq_true.mp entries_speed e he
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨i, vs⟩, hc, hi, hv⟩ := hs
  dsimp at hi hv
  subst i
  exact List.all_eq_true.mp hv _ (VS.mem_elems (h.cells _ hc))

/-- Every admitted box at the normal return `$AF01` has the speed bound.
The pipe, flag and death exits are deliberately not claimed here. -/
theorem return_speed {ram0 : UInt16 → UInt8} {b : Box} {s : Plain}
    (hb : b ∈ (player.tableWith G Smb.prg).at 0xAF01)
    (h : Holds player.protFn G ram0 b s) : speedBound (s.ram 0x57) = true := by
  have ha := accepted
  simp only [Smb.Abs.PlaySpeed.accepted, Config.C.linkedE, Bool.and_eq_true] at ha
  have hl := List.all_eq_true.mp ha.1.2 (0xAF01, enemy.entries) (by simp)
  have he := List.all_eq_true.mp hl b hb
  simp only [List.any_eq_true] at he
  obtain ⟨e, he, hle⟩ := he
  exact enemy_entry_speed he (h.of_le hle)

end Smb.Routine.PlaySpeed
