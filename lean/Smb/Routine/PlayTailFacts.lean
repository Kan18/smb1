import Smb.Routine.PlayTail
import Smb.Routine.KeptEntry

/-! The checked tail supplies the parser's ordinary entry constraints. Its
exact saved tuple remains an explicit hypothesis, to be carried by the run. -/
namespace Smb.Routine.PlayTail
open Smb Smb.Abs Smb.Abs.PlayTail

/-- Choose the parser entry matching the saved tuple, restore its protected
constraints, and start the parser's own protected-memory frame. -/
theorem parser_entry {ram0 : UInt16 → UInt8} {b e : Box} {s : Plain}
    (hb : b ∈ (tail.tableWith G Smb.prg).at 0xAF67)
    (h : Holds tail.protFn G ram0 b s)
    (he : e ∈ parser.entries)
    (saved : ∀ c ∈ e.cells, tail.protFn c.1 = true → c.2.mem (ram0 c.1) = true) :
    Holds parser.protFn G s.ram e s := by
  have ha := accepted
  simp only [Smb.Abs.PlayTail.accepted, Bool.and_eq_true] at ha
  have hl := List.all_eq_true.mp ha.1.2 b hb
  have hle := List.all_eq_true.mp hl e he
  change Box.le G b (e.withoutProtected tail.protFn) = true at hle
  exact (h.link_kept hle saved).rebase parser.protFn

end Smb.Routine.PlayTail
