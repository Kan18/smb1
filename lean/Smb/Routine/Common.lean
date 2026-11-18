import Smb.SymRun
import Smb.RefineRun
import Smb.Game
import Std.Tactic.BVDecide

/-! Shared definitions for routine theorems. -/
namespace Smb.Routine

/-- `prg` (indexed by ROM offset) holds `bytes` starting at `start`. -/
def CodeAt (prg : UInt16 → UInt8) (start : UInt16) : List UInt8 → Prop
  | [] => True
  | b :: bs => prg start = b ∧ CodeAt prg (start + 1) bs

def codeMatches (prg : UInt16 → UInt8) (start : UInt16) : List UInt8 → Bool
  | [] => true
  | b :: bs => prg start == b && codeMatches prg (start + 1) bs

theorem codeAt_of_matches (prg : UInt16 → UInt8) (start : UInt16) (bytes : List UInt8)
    (h : codeMatches prg start bytes = true) : CodeAt prg start bytes := by
  induction bytes generalizing start with
  | nil => trivial
  | cons b bs ih =>
    simp only [codeMatches, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, ih _ h.2⟩

/-- RAM of a full NES state, addressed like the plain machine (mirrored below `$2000`). -/
def ramAt (s : NES) (i : UInt16) : UInt8 := s.ram.get! (i &&& 0x7FF).toNat

theorem ramAt_of_rel {s : NES} {t : Plain} (hr : Rel s t) (i : UInt16) :
    ramAt s i = t.ram (i &&& 0x7FF) := hr.ram i

theorem and7ff_of_lt (i : UInt16) (h : i < 0x800) : i &&& 0x7FF = i := by bv_decide

end Smb.Routine
