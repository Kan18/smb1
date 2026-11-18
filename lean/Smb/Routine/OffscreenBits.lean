import Smb.Routine.OffscreenBitsNegative
import Smb.Routine.OffscreenBitsPositive
import Smb.Routine.OffscreenBitsZero
namespace Smb.Routine
set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- `hx`: the object's position bytes `$86,x` / `$6D,x` must not wrap around the zero page
onto the scratch bytes `$04`–`$07` that the routine writes before the second (left-edge)
iteration reads them again. -/
theorem getXOffscreenBits_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xF1F6 ≤ a && a ≤ 0xF22A || 0xF26D ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (htab : CodeAt prg 0x71E3 xOffscreenBitsData) (hcode : CodeAt prg 0x71F3 getXOffscreenBitsCode)
    (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x7A) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 75)).run ⟨⟨0xF1F6, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xF22A, gxoBits ram x, x, gxoY ram x, sp, p'⟩,
        gxoRam x sp ram, prg, cyc + gxoCyc ram x, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  by_cases hn : (edgePageDiff (ram 0x71D) (ram 0x71B) (objX ram x) (objPage ram x)) &&& 0x80 = 0
  · by_cases hz : edgePageDiff (ram 0x71D) (ram 0x71B) (objX ram x) (objPage ram x) = 0
    · exact getXOffscreenBitsZero_call stop hstop m a x y sp p ram prg cyc bad htab hcode hdcode hI hx hz
    · exact getXOffscreenBitsPositive_call stop hstop m a x y sp p ram prg cyc bad htab hcode hdcode hI hx hn hz
  · exact getXOffscreenBitsNegative_call stop hstop m a x y sp p ram prg cyc bad htab hcode hdcode hI hx hn
end Smb.Routine
