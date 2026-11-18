import Smb.Routine.ScrollHandlerLocked
import Smb.Routine.ScrollHandlerNear
import Smb.Routine.ScrollHandlerTimed
import Smb.Routine.ScrollHandlerStill
import Smb.Routine.ScrollHandlerMoving

namespace Smb.Routine
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem scrollHandler_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xAF93 ≤ a && a ≤ 0xB033 || 0xB038 ≤ a && a ≤ 0xB049 ||
      0xF1F6 ≤ a && a ≤ 0xF22A || 0xF26D ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x2F93 scrollCode)
    (htab : CodeAt prg 0x71E3 xOffscreenBitsData) (hgcode : CodeAt prg 0x71F3 getXOffscreenBitsCode)
    (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hI : (p &&& 4 == 0) = false) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xAF93, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB033, 0, 0, bif clampLeft ram then 0 else 1, sp, p'⟩,
        scrollRam sp ram, prg, cyc + scrollCyc ram, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  by_cases hl : ram 0x723 = 0
  · by_cases hn : ram 0x755 < 0x50
    · exact scrollHandlerNear_call stop hstop m a x y sp p ram prg cyc bad hcode htab hgcode hdcode hI hl hn
    · by_cases ht : ram 0x785 = 0
      · by_cases ha : (scrPxs ram - 1) &&& 0x80 = 0
        · exact scrollHandlerMoving_call stop hstop m a x y sp p ram prg cyc bad hcode htab hgcode hdcode hI hl hn ht ha
        · exact scrollHandlerStill_call stop hstop m a x y sp p ram prg cyc bad hcode htab hgcode hdcode hI hl hn ht ha
      · exact scrollHandlerTimed_call stop hstop m a x y sp p ram prg cyc bad hcode htab hgcode hdcode hI hl hn ht
  · exact scrollHandlerLocked_call stop hstop m a x y sp p ram prg cyc bad hcode htab hgcode hdcode hI hl

end Smb.Routine
