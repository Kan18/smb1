import Smb.Routine.ScrollDefs
namespace Smb.Routine
set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- `hx`: the object's position bytes `$86,x` / `$6D,x` must not wrap around the zero page
onto the scratch bytes `$04`–`$07` that the routine writes before the second (left-edge)
iteration reads them again. -/
theorem getXOffscreenBitsPositive_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xF1F6 ≤ a && a ≤ 0xF22A || 0xF26D ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (htab : CodeAt prg 0x71E3 xOffscreenBitsData) (hcode : CodeAt prg 0x71F3 getXOffscreenBitsCode)
    (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hI : (p &&& 4 == 0) = false) (hx : x < 0x7A) (hneg : (edgePageDiff (ram 0x71D) (ram 0x71B) (objX ram x) (objPage ram x)) &&& 0x80 = 0) (hpos : edgePageDiff (ram 0x71D) (ram 0x71B) (objX ram x) (objPage ram x) ≠ 0) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 75)).run ⟨⟨0xF1F6, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xF22A, gxoBits ram x, x, gxoY ram x, sp, p'⟩,
        gxoRam x sp ram, prg, cyc + gxoCyc ram x, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [edgePageDiff, objX, objPage] at hneg hpos
  simp only [CodeAt, xOffscreenBitsData, UInt16.reduceAdd] at htab
  simp only [CodeAt, getXOffscreenBitsCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, dividePDiffCode, UInt16.reduceAdd] at hdcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 75)).run ⟨⟨0xF1F6, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hdcode, hI, hx] until 61994
  all_goals
    intros
    -- `htab` stays: the table is read at a computed index, so the proof needs its values.
    clear hcode hdcode
    subst hrun
    call_finish [gxoRam, gxoCyc, gxoCalled, gxoY, gxoBits, gxoL, gxoR, objX, objPage, offCyc, offDiv,
      offBits, edgePageDiff]


end Smb.Routine
