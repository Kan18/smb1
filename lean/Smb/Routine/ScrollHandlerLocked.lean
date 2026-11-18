import Smb.Routine.ScrollFinish
namespace Smb.Routine
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem scrollHandlerLocked_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xAF93 ≤ a && a ≤ 0xB033 || 0xB038 ≤ a && a ≤ 0xB049 ||
      0xF1F6 ≤ a && a ≤ 0xF22A || 0xF26D ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x2F93 scrollCode)
    (htab : CodeAt prg 0x71E3 xOffscreenBitsData) (hgcode : CodeAt prg 0x71F3 getXOffscreenBitsCode)
    (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hI : (p &&& 4 == 0) = false) (hlock : ram 0x723 ≠ 0) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xAF93, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0xB033, 0, 0, bif clampLeft ram then 0 else 1, sp, p'⟩,
        scrollRam sp ram, prg, cyc + scrollCyc ram, bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  have hs : scrolls ram = false := by
    simp only [scrolls, scrPxs, bne] at *
    bv_decide
  have hpostcode := hcode
  simp only [CodeAt, scrollCode, UInt16.reduceAdd] at hcode
  -- `GetXOffscreenBits`' RTS, executed here after its call theorem.
  have hrts : prg 0x722A = 0x60 := by
    have h := hgcode; simp only [CodeAt, getXOffscreenBitsCode, UInt16.reduceAdd] at h; simp [h]
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 200)).run ⟨⟨0xAF93, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hrts, hI, gxoRam] until 45107 calls [getXOffscreenBits_call, scrollPost_call]
  all_goals
    intros
    clear hcode hpostcode hrts htab hgcode hdcode
    subst hrun
    -- The clamp is a sealed call: compare its final state field by field.
    run_tac do
      let _ ← Smb.Symbolic.dbg "Locked: finish path"
      pure ()
    run_tac do
      let _ ← Smb.Symbolic.dbg "Locked: normalized path"
      pure ()
    normalize_offscreen_hyps
    call_finish [scrollPostRam, scrollPostCycles, scrollPostLeft, scrollPostRight, hs, hlock, scrollRam, scrollCyc, scrollPreCyc, scrollPostCyc, stopsSpeed, clampPage, clampX,
      clampRight, clampLeft, scrBits, scrMid, scrRightPage, scrRightX, scrLeftPage, scrLeftX, scrAmt,
      scrolls, scrPxs, gxoRam, gxoCyc, gxoCalled, gxoY, gxoBits, gxoL, gxoR, objX, objPage, offCyc,
      offDiv, offBits, edgePageDiff]

end Smb.Routine
