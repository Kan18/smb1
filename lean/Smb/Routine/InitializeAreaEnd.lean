import Smb.Routine.InitializeAreaSegments

/-! `$9032`–`$9060`: the hard mode test and `DoneInitArea`. -/
namespace Smb.Routine
set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem iaEnd_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x9032 ≤ a && a ≤ 0x905F) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x1032 iaEndCode) (hI : (p &&& 4 == 0) = false) (hsec : ram 0x6CC = 0) :
    ((CPU.runTo (σ := Plain) stop (m + 30)).run ⟨⟨0x9032, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, iaEndCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 30)).run ⟨⟨0x9032, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary iaEnd hrun [hcode, hI, hsec] until 0x9060 exact finish (clear hcode; exact_finish iaEnd)
set_option maxRecDepth 20000 in
summary_interface iaEnd
summary_regs iaEnd

end Smb.Routine
