import Smb.Summary
import Smb.Routine.Jumpspring

/-!
# Regression check for `sym_summary`

The jumpspring's closed form generated from its symbolic execution (`Smb.Summary`) is exact
(`js_exact`: a call theorem whose end state is entirely the generated definitions, proved by
`summary_finish`).
-/
namespace Smb.Routine.SummaryCheck
open Smb Smb.Routine
set_option linter.unusedVariables false
set_option sym_summary.raw true
set_option maxHeartbeats 40000000 in
sym_summarize js (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xB8BD ≤ a && a ≤ 0xB902) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x38B6 jumpspringCode) (hI : (p &&& 4 == 0) = false) (hx : x < 6) :
    ∃ j t, ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB8BD, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run t).2 ∧ True := by
  simp only [CodeAt, jumpspringCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB8BD, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary js hrun [hcode, hI, hx] until 47362

-- The generated closed form is exact: a call theorem with every field from the definitions.
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem js_exact (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xB8BD ≤ a && a ≤ 0xB902) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x38B6 jumpspringCode) (hI : (p &&& 4 == 0) = false) (hx : x < 6) :
    ∃ j p', ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB8BD, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨js_pc, js_a x ram prg,
        js_x x, js_y y ram, js_s sp, p'⟩,
        js_ram x ram prg, prg, js_cyc ram cyc, js_bad x p ram prg⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, jumpspringCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB8BD, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_run hrun [hcode, hI, hx] until 47362
  all_goals
    intros
    clear hcode
    subst hrun
    summary_finish js []

end Smb.Routine.SummaryCheck
