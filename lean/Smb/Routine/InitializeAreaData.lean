import Smb.Routine.InitializeAreaSegments

/-! `GetAreaDataAddrs` (`$9C22`), called from `$902F`, in four segments: the pointers, each header byte, the pointer
increment and the `rts`. -/
namespace Smb.Routine
set_option linter.unusedVariables false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
-- `$902F`–`$9C58`: the `jsr`, `GetAreaType` and the data pointers.
sym_theorem iaDA_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x902F ≤ a && a ≤ 0x9031 || 0x9C09 ≤ a && a ≤ 0x9C12 || 0x9C22 ≤ a && a ≤ 0x9C57) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x0FE9 iaMidCode) (htcode : CodeAt prg 0x1C09 getAreaTypeCode) (hdcode : CodeAt prg 0x1C22 getAreaDataCode)
    (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0x902F, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, iaMidCode, getAreaTypeCode, getAreaDataCode, UInt16.reduceAdd] at hcode htcode hdcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0x902F, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary iaDA hrun [hcode, htcode, hdcode, hI] until 0x9C58 exact finish (clear hcode htcode hdcode; exact_finish iaDA)
set_option maxRecDepth 20000 in
summary_interface iaDA
summary_regs iaDA

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
-- `$9C58`–`$9C7F`: the first header byte.
sym_theorem iaDB_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x9C58 ≤ a && a ≤ 0x9C7E) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hdcode : CodeAt prg 0x1C22 getAreaDataCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 25)).run ⟨⟨0x9C58, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, getAreaDataCode, UInt16.reduceAdd] at hdcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 25)).run ⟨⟨0x9C58, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary iaDB hrun [hdcode, hI] until 0x9C7F exact finish (clear hdcode; exact_finish iaDB)
set_option maxRecDepth 20000 in
summary_interface iaDB
summary_regs iaDB

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
-- `$9C7F`–`$9CA6`: the second header byte.
sym_theorem iaDC_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x9C7F ≤ a && a ≤ 0x9CA5) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hdcode : CodeAt prg 0x1C22 getAreaDataCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 25)).run ⟨⟨0x9C7F, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, getAreaDataCode, UInt16.reduceAdd] at hdcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 25)).run ⟨⟨0x9C7F, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary iaDC hrun [hdcode, hI] until 0x9CA6 exact finish (clear hdcode; exact_finish iaDC)
set_option maxRecDepth 20000 in
summary_interface iaDC
summary_regs iaDC

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
-- `$9CA6`–`$9032`: the data pointer's increment and the `rts`.
sym_theorem iaDD_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x9CA6 ≤ a && a ≤ 0x9CB3) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hdcode : CodeAt prg 0x1C22 getAreaDataCode) (hI : (p &&& 4 == 0) = false)
    (hlo : ram ((256 ||| (sp + 1).toUInt16) &&& 2047) = 0x31) (hhi : ram ((256 ||| (sp + 2).toUInt16) &&& 2047) = 0x90) :
    ((CPU.runTo (σ := Plain) stop (m + 15)).run ⟨⟨0x9CA6, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, getAreaDataCode, UInt16.reduceAdd] at hdcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 15)).run ⟨⟨0x9CA6, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary iaDD hrun [hdcode, hI, hlo, hhi] until 0x9032 exact finish (clear hdcode hlo hhi; exact_finish iaDD)
set_option maxRecDepth 20000 in
summary_interface iaDD
summary_regs iaDD

end Smb.Routine
