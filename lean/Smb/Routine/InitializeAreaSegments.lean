import Smb.Data.ProofRom
import Smb.Routine.InitializeMemory

/-!
# `InitializeArea` (`$8FE4`) after the clear: segments

`iaHead`, `initMem_call`, `iaRts`, then `iaMid` (timers, page variables, `GetScreenPosition`), `iaData` (`GetAreaDataAddrs`),
`iaEnd` (hard mode, `DoneInitArea`). Each is stated for any RAM; `iaMid` and `iaEnd` assume the bytes that the clear has just zeroed.
-/
namespace Smb.Routine
set_option linter.unusedVariables false

/-- `$8FE4`–`$8FE8`: `ldy #$4B`, `jsr InitializeMemory`. -/
def iaHeadCode : List UInt8 := smbPrg% 0x8FE4 5
/-- `$8FE9`–`$9031`: from `ldx #$21` up to and including `jsr GetAreaDataAddrs`. -/
def iaMidCode : List UInt8 := smbPrg% 0x8FE9 73
/-- `$9032`–`$9060`: the hard mode test and `DoneInitArea`. -/
def iaEndCode : List UInt8 := smbPrg% 0x9032 47
/-- `$B038`–`$B049`: `GetScreenPosition`. -/
def getScreenPosCode : List UInt8 := smbPrg% 0xB038 18
/-- `$9C09`–`$9C12`: `GetAreaType`. -/
def getAreaTypeCode : List UInt8 := smbPrg% 0x9C09 10
/-- `$9C22`–`$9CB3`: `GetAreaDataAddrs`. -/
def getAreaDataCode : List UInt8 := smbPrg% 0x9C22 146

/-- The return address `$8FE8` pushed by the `jsr` at `$8FE6`. -/
def iaPushRam (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == 0x100 ||| (sp - 1).toUInt16 then 0xE8 else bif i == 0x100 ||| sp.toUInt16 then 0x8F else ram i

set_option maxHeartbeats 4000000 in
theorem iaHead (stop : UInt16) (hstop : ∀ a : UInt16, (0x8FE4 ≤ a && a ≤ 0x8FE8) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x0FE4 iaHeadCode) (hI : (p &&& 4 == 0) = false) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 2)).run ⟨⟨0x8FE4, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x90CC, a, x, 0x4B, sp - 2, p'⟩, iaPushRam sp ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, iaHeadCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 2)).run ⟨⟨0x8FE4, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI] until 0x90CC
  all_goals
    intros
    subst hrun
    subst_vars
    call_finish [iaPushRam]

set_option maxHeartbeats 4000000 in
/-- The `rts` of `InitializeMemory` back to `$8FE9`. -/
theorem iaRts (stop : UInt16) (hstop : ∀ a : UInt16, (0x90E6 ≤ a && a ≤ 0x90E6) = true → a ≠ stop)
    (m : Nat) (a x y s p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x10CC initMemCode) (hI : (p &&& 4 == 0) = false)
    (hlo : ram ((0x100 ||| (s + 1).toUInt16) &&& 0x7FF) = 0xE8) (hhi : ram ((0x100 ||| (s + 2).toUInt16) &&& 0x7FF) = 0x8F) :
    ∃ j p' c', ((CPU.runTo (σ := Plain) stop (m + 1)).run ⟨⟨0x90E6, a, x, y, s, p⟩, ram, prg, cyc, bad⟩).2 =
      ((CPU.runTo stop (j + m)).run ⟨⟨0x8FE9, a, x, y, s + 2, p'⟩, ram, prg, c', bad⟩).2 ∧
      (p' &&& 4 == 0) = false := by
  simp only [CodeAt, initMemCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 1)).run ⟨⟨0x90E6, a, x, y, s, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_run hrun [hcode, hI, hlo, hhi] until 0x8FE9
  all_goals
    intros
    subst hrun
    subst_vars
    call_finish []

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem iaMid_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8FE9 ≤ a && a ≤ 0x902E || 0xB038 ≤ a && a ≤ 0xB049) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x0FE9 iaMidCode) (hscode : CodeAt prg 0x3038 getScreenPosCode) (hI : (p &&& 4 == 0) = false)
    (hsx : ram 0x71C = 0) (h0 : ram 0x730 = 0) (h1 : ram 0x731 = 0) (h2 : ram 0x732 = 0) :
    ((CPU.runTo (σ := Plain) stop (m + 150)).run ⟨⟨0x8FE9, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, iaMidCode, getScreenPosCode, UInt16.reduceAdd] at hcode hscode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 150)).run ⟨⟨0x8FE9, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary iaMid hrun [hcode, hscode, hI, hsx, h0, h1, h2] until 0x902F exact finish (clear hcode hscode; exact_finish iaMid)
set_option maxRecDepth 20000 in
summary_interface iaMid
summary_regs iaMid

end Smb.Routine
