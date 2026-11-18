import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Column-position writer endpoints

Initialization establishes column 0 or 16; the completed increment masks any old
byte into 0..31. The actual increment temporarily stores 32 when the old byte is 31,
so the range is a boundary property, not an every-instruction invariant.

Initialization stops after its column store, the increment before RTS, and the
transient cut just after INC. They do not cover intervening parser work, indirect
writers or full NES execution.
-/

namespace Smb.Routine.ColumnPosition
open Smb Smb.Routine
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- IncrementColumnPos, including its final RTS. -/
def columnIncCode : List UInt8 := smbPrg% 0x92DB 28
/-- Area initialization from LDY #20 through the column store. -/
def columnInitCode : List UInt8 := smbPrg% 0x900A 23

def incRun (s : Plain) : Plain := ((CPU.runTo (σ := Plain) 0x92F6 20).run s).2

def IncPost (ram : UInt16 → UInt8) (sp : UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0x92F6 ∧ t.bad = false ∧ t.regs.s = sp ∧
  t.ram 0x6A0 = (ram 0x6A0 + 1) &&& 0x1F ∧ t.ram 0x6A0 < 0x20

/-- Actual bounded machine-code contract. No old-column range is assumed. -/
theorem increment_column (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x12DB columnIncCode) (hI : (p &&& 4 == 0) = false) :
    IncPost ram sp (incRun ⟨⟨0x92DB, a, x, y, sp, p⟩, ram, prg, cyc, false⟩) := by
  simp only [CodeAt, columnIncCode, UInt16.reduceAdd] at hcode
  generalize hrun : incRun ⟨⟨0x92DB, a, x, y, sp, p⟩, ram, prg, cyc, false⟩ = f
  unfold incRun at hrun
  sym_run hrun [hcode, hI]
  all_goals
    intros
    clear hcode
    sym_exec [IncPost] at *
    bv_decide

def initRun (s : Plain) : Plain := ((CPU.runTo (σ := Plain) 0x9021 20).run s).2

def InitPost (a sp : UInt8) (t : Plain) : Prop :=
  t.regs.pc = 0x9021 ∧ t.bad = false ∧ t.regs.s = sp ∧
  t.ram 0x6A0 = (a &&& 1) <<< 4 ∧ (t.ram 0x6A0 = 0 ∨ t.ram 0x6A0 = 0x10)

theorem initialize_column (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x100A columnInitCode) (hI : (p &&& 4 == 0) = false) :
    InitPost a sp (initRun ⟨⟨0x900A, a, x, y, sp, p⟩, ram, prg, cyc, false⟩) := by
  simp only [CodeAt, columnInitCode, UInt16.reduceAdd] at hcode
  generalize hrun : initRun ⟨⟨0x900A, a, x, y, sp, p⟩, ram, prg, cyc, false⟩ = f
  unfold initRun at hrun
  sym_run hrun [hcode, hI]
  all_goals
    intros
    clear hcode
    sym_exec [InitPost] at *
    bv_decide

/-- The real increment's transient value, before LDA/AND/STA restores the bound. -/
theorem column_transient (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x12DB columnIncCode) (hI : (p &&& 4 == 0) = false)
    (hc : ram 0x6A0 = 0x1F) :
    let t := ((CPU.runTo (σ := Plain) 0x92EE 2).run
      ⟨⟨0x92EB, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    t.regs.pc = 0x92EE ∧ t.bad = false ∧ t.ram 0x6A0 = 0x20 := by
  simp only [CodeAt, columnIncCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) 0x92EE 2).run
    ⟨⟨0x92EB, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  change f.regs.pc = 0x92EE ∧ f.bad = false ∧ f.ram 0x6A0 = 0x20
  sym_run hrun [hcode, hI]
  all_goals
    intros
    clear hcode
    simp [hc]

/-- Tight normal block-buffer bounds, unlike the broader <=6CF read envelope. -/
theorem normal_buffer_not_column (lo row : UInt8) (hl : lo ≤ 0xDF) (hr : row ≤ 0xC0) :
    (0x500 : UInt16) + lo.toUInt16 + row.toUInt16 ≤ 0x69F ∧
    (((0x500 : UInt16) + lo.toUInt16 + row.toUInt16) &&& 0x7FF) ≠ 0x6A0 := by
  bv_decide


/-- Both instruction ranges are bytes of the actual cartridge. -/
theorem column_rom :
    let prg := fun a => Smb.prg.get! (a &&& 0x7FFF).toNat
    CodeAt prg 0x12DB columnIncCode ∧ CodeAt prg 0x100A columnInitCode := by
  exact ⟨codeAt_of_matches _ _ _ (by native_decide),
    codeAt_of_matches _ _ _ (by native_decide)⟩

end Smb.Routine.ColumnPosition
