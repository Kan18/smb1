import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
The actual row-end branch in `RenderAreaGraphics`: after each row it
loads the saved row number, increments it, compares it with 13, and
returns to `DrawMTLoop` for rows 0--11. Row 12 exits the loop.
-/

namespace Smb.Buffer.Renderer.RendererLoopBranch
open Smb Smb.Routine Smb.Symbolic

def code : List UInt8 := smbPrg% 0x893C 7
def rom (addr : UInt16) : UInt8 := Smb.prg.get! (addr &&& 0x7fff).toNat

theorem code_in_rom : CodeAt rom 0x093c code :=
  codeAt_of_matches _ _ _ (by native_decide)

set_option maxHeartbeats 3000000 in
theorem loops_before_last_row (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x093c code) (hI : p &&& 4 ≠ 0)
    (hr : ram 1 < 12) :
    let s : Plain := ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88d0 5).run s).2
    t.bad = false ∧ t.regs.pc = 0x88d0 ∧ t.regs.x = ram 1 + 1 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hrun : ((CPU.runTo (σ := Plain) 0x88d0 5).run
    ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hrun [hc, hi, hr]
  all_goals
    intros
    clear hc hi
    simp_all

set_option maxHeartbeats 3000000 in
theorem loop_seam (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x093c code) (hI : p &&& 4 ≠ 0)
    (hr : ram 1 < 12) :
    let s : Plain := ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88d0 5).run s).2
    t.ram 0 = ram 0 ∧ t.ram 1 = ram 1 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hrun : ((CPU.runTo (σ := Plain) 0x88d0 5).run
    ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hrun [hc, hi, hr]
  all_goals
    intros
    clear hc hi
    simp_all

set_option maxHeartbeats 3000000 in
theorem loop_keeps_I (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x093c code) (hI : p &&& 4 ≠ 0)
    (hr : ram 1 < 12) :
    let s : Plain := ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88d0 5).run s).2
    t.regs.p &&& 4 ≠ 0 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hrun : ((CPU.runTo (σ := Plain) 0x88d0 5).run
    ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hrun [hc, hi, hr] until 0x88d0
  all_goals
    intros
    clear hc hi
    subst hrun
    rw [runTo_snd_stop _ 0x88d0 _ rfl]
    dsimp only
    bv_decide

set_option maxHeartbeats 3000000 in
theorem loop_keeps_prg (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x093c code) (hI : p &&& 4 ≠ 0)
    (hr : ram 1 < 12) :
    let s : Plain := ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x88d0 5).run s).2
    t.prg = prg := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hrun : ((CPU.runTo (σ := Plain) 0x88d0 5).run
    ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hrun [hc, hi, hr] until 0x88d0
  all_goals
    intros
    clear hc hi
    subst hrun
    rw [runTo_snd_stop _ 0x88d0 _ rfl]

set_option maxHeartbeats 3000000 in
theorem exits_after_last_row (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x093c code) (hI : p &&& 4 ≠ 0)
    (hr : ram 1 = 12) :
    let s : Plain := ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8943 5).run s).2
    t.bad = false ∧ t.regs.pc = 0x8943 ∧ t.regs.x = 13 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hrun : ((CPU.runTo (σ := Plain) 0x8943 5).run
    ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hrun [hc, hi, hr]
  all_goals
    intros
    clear hc hi
    simp_all

set_option maxHeartbeats 3000000 in
theorem exit_seam (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x093c code) (hI : p &&& 4 ≠ 0)
    (hr : ram 1 = 12) :
    let s : Plain := ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8943 5).run s).2
    t.ram 0 = ram 0 ∧ t.ram 1 = ram 1 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hrun : ((CPU.runTo (σ := Plain) 0x8943 5).run
    ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hrun [hc, hi, hr]
  all_goals
    intros
    clear hc hi
    simp_all

end Smb.Buffer.Renderer.RendererLoopBranch
