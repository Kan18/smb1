import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
One ROM-backed attribute tail of `RenderAreaGraphics`, from `$8906` through
`$893B`.  It proves that all four attribute branches rejoin and advance the
saved output offset by two without changing the saved row number.  The earlier
tile loads/stores and the later row-end branch are separate obligations.
-/
namespace Smb.Buffer.Renderer.AttributeTail
open Smb Smb.Routine Smb.Symbolic

def code : List UInt8 :=
  smbPrg% 0x8906 54

def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem code_in_rom : CodeAt rom 0x0906 code :=
  codeAt_of_matches _ _ _ (by native_decide)

set_option maxHeartbeats 10000000 in
theorem joins_and_advances (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x0906 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x8906, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x893c 26).run s).2
    t.bad = false ∧ t.regs.pc = 0x893c ∧
      t.ram 0 = ram 0 + 2 ∧ t.ram 1 = ram 1 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x893c 26).run
    ⟨⟨0x8906, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x893c
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x893c _ rfl]
    simp_all (config := { maxSteps := 1000000 })
    bv_decide


set_option maxHeartbeats 10000000 in
theorem joins_keeps_I (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x0906 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x8906, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x893c 26).run s).2
    t.regs.p &&& 4 ≠ 0 := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x893c 26).run
    ⟨⟨0x8906, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x893c
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x893c _ rfl]
    dsimp only
    bv_decide

set_option maxHeartbeats 10000000 in
theorem joins_keeps_prg (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x0906 code) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x8906, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x893c 26).run s).2
    t.prg = prg := by
  dsimp only
  simp only [CodeAt, code, UInt16.reduceAdd] at hc
  generalize hr : ((CPU.runTo (σ := Plain) 0x893c 26).run
    ⟨⟨0x8906, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi] until 0x893c
  all_goals
    intros
    clear hc hi
    subst hr
    rw [runTo_snd_stop _ 0x893c _ rfl]


end Smb.Buffer.Renderer.AttributeTail
