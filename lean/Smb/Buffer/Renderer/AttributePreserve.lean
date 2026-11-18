import Smb.Buffer.Renderer.AttributeTail

/-!
The attribute store in the final row can alias `$0433` only when the
attribute index loaded from `$04` is `$3a`.
-/
namespace Smb.Buffer.Renderer.AttributePreserve

open Smb Smb.Routine Smb.Symbolic

set_option maxHeartbeats 10000000 in
theorem keeps_433 (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x0906 Smb.Buffer.Renderer.AttributeTail.code)
    (hI : p &&& 4 ≠ 0) (h4 : ram 4 ≠ 0x3a) :
    let s : Plain := ⟨⟨0x8906, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x893c 26).run s).2
    t.bad = false ∧ t.regs.pc = 0x893c ∧
      t.ram 0x433 = ram 0x433 := by
  dsimp only
  simp only [CodeAt, Smb.Buffer.Renderer.AttributeTail.code,
    UInt16.reduceAdd] at hc
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


end Smb.Buffer.Renderer.AttributePreserve
