import Smb.Buffer.Renderer.RendererLoopBranch

/-! The final row branch only reads scratch state; it does not write RAM. -/
namespace Smb.Buffer.Renderer.BranchPreserve

open Smb Smb.Routine Smb.Symbolic

set_option maxHeartbeats 3000000 in
theorem keeps_433 (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x093c Smb.Buffer.Renderer.RendererLoopBranch.code)
    (hI : p &&& 4 ≠ 0) (hr : ram 1 = 12) :
    let s : Plain := ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8943 5).run s).2
    t.bad = false ∧ t.regs.pc = 0x8943 ∧
      t.ram 0x433 = ram 0x433 := by
  dsimp only
  simp only [CodeAt, Smb.Buffer.Renderer.RendererLoopBranch.code,
    UInt16.reduceAdd] at hc
  generalize hrun : ((CPU.runTo (σ := Plain) 0x8943 5).run
    ⟨⟨0x893c, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hrun [hc, hi, hr] until 0x8943
  all_goals
    intros
    clear hc hi
    subst hrun
    rw [runTo_snd_stop _ 0x8943 _ rfl]
    simp_all


end Smb.Buffer.Renderer.BranchPreserve
