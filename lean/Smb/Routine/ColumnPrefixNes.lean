import Smb.Routine.ColumnWrite
import Smb.Routine.NesStoreStep
import Smb.RefineRun
import Smb.Game

/-!
# The real NES filter prefix and following store

The prefix uses Quiet/I/code at entry and preserves the finish predicate, supplies
A's filter range, and establishes the next opcode. The separate full-NES step
then handles an arbitrary destination and any post-store NMI. No column/pointer
bound is assumed. The result is this bounded prefix followed by one CPU.step,
not a whole buffer loop or video-frame theorem, and makes no PPU-support claim.
-/

open Smb Smb.Routine Smb.Symbolic
open Smb.Routine.ColumnCopy (copyCode)
open Smb.Routine.ColumnFinish (Finish)
open Smb.Routine.ColumnWrite
namespace Smb.Routine.ColumnPrefixNes
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
/-- Only the missing bad-flag projection is reexecuted. Arbitrary initial bad. -/
theorem filter_prefix_bad (a x y sp p : UInt8) (ram prg : UInt16 → UInt8)
    (cyc : UInt64) (bad : Bool) (hcode : CodeAt prg 0x14D6 copyCode)
    (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) 0x94F7 14).run
      ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2.bad = bad := by
  simp only [CodeAt, copyCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) 0x94F7 14).run
    ⟨⟨0x94E0,a,x,y,sp,p⟩,ram,prg,cyc,bad⟩).2 = t
  sym_run hrun [hcode, hI]
  all_goals
    intros
    clear hcode
    try sym_exec [bne]
    first | rfl | bv_decide

/-- Only the three canonical finish cells are transferred. -/
theorem finish_of_rel {s : NES} {t : Plain} (h : Rel s t) :
    finalVictory s = true ↔ Finish t.ram := by
  have hm : s.ram.get! 0x770 = t.ram 0x770 := h.ram 0x770
  have hw : s.ram.get! 0x75F = t.ram 0x75F := h.ram 0x75F
  have hl : s.ram.get! 0x75C = t.ram 0x75C := h.ram 0x75C
  simp only [finalVictory, operMode, Bool.and_eq_true, beq_iff_eq, Finish]
  rw [hm, hw, hl]
  exact and_assoc

/-- The actual NES prefix ends before STA ($06),Y. No pointer or X/Y bound.
Quiet is an explicit input condition; no PPU supportedness claim is made. -/
theorem filter_prefix_nes (s : NES) (hq : s.Quiet) (hpc : s.pc = 0x94E0)
    (hI : (s.p &&& 4 == 0) = false)
    (hcode : CodeAt s.toPlain.prg 0x14D6 copyCode) :
    let out := ((CPU.runTo (σ := NES) 0x94F7 14).run s).2
    out.pc = 0x94F7 ∧ (out.a = 0 ∨ 0x10 ≤ out.a) ∧
      (finalVictory out = true ↔ finalVictory s = true) ∧ out.Quiet ∧
      out.prgAt 0x94F7 = 0x91 := by
  have hp : PrefixPost s.x s.y s.s s.toPlain.ram s.toPlain.prg
      ((CPU.runTo (σ := Plain) 0x94F7 14).run s.toPlain).2 := by
    simpa only [NES.toPlain, hpc] using
      filter_prefix s.a s.x s.y s.s s.p s.toPlain.ram s.toPlain.prg s.cyc false hcode hI
  have hb : ((CPU.runTo (σ := Plain) 0x94F7 14).run s.toPlain).2.bad = false := by
    simpa only [NES.toPlain, hpc] using
      filter_prefix_bad s.a s.x s.y s.s s.p s.toPlain.ram s.toPlain.prg s.cyc false hcode hI
  have hr := refine_runTo s hq 0x94F7 14 hb
  have hpc' := congrArg Regs.pc hr.regs
  have ha' := congrArg Regs.a hr.regs
  dsimp only at hpc' ha' ⊢
  refine ⟨hpc'.trans hp.1, ?_, ?_, ?_, ?_⟩
  · rw [ha']
    exact hp.2.1
  · exact (finish_of_rel hr).trans
      ((prefix_finish_iff hp).trans (finish_of_rel (s.rel_toPlain hq)).symm)
  · exact ⟨hr.size, hr.ctrl, hr.nmiPending, hr.nmiPolled, hr.dma⟩
  · have hstore := store_code hcode
    simp only [CodeAt, UInt16.reduceAdd] at hstore
    calc
      _ = ((CPU.runTo (σ := Plain) 0x94F7 14).run s.toPlain).2.prg 0x14F7 :=
        hr.prg 0x94F7
      _ = s.toPlain.prg 0x14F7 := congrArg (fun f => f 0x14F7) hp.2.2.2.2.2.1
      _ = 0x91 := hstore.1

/-- Specialization to the project's actual ROM, using the existing checked code fact. -/
theorem filter_prefix_actual_rom (s : NES) (hq : s.Quiet)
    (hrom : s.prg = Smb.prg) (hpc : s.pc = 0x94E0)
    (hI : (s.p &&& 4 == 0) = false) :
    let out := ((CPU.runTo (σ := NES) 0x94F7 14).run s).2
    out.pc = 0x94F7 ∧ (out.a = 0 ∨ 0x10 ≤ out.a) ∧
      (finalVictory out = true ↔ finalVictory s = true) ∧ out.Quiet ∧
      out.prgAt 0x94F7 = 0x91 := by
  apply filter_prefix_nes s hq hpc hI
  simpa only [NES.toPlain, hrom] using ColumnCopy.copy_rom.1


/-- Compose the actual prefix and whole following instruction, including opcode
fetch and a possible NMI entry. The output PC need not be the ordinary $94F9. -/
theorem filter_then_store_cannot_create (s : NES) (hq : s.Quiet)
    (hpc : s.pc = 0x94E0) (hI : (s.p &&& 4 == 0) = false)
    (hcode : CodeAt s.toPlain.prg 0x14D6 copyCode) :
    let t := ((CPU.runTo (σ := NES) 0x94F7 14).run s).2
    finalVictory ((CPU.step (σ := NES)).run t).2 = true → finalVictory s = true := by
  let t := ((CPU.runTo (σ := NES) 0x94F7 14).run s).2
  obtain ⟨hpc', ha, hfinish, hquiet, hop⟩ := filter_prefix_nes s hq hpc hI hcode
  change t.pc = 0x94F7 at hpc'
  change t.prgAt 0x94F7 = 0x91 at hop
  have hrompc : 0x8000 ≤ t.pc := by rw [hpc']; decide
  have hopcode : t.prgAt t.pc = 0x91 := by rw [hpc']; exact hop
  change finalVictory ((CPU.step (σ := NES)).run t).2 = true → finalVictory s = true
  intro hf
  exact hfinish.mp (NesStoreStep.step91_cannot_create t hrompc hopcode hquiet.size ha hf)

/-- The same composed result for this project's actual cartridge. -/
theorem filter_then_store_actual_rom (s : NES) (hq : s.Quiet)
    (hrom : s.prg = Smb.prg) (hpc : s.pc = 0x94E0)
    (hI : (s.p &&& 4 == 0) = false) :
    let t := ((CPU.runTo (σ := NES) 0x94F7 14).run s).2
    finalVictory ((CPU.step (σ := NES)).run t).2 = true → finalVictory s = true := by
  apply filter_then_store_cannot_create s hq hpc hI
  simpa only [NES.toPlain, hrom] using ColumnCopy.copy_rom.1

end Smb.Routine.ColumnPrefixNes
