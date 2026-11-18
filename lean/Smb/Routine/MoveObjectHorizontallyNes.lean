import Smb.Routine.MoveObjectHorizontally
import Smb.RefineRun
import Smb.Game
import Std.Tactic.BVDecide

/-!
# `MoveObjectHorizontally` on the full NES model

The plain-machine theorem transfers to the full NES (PPU, DMA, NMI timing) through
`refine_runTo`, for the game's actual ROM: whenever the CPU enters the routine with NMI
generation off and nothing pending (true inside SMB's NMI handler), the run to its RTS
changes registers, position, cycles and RAM exactly as summarized.

The theorem says nothing about the PPU side of the final state. In particular the PPU may
set `unmodelled` during these cycles (e.g. at the pre-render line with sprite rendering on
and `OAMADDR ≥ 8`); a lower-bound proof that relies on supported execution must establish
that separately.
-/
namespace Smb.Routine

/-- The routine's bytes are in the game's ROM (checked by compiled evaluation). -/
theorem rom_moveObjectHorizontally :
    CodeAt (fun a => Smb.prg.get! (a &&& 0x7FFF).toNat) 0x3F0F moveObjectHorizontallyCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem moveObjectHorizontally_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0xBF0F) (hp : s.p &&& 4 ≠ 0) (hx : s.x < 0x7A) :
    let s' := ((CPU.runTo (σ := NES) 0xBF4C 40).run s).2
    let v := ramAt s (speedIdx s.x)
    s'.pc = 0xBF4C ∧ s'.x = s.x ∧ s'.s = s.s ∧
    s'.a = ramAt s' (posIdx s.x) - ramAt s (posIdx s.x) ∧ s'.y = (if v ≥ 0x80 then 0xFF else 0) ∧
    pos24 (ramAt s') s.x = (pos24 (ramAt s) s.x + sext v * 16) &&& 0xFFFFFF ∧
    s'.cyc = s.cyc + (if v ≥ 0x80 then 101 else 99) ∧
    (∀ i : UInt16, i < 0x800 → i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ forceIdx s.x → i ≠ posIdx s.x →
      i ≠ pageIdx s.x → i ≠ (0x100 ||| s.s.toUInt16) &&& 0x7FF → ramAt s' i = ramAt s i) := by
  intro s' v
  have ht : s.toPlain = ⟨⟨0xBF0F, s.a, s.x, s.y, s.s, s.p⟩, ramAt s,
      fun a => s.prg.get! (a &&& 0x7FFF).toNat, s.cyc, false⟩ := by
    simp only [NES.toPlain, hpc]; rfl
  have hcode : CodeAt (fun a => s.prg.get! (a &&& 0x7FFF).toNat) 0x3F0F moveObjectHorizontallyCode := by
    rw [hprg]; exact rom_moveObjectHorizontally
  have hsum := moveObjectHorizontally s.a s.x s.y s.s s.p (ramAt s) _ s.cyc hcode hp hx
  rw [← ht] at hsum
  obtain ⟨hbad, hpc', hx', hs', ha', hy', hpos, hcyc, hframe⟩ := hsum
  unfold moveObjectHorizontallyRun at hbad hpc' hx' hs' ha' hy' hpos hcyc hframe
  have hr := refine_runTo s hq 0xBF4C 40 hbad
  have hr_pc := congrArg Regs.pc hr.regs
  have hr_x := congrArg Regs.x hr.regs
  have hr_s := congrArg Regs.s hr.regs
  have hidem := and_idem
  have hps : ramAt s' (posIdx s.x) = ((CPU.runTo (σ := Plain) 0xBF4C 40).run s.toPlain).2.ram (posIdx s.x) := by
    rw [ramAt_of_rel hr, posIdx, hidem]
  refine ⟨hr_pc.trans hpc', hr_x.trans hx', hr_s.trans hs', ?_,
    (congrArg Regs.y hr.regs).trans hy', ?_, hr.cyc.trans hcyc, ?_⟩
  · rw [hps]; exact (congrArg Regs.a hr.regs).trans ha'
  · have hpg : ramAt s' (pageIdx s.x) = ((CPU.runTo (σ := Plain) 0xBF4C 40).run s.toPlain).2.ram (pageIdx s.x) := by
      rw [ramAt_of_rel hr, pageIdx, hidem]
    have hfo : ramAt s' (forceIdx s.x) = ((CPU.runTo (σ := Plain) 0xBF4C 40).run s.toPlain).2.ram (forceIdx s.x) := by
      rw [ramAt_of_rel hr, forceIdx, hidem]
    simp only [pos24] at hpos ⊢
    rw [hpg, hps, hfo]
    exact hpos
  · intro i hi h0 h1 h2 h3 h4 h5 h6
    have hm : i &&& 0x7FF = i := and7ff_of_lt i hi
    rw [ramAt_of_rel hr, hm]
    exact hframe i h0 h1 h2 h3 h4 h5 h6

end Smb.Routine
