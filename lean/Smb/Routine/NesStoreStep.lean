import Smb.Routine.NesStoreTail
import Smb.Routine.NesBusReadValues

open Smb
open Smb.Routine.FinishWritesNes
open Smb.Routine.NesStoreTail
namespace Smb.Routine.NesStoreStep

-- Do not expose PPU/DMA implementations during the instruction-level composition.
attribute [local irreducible] NES.rdS

/-- Actual opcode fetch from ROM, including pending DMA and arbitrary PPU state.
The fetch increments PC before the read but still reads the old address. -/
theorem fetch_rom_value (s : NES) (hpc : 0x8000 ≤ s.pc) :
    ((CPU.fetch (σ := NES)).run s).1 = s.prgAt s.pc := by
  change (NES.rdS {s with pc := s.pc + 1} s.pc).1 = s.prgAt s.pc
  exact NES.BusReadValues.rdS_rom_value _ _ hpc

attribute [local irreducible] CPU.fetch CPU.stepTail

/-- Whole CPU.step, not just a selected tail. The ROM-range and actual opcode
hypotheses justify the initial fetch; operand/address bytes are unrestricted.
The imported tail theorem includes the post-instruction NMI branch. -/
theorem step91_cannot_create (s : NES)
    (hpc : 0x8000 ≤ s.pc) (hopcode : s.prgAt s.pc = 0x91)
    (hs : s.ram.size = 0x800) (ha : s.a = 0 ∨ 0x10 ≤ s.a)
    (hf : finalVictory ((CPU.step (σ := NES)).run s).2 = true) :
    finalVictory s = true := by
  let f := (CPU.fetch (σ := NES)).run s
  have hop : f.1 = 0x91 := (fetch_rom_value s hpc).trans hopcode
  have hframe := fetch_frame s
  have hr : f.2.ram = s.ram := hframe.1
  have hA : f.2.a = s.a := hframe.2
  have hsize : f.2.ram.size = 0x800 := by rw [hr]; exact hs
  have hvalue : f.2.a = 0 ∨ 0x10 ≤ f.2.a := by rw [hA]; exact ha
  have hstep : ((CPU.step (σ := NES)).run s).2 =
      ((CPU.stepTail (σ := NES) 0x91).run f.2).2 := by
    change ((CPU.stepTail (σ := NES) f.1).run f.2).2 = _
    rw [hop]
  rw [hstep] at hf
  have hbefore := tail91_cannot_create f.2 hsize hvalue hf
  rw [finish_eq_of_ram_eq s f.2 hr] at hbefore
  exact hbefore

end Smb.Routine.NesStoreStep
