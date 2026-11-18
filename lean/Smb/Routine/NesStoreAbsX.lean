import Smb.Routine.NesStoreStep

/-! One full NES STA abs,X cannot create finish when A is distinct from 2, 7, 3.
This does not establish the preceding load or a legal entry history. -/
open Smb Std.WP Lean.Order
open Smb.Routine.FinishWritesNes Smb.Routine.NesStoreTail
namespace Smb.Routine.NesStoreAbsX
set_option experimental.vcgen true

attribute [local irreducible] NES.rdS NES.wrS

theorem absx_frame (s : NES) :
    ((CPU.aAbsX (σ := NES) true).run s).2.ram = s.ram ∧
    ((CPU.aAbsX (σ := NES) true).run s).2.a = s.a := by
  let lo := (CPU.fetch (σ := NES)).run s
  let hi := (CPU.fetch (σ := NES)).run lo.2
  let base := lo.1.toUInt16 ||| (hi.1.toUInt16 <<< 8)
  let addr := base + s.x.toUInt16
  let d := NES.rdS hi.2 ((base &&& 0xFF00) ||| (addr &&& 0xFF))
  have he : ((CPU.aAbsX (σ := NES) true).run s).2 = d.2 := rfl
  rw [he]
  have hlo := fetch_frame s
  have hhi := fetch_frame lo.2
  constructor
  · calc d.2.ram = hi.2.ram := NES.BusRam.rdS_ram _ _
         _ = lo.2.ram := hhi.1
         _ = s.ram := hlo.1
  · calc d.2.a = hi.2.a := read_preserves_A _ _
         _ = lo.2.a := hhi.2
         _ = s.a := hlo.2

attribute [local irreducible] CPU.aAbsX

theorem exec9D_eq : CPU.exec (σ := NES) 0x9D = CPU.st (·.a) (CPU.aAbsX true) := rfl

theorem write_safe (s : NES) (addr : UInt16) (v : UInt8)
    (h : NoFinish s) (hv : v ≠ 2 ∧ v ≠ 7 ∧ v ≠ 3) :
    NoFinish (NES.wrS s addr v) := by
  refine ⟨(write_preserves_ram_size s addr v).trans h.1, ?_⟩
  intro hf
  exact h.2 (write_cannot_create s addr v h.1 hv hf)

@[local spec] theorem exec9D_safe :
    ⦃fun s => NoFinish s ∧ (s.a ≠ 2 ∧ s.a ≠ 7 ∧ s.a ≠ 3)⦄ CPU.exec (σ := NES) 0x9D
    ⦃fun _ s => NoFinish s⦄ := by
  constructor
  intro s hs
  let q := (CPU.aAbsX (σ := NES) true).run s
  have hq := absx_frame s
  rw [exec9D_eq]
  change NoFinish (NES.wrS q.2 q.1 q.2.a)
  apply write_safe
  · exact safe_of_ram_eq s q.2 hq.1 hs.1
  · have hqa : q.2.a = s.a := hq.2
    rw [hqa]
    exact hs.2

-- Reuse only the imported local interfaces needed by stepTail; no NMI body replay.
attribute [local spec] getRegs_safe unsupported_safe nmiPolled_safe nmi_safe

theorem tail9D_safe :
    ⦃fun s => NoFinish s ∧ (s.a ≠ 2 ∧ s.a ≠ 7 ∧ s.a ≠ 3)⦄ CPU.stepTail (σ := NES) 0x9D
    ⦃fun _ s => NoFinish s⦄ := by
  vcgen [CPU.stepTail]
  all_goals assumption

theorem tail9D_cannot_create (s : NES)
    (hs : s.ram.size = 0x800) (ha : s.a ≠ 2 ∧ s.a ≠ 7 ∧ s.a ≠ 3)
    (hf : finalVictory ((CPU.stepTail (σ := NES) 0x9D).run s).2 = true) :
    finalVictory s = true := by
  by_cases h : finalVictory s = true
  · exact h
  · have ho := tail9D_safe.le_wp s ⟨⟨hs, h⟩, ha⟩
    exact False.elim (ho.2 hf)

attribute [local irreducible] CPU.fetch CPU.stepTail

/-- Actual ROM opcode fetch plus STA abs,X, unsupported-I check, and optional
NMI entry. Operand bytes, X, destination, PPU state, and DMA are unrestricted. -/
theorem step9D_cannot_create (s : NES)
    (hpc : 0x8000 ≤ s.pc) (hopcode : s.prgAt s.pc = 0x9D)
    (hs : s.ram.size = 0x800) (ha : s.a ≠ 2 ∧ s.a ≠ 7 ∧ s.a ≠ 3)
    (hf : finalVictory ((CPU.step (σ := NES)).run s).2 = true) :
    finalVictory s = true := by
  let f := (CPU.fetch (σ := NES)).run s
  have hop : f.1 = 0x9D := (NesStoreStep.fetch_rom_value s hpc).trans hopcode
  have hframe := fetch_frame s
  have hr : f.2.ram = s.ram := hframe.1
  have hA : f.2.a = s.a := hframe.2
  have hsize : f.2.ram.size = 0x800 := by rw [hr]; exact hs
  have hvalue : f.2.a ≠ 2 ∧ f.2.a ≠ 7 ∧ f.2.a ≠ 3 := by rw [hA]; exact ha
  have hstep : ((CPU.step (σ := NES)).run s).2 =
      ((CPU.stepTail (σ := NES) 0x9D).run f.2).2 := by
    change ((CPU.stepTail (σ := NES) f.1).run f.2).2 = _
    rw [hop]
  rw [hstep] at hf
  have hbefore := tail9D_cannot_create f.2 hsize hvalue hf
  rw [finish_eq_of_ram_eq s f.2 hr] at hbefore
  exact hbefore

end Smb.Routine.NesStoreAbsX
