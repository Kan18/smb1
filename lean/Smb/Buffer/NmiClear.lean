import Smb.Data.ProofRom
import Smb.Routine.Common

/-!
# Which VRAM buffer the NMI clears

The NMI draws one buffer, then at `InitBuffer` (`$80C6`–`$80DB`) clears the header of one: buffer 2's
(`$0340`/`$0341`) when the address control `$0773` is exactly 6, and buffer 1's (`$0300`/`$0301`) otherwise,
including 7, which selects the same `$0341` stream. The other buffer's offset is kept, so buffer 1's offset
carries over every update that ends with control 6. This is the clearing rule of the buffer semantics.

The checked fragment starts immediately after `UpdateScreen` returns.
-/
namespace Smb.Buffer
open Smb Smb.Routine

def clearCode : List UInt8 :=
  smbPrg% 0x80C6 24       -- sta $0773

def offsetTable : List UInt8 := smbPrg% 0x8080 2

private def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem clearCode_in_rom : CodeAt rom 0x00c6 clearCode :=
  codeAt_of_matches _ _ _ (by native_decide)

theorem offsetTable_in_rom : CodeAt rom 0x0080 offsetTable :=
  codeAt_of_matches _ _ _ (by native_decide)

set_option maxHeartbeats 3000000 in
theorem control6_clears_buffer2
    (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x00c6 clearCode)
    (htable : CodeAt prg 0x0080 offsetTable)
    (hctrl : ram 0x773 = 0x06) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x80c6, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x80de 12).run s).2
    t.bad = false ∧ t.regs.pc = 0x80de ∧
      t.ram 0x300 = ram 0x300 ∧ t.ram 0x301 = ram 0x301 ∧
      t.ram 0x340 = 0 ∧ t.ram 0x341 = 0 ∧ t.ram 0x773 = 0 := by
  dsimp only
  simp only [CodeAt, clearCode, offsetTable, UInt16.reduceAdd] at hcode htable
  generalize hr : ((CPU.runTo (σ := Plain) 0x80de 12).run
    ⟨⟨0x80c6, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hcode, htable, hctrl, hi]
  all_goals
    intros
    clear hcode htable hi
    simp_all

set_option maxHeartbeats 3000000 in
theorem non6_clears_buffer1
    (a x y sp p ctrl : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x00c6 clearCode)
    (htable : CodeAt prg 0x0080 offsetTable)
    (hctrl : ram 0x773 = ctrl) (hne : ctrl ≠ 0x06) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x80c6, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x80de 12).run s).2
    t.bad = false ∧ t.regs.pc = 0x80de ∧
      t.ram 0x300 = 0 ∧ t.ram 0x301 = 0 ∧
      t.ram 0x340 = ram 0x340 ∧ t.ram 0x341 = ram 0x341 ∧
      t.ram 0x773 = 0 := by
  dsimp only
  simp only [CodeAt, clearCode, offsetTable, UInt16.reduceAdd] at hcode htable
  generalize hr : ((CPU.runTo (σ := Plain) 0x80de 12).run
    ⟨⟨0x80c6, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hcode, htable, hctrl, hne, hi]
  all_goals
    intros
    clear hcode htable hi
    simp_all

/-! The same on the full NES model. `Quiet` is the refinement's premise: 2 KiB RAM, NMI generation off, no
pending or polled NMI, and no pending OAM DMA. The handler sets these up before this point, but these
theorems take them as given. -/

theorem control6_clears_buffer2_nes (s : NES)
    (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0x80c6) (hI : s.p &&& 4 ≠ 0)
    (hctrl : ramAt s 0x773 = 0x06) :
    let s' := ((CPU.runTo (σ := NES) 0x80de 12).run s).2
    s'.pc = 0x80de ∧
      ramAt s' 0x300 = ramAt s 0x300 ∧ ramAt s' 0x301 = ramAt s 0x301 ∧
      ramAt s' 0x340 = 0 ∧ ramAt s' 0x341 = 0 ∧ ramAt s' 0x773 = 0 := by
  intro s'
  have ht : s.toPlain = ⟨⟨0x80c6, s.a, s.x, s.y, s.s, s.p⟩, ramAt s,
      fun a => s.prg.get! (a &&& 0x7fff).toNat, s.cyc, false⟩ := by
    simp only [NES.toPlain, hpc]
    rfl
  have hc : CodeAt (fun a => s.prg.get! (a &&& 0x7fff).toNat) 0x00c6 clearCode := by
    rw [hprg]
    exact clearCode_in_rom
  have hd : CodeAt (fun a => s.prg.get! (a &&& 0x7fff).toNat) 0x0080 offsetTable := by
    rw [hprg]
    exact offsetTable_in_rom
  have hs := control6_clears_buffer2 s.a s.x s.y s.s s.p (ramAt s) _ s.cyc hc hd hctrl hI
  rw [← ht] at hs
  obtain ⟨hbad, hpc', h300, h301, h340, h341, h773⟩ := hs
  have hr := refine_runTo s hq 0x80de 12 hbad
  have hram (i : UInt16) (hi : i < 0x800) :
      ramAt s' i = ((CPU.runTo (σ := Plain) 0x80de 12).run s.toPlain).2.ram i := by
    rw [ramAt_of_rel hr, and7ff_of_lt i hi]
  refine ⟨(congrArg Regs.pc hr.regs).trans hpc', ?_, ?_, ?_, ?_, ?_⟩
  · exact (hram 0x300 (by decide)).trans h300
  · exact (hram 0x301 (by decide)).trans h301
  · exact (hram 0x340 (by decide)).trans h340
  · exact (hram 0x341 (by decide)).trans h341
  · exact (hram 0x773 (by decide)).trans h773

theorem non6_clears_buffer1_nes (s : NES) (ctrl : UInt8)
    (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0x80c6) (hI : s.p &&& 4 ≠ 0)
    (hctrl : ramAt s 0x773 = ctrl) (hne : ctrl ≠ 0x06) :
    let s' := ((CPU.runTo (σ := NES) 0x80de 12).run s).2
    s'.pc = 0x80de ∧
      ramAt s' 0x300 = 0 ∧ ramAt s' 0x301 = 0 ∧
      ramAt s' 0x340 = ramAt s 0x340 ∧ ramAt s' 0x341 = ramAt s 0x341 ∧
      ramAt s' 0x773 = 0 := by
  intro s'
  have ht : s.toPlain = ⟨⟨0x80c6, s.a, s.x, s.y, s.s, s.p⟩, ramAt s,
      fun a => s.prg.get! (a &&& 0x7fff).toNat, s.cyc, false⟩ := by
    simp only [NES.toPlain, hpc]
    rfl
  have hc : CodeAt (fun a => s.prg.get! (a &&& 0x7fff).toNat) 0x00c6 clearCode := by
    rw [hprg]
    exact clearCode_in_rom
  have hd : CodeAt (fun a => s.prg.get! (a &&& 0x7fff).toNat) 0x0080 offsetTable := by
    rw [hprg]
    exact offsetTable_in_rom
  have hs := non6_clears_buffer1 s.a s.x s.y s.s s.p ctrl (ramAt s) _ s.cyc hc hd hctrl hne hI
  rw [← ht] at hs
  obtain ⟨hbad, hpc', h300, h301, h340, h341, h773⟩ := hs
  have hr := refine_runTo s hq 0x80de 12 hbad
  have hram (i : UInt16) (hi : i < 0x800) :
      ramAt s' i = ((CPU.runTo (σ := Plain) 0x80de 12).run s.toPlain).2.ram i := by
    rw [ramAt_of_rel hr, and7ff_of_lt i hi]
  refine ⟨(congrArg Regs.pc hr.regs).trans hpc', ?_, ?_, ?_, ?_, ?_⟩
  · exact (hram 0x300 (by decide)).trans h300
  · exact (hram 0x301 (by decide)).trans h301
  · exact (hram 0x340 (by decide)).trans h340
  · exact (hram 0x341 (by decide)).trans h341
  · exact (hram 0x773 (by decide)).trans h773


end Smb.Buffer
