import Smb.Routine.NesBusRam
import Smb.Routine.NesBusStable

/-! RAM/ROM read values in the full NES model, including pending DMA.
Only the address range is restricted; no quietness or support premise is needed. -/
namespace Smb.NES.BusReadValues

theorem readCycle_ram_value (s : NES) (a : UInt16) (ha : a < 0x2000) :
    (readCycle s a).1 = s.ram.get! (a &&& 0x7FF).toNat := by
  unfold readCycle
  dsimp only
  simp only [ha, ↓reduceIte, not_le_of_lt_2000 ha, decide_false,
    Bool.false_and, Bool.false_eq_true, BusRam.beginCycle_ram]

theorem readCycle_rom_value (s : NES) (a : UInt16) (ha : 0x8000 ≤ a) :
    (readCycle s a).1 = s.prgAt a := by
  have hb : (beginCycle s).prg = s.prg :=
    congrArg Prod.snd (BusStable.beginCycle_view s)
  obtain ⟨h1, h2, h3, h4⟩ := lt_of_ge_8000 ha
  unfold readCycle
  dsimp only
  simp [h1, h2, h3, h4, ha, beq_iff_eq, Bool.or_eq_true, prgAt, hb]

theorem rdS_ram_value (s : NES) (a : UInt16) (ha : a < 0x2000) :
    (rdS s a).1 = s.ram.get! (a &&& 0x7FF).toNat := by
  unfold rdS
  rw [readCycle_ram_value _ a ha]
  split
  · rw [BusRam.oamDma_ram]
  · rfl

theorem rdS_rom_value (s : NES) (a : UInt16) (ha : 0x8000 ≤ a) :
    (rdS s a).1 = s.prgAt a := by
  unfold rdS
  rw [readCycle_rom_value _ a ha]
  split
  · simp only [prgAt, BusStable.oamDma_prg]
  · rfl

end Smb.NES.BusReadValues
