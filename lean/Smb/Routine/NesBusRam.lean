import Smb.Refine

/-! CPU RAM effects of the full NES bus, without quietness or support premises.
These concern the executable NES model, not hardware equivalence. -/
namespace Smb.NES.BusRam

private theorem ram_ite (c : Prop) [Decidable c] (s t : NES) :
    (if c then s else t).ram = if c then s.ram else t.ram := by
  split <;> rfl

private theorem snd_ite {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).2 = if c then x.2 else y.2 := by
  split <;> rfl

theorem sched_ram (s : NES) : (sched s).ram = s.ram :=
  congrArg Core.ram (core_sched s)

theorem handleEv_ram (s : NES) : (handleEv s).ram = s.ram :=
  congrArg Core.ram (core_handleEv s)

theorem ppuEvents_go_ram (n : Nat) (s : NES) : (ppuEvents.go n s).ram = s.ram :=
  congrArg Core.ram (core_ppuEvents_go n s)

theorem ppuEvents_ram (s : NES) : (ppuEvents s).ram = s.ram :=
  ppuEvents_go_ram 64 s

theorem advancePpu_ram (s : NES) (dots : UInt32) : (advancePpu s dots).ram = s.ram :=
  congrArg Core.ram (core_advancePpu s dots)

theorem beginCycle_ram (s : NES) : (beginCycle s).ram = s.ram :=
  congrArg Core.ram (core_beginCycle s)

theorem endCycle_ram (s : NES) : (endCycle s).ram = s.ram := by
  simp only [endCycle, advancePpu_ram]

theorem tickS_ram (s : NES) : (tickS s).ram = s.ram := by
  rw [tickS, endCycle_ram, beginCycle_ram]

theorem ppuMemWrite_ram (s : NES) (a : UInt16) (b : UInt8) :
    (ppuMemWrite s a b).ram = s.ram := by
  unfold ppuMemWrite
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem ppuRegRead_ram (s : NES) (a : UInt16) :
    (ppuRegRead s a).2.ram = s.ram := by
  unfold ppuRegRead
  dsimp only
  repeat' first | rfl | split

theorem ppuRegWrite_ram (s : NES) (a : UInt16) (b : UInt8) :
    (ppuRegWrite s a b).ram = s.ram := by
  unfold ppuRegWrite
  simp only [ram_ite, sched_ram, ppuMemWrite_ram, setOam, ite_self]

theorem readCycle_ram (s : NES) (a : UInt16) :
    (readCycle s a).2.ram = s.ram := by
  unfold readCycle
  simp only [snd_ite, ram_ite, endCycle_ram, ppuRegRead_ram, beginCycle_ram, ite_self]

theorem oamDma_go_ram (n : Nat) (i : UInt16) (s : NES) :
    (oamDma.go n i s).ram = s.ram := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
    simp only [oamDma.go, ih, endCycle_ram, ppuRegWrite_ram, beginCycle_ram, readCycle_ram]

theorem oamDma_ram (s : NES) (haltAddr : UInt16) :
    (oamDma s haltAddr).ram = s.ram := by
  unfold oamDma
  rw [oamDma_go_ram]
  split <;> simp only [readCycle_ram]

theorem rdS_ram (s : NES) (a : UInt16) : (rdS s a).2.ram = s.ram := by
  rw [rdS, readCycle_ram]
  split
  · exact oamDma_ram s a
  · rfl

theorem wrS_ram (s : NES) (a : UInt16) (b : UInt8) :
    (wrS s a b).ram =
      if a < 0x2000 then s.ram.set! (a &&& 0x7FF).toNat b else s.ram := by
  unfold wrS
  rw [endCycle_ram]
  dsimp only
  split
  · simp only [setRam, beginCycle_ram]
  · repeat' first
      | rfl
      | (simp only [ppuRegWrite_ram, beginCycle_ram]; done)
      | split

end Smb.NES.BusRam
