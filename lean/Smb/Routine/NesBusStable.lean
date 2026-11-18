import Smb.Refine

/-! CPU register and PRG preservation by the full NES bus, without quietness or support premises.
These concern the executable NES model, not hardware equivalence. -/
namespace Smb.NES.BusStable

def view (s : NES) : Regs × ByteArray :=
  (⟨s.pc, s.a, s.x, s.y, s.s, s.p⟩, s.prg)

private def coreView (s : Core) : Regs × ByteArray :=
  (⟨s.pc, s.a, s.x, s.y, s.s, s.p⟩, s.prg)

private theorem regs_of_view {s t : NES} (h : view s = view t) :
    Bus.regs s = Bus.regs t := congrArg Prod.fst h

private theorem prg_of_view {s t : NES} (h : view s = view t) :
    s.prg = t.prg := congrArg Prod.snd h

private theorem fields {s t : NES} (h : view s = view t) :
    s.pc = t.pc ∧ s.a = t.a ∧ s.x = t.x ∧ s.y = t.y ∧
    s.s = t.s ∧ s.p = t.p ∧ s.prg = t.prg := by
  simpa only [view, Prod.mk.injEq, Regs.mk.injEq, and_assoc] using h

private theorem snd_ite {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).2 = if c then x.2 else y.2 := by
  split <;> rfl

private theorem pc_ite (c : Prop) [Decidable c] (s t : NES) :
    (if c then s else t).pc = if c then s.pc else t.pc := by
  split <;> rfl

private theorem a_ite (c : Prop) [Decidable c] (s t : NES) :
    (if c then s else t).a = if c then s.a else t.a := by
  split <;> rfl

private theorem x_ite (c : Prop) [Decidable c] (s t : NES) :
    (if c then s else t).x = if c then s.x else t.x := by
  split <;> rfl

private theorem y_ite (c : Prop) [Decidable c] (s t : NES) :
    (if c then s else t).y = if c then s.y else t.y := by
  split <;> rfl

private theorem s_ite (c : Prop) [Decidable c] (s t : NES) :
    (if c then s else t).s = if c then s.s else t.s := by
  split <;> rfl

private theorem p_ite (c : Prop) [Decidable c] (s t : NES) :
    (if c then s else t).p = if c then s.p else t.p := by
  split <;> rfl

private theorem prg_ite (c : Prop) [Decidable c] (s t : NES) :
    (if c then s else t).prg = if c then s.prg else t.prg := by
  split <;> rfl

theorem sched_view (s : NES) : view (sched s) = view s :=
  congrArg coreView (core_sched s)

theorem handleEv_view (s : NES) : view (handleEv s) = view s :=
  congrArg coreView (core_handleEv s)

theorem ppuEvents_go_view (n : Nat) (s : NES) : view (ppuEvents.go n s) = view s :=
  congrArg coreView (core_ppuEvents_go n s)

theorem ppuEvents_view (s : NES) : view (ppuEvents s) = view s :=
  ppuEvents_go_view 64 s

theorem advancePpu_view (s : NES) (dots : UInt32) : view (advancePpu s dots) = view s :=
  congrArg coreView (core_advancePpu s dots)

theorem beginCycle_view (s : NES) : view (beginCycle s) = view s :=
  congrArg coreView (core_beginCycle s)

theorem endCycle_view (s : NES) : view (endCycle s) = view s := by
  have ha := fun s d => fields (advancePpu_view s d)
  unfold endCycle
  simp only [view, ha]

theorem tickS_view (s : NES) : view (tickS s) = view s := by
  rw [tickS, endCycle_view, beginCycle_view]

theorem ppuMemWrite_view (s : NES) (a : UInt16) (b : UInt8) :
    view (ppuMemWrite s a b) = view s := by
  unfold ppuMemWrite
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem ppuRegRead_view (s : NES) (a : UInt16) :
    view (ppuRegRead s a).2 = view s := by
  unfold ppuRegRead
  dsimp only
  repeat' first | rfl | split

theorem ppuRegWrite_view (s : NES) (a : UInt16) (b : UInt8) :
    view (ppuRegWrite s a b) = view s := by
  unfold ppuRegWrite
  have hs := fun s => fields (sched_view s)
  have hm := fun s a b => fields (ppuMemWrite_view s a b)
  simp only [view, pc_ite, a_ite, x_ite, y_ite, s_ite, p_ite, prg_ite, hs, hm, setOam, ite_self]

theorem readCycle_view (s : NES) (a : UInt16) :
    view (readCycle s a).2 = view s := by
  unfold readCycle
  have he := fun s => fields (endCycle_view s)
  have hr := fun s a => fields (ppuRegRead_view s a)
  have hb := fun s => fields (beginCycle_view s)
  simp only [view, snd_ite, pc_ite, a_ite, x_ite, y_ite, s_ite, p_ite, prg_ite, he, hr, hb, ite_self]

theorem oamDma_go_view (n : Nat) (i : UInt16) (s : NES) :
    view (oamDma.go n i s) = view s := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
    have hi := fun i s => fields (ih i s)
    have he := fun s => fields (endCycle_view s)
    have hw := fun s a b => fields (ppuRegWrite_view s a b)
    have hb := fun s => fields (beginCycle_view s)
    have hr := fun s a => fields (readCycle_view s a)
    simp only [oamDma.go, view, hi, he, hw, hb, hr]

theorem oamDma_view (s : NES) (haltAddr : UInt16) :
    view (oamDma s haltAddr) = view s := by
  unfold oamDma
  rw [oamDma_go_view]
  have hr := fun s a => fields (readCycle_view s a)
  simp only [view, pc_ite, a_ite, x_ite, y_ite, s_ite, p_ite, prg_ite, hr, ite_self]

theorem rdS_view (s : NES) (a : UInt16) : view (rdS s a).2 = view s := by
  rw [rdS, readCycle_view]
  split
  · exact oamDma_view s a
  · rfl

theorem wrS_view (s : NES) (a : UInt16) (b : UInt8) :
    view (wrS s a b) = view s := by
  unfold wrS
  rw [endCycle_view]
  have hw := fun s a b => fields (ppuRegWrite_view s a b)
  have hb := fun s => fields (beginCycle_view s)
  simp only [view, pc_ite, a_ite, x_ite, y_ite, s_ite, p_ite, prg_ite, hw, setRam, hb, ite_self]

theorem readCycle_regs (s : NES) (a : UInt16) : Bus.regs (readCycle s a).2 = Bus.regs s :=
  congrArg Prod.fst (readCycle_view s a)

theorem readCycle_prg (s : NES) (a : UInt16) : (readCycle s a).2.prg = s.prg :=
  congrArg Prod.snd (readCycle_view s a)

theorem rdS_regs (s : NES) (a : UInt16) : Bus.regs (rdS s a).2 = Bus.regs s :=
  congrArg Prod.fst (rdS_view s a)

theorem rdS_prg (s : NES) (a : UInt16) : (rdS s a).2.prg = s.prg :=
  congrArg Prod.snd (rdS_view s a)

theorem wrS_regs (s : NES) (a : UInt16) (b : UInt8) : Bus.regs (wrS s a b) = Bus.regs s :=
  congrArg Prod.fst (wrS_view s a b)

theorem wrS_prg (s : NES) (a : UInt16) (b : UInt8) : (wrS s a b).prg = s.prg :=
  congrArg Prod.snd (wrS_view s a b)

theorem tickS_regs (s : NES) : Bus.regs (tickS s) = Bus.regs s :=
  congrArg Prod.fst (tickS_view s)

theorem tickS_prg (s : NES) : (tickS s).prg = s.prg :=
  congrArg Prod.snd (tickS_view s)

theorem oamDma_regs (s : NES) (haltAddr : UInt16) : Bus.regs (oamDma s haltAddr) = Bus.regs s :=
  regs_of_view (s := oamDma s haltAddr) (t := s) (oamDma_view s haltAddr)

theorem oamDma_prg (s : NES) (haltAddr : UInt16) : (oamDma s haltAddr).prg = s.prg :=
  prg_of_view (s := oamDma s haltAddr) (t := s) (oamDma_view s haltAddr)

end Smb.NES.BusStable
