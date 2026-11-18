import Smb.RefineRun

/-! Quiet preservation for the joypad bus addresses. Controller read values and
controller/strobe/shift-register effects are deliberately not constrained. -/
namespace Smb.NES.JoypadQuiet

theorem readCycle_core (s : NES) (a : UInt16)
    (ha : a = 0x4016 ∨ a = 0x4017)
    (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    core (readCycle s a).2 = core { s with cyc := s.cyc + 1, nmiPolled := false } := by
  rcases ha with rfl | rfl
  all_goals
    have hb := core_beginCycle s
    simp only [core, Core.mk.injEq] at hb
    unfold readCycle
    simp
    rw [core_endCycle _ (by simp [hb, hp]) (by simp [hb, hc])]
    simp [core, hb]

theorem wrS_core (s : NES) (b : UInt8)
    (hp : s.nmiPending = false) (hc : s.ctrl &&& 0x80 = 0) :
    core (wrS s 0x4016 b) = core { s with cyc := s.cyc + 1, nmiPolled := false } := by
  have hb := core_beginCycle s
  simp only [core, Core.mk.injEq] at hb
  unfold wrS
  simp only [UInt16.reduceLT, ↓reduceIte]
  rw [core_endCycle _ (by simp [hb, hp]) (by simp [hb, hc])]
  simp [core, hb]

private theorem quiet_of_core (s t : NES) (hq : s.Quiet)
    (h : core t = core { s with cyc := s.cyc + 1, nmiPolled := false }) : t.Quiet := by
  simp only [core, Core.mk.injEq] at h
  exact ⟨by simpa [h] using hq.size,
    by simpa [h] using hq.nmiOff,
    by simpa [h] using hq.noNmi,
    by simp [h],
    by simpa [h] using hq.noDma⟩

theorem rdS_core (s : NES) (a : UInt16) (hq : s.Quiet)
    (ha : a = 0x4016 ∨ a = 0x4017) :
    core (rdS s a).2 = core { s with cyc := s.cyc + 1, nmiPolled := false } := by
  simp only [rdS, hq.noDma, Bool.false_eq_true, ↓reduceIte]
  simpa only [hq.noDma] using readCycle_core s a ha hq.noNmi hq.nmiOff

theorem rdS_quiet (s : NES) (a : UInt16) (hq : s.Quiet)
    (ha : a = 0x4016 ∨ a = 0x4017) : (rdS s a).2.Quiet :=
  quiet_of_core s _ hq (rdS_core s a hq ha)

theorem wrS_quiet (s : NES) (b : UInt8) (hq : s.Quiet) :
    (wrS s 0x4016 b).Quiet :=
  quiet_of_core s _ hq (wrS_core s b hq.noNmi hq.nmiOff)

end Smb.NES.JoypadQuiet
