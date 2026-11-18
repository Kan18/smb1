import Smb.Routine.ImposeGravity

/-! # `ImposeGravity` on the full NES model, for the game's ROM -/
namespace Smb.Routine

theorem rom_imposeGravity :
    CodeAt (fun a => Smb.prg.get! (a &&& 0x7FFF).toNat) 0x3FD7 imposeGravityCode :=
  codeAt_of_matches _ _ _ (by native_decide)

/-- Entering `$BFD7` with NMI generation off, the I flag set, object offset `X < $32`, speed in
[−64, 63] and maximum speed below 64, the run to the RTS moves the object by its 8.8 velocity
and updates the velocity as `gravityVel`, with `A`, `Y` and the cycle count as in the summary,
changing no other RAM than the object's five bytes, `$07` and one stack byte.

As with `moveObjectHorizontally_nes`, nothing is claimed about the PPU side of the final
state, including `unmodelled`. -/
theorem imposeGravity_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0xBFD7) (hp : s.p &&& 4 ≠ 0) (hx : s.x < 0x32)
    (hspd : ramAt s (ySpeedIdx s.x) + 0x40 < 0x80) (hmax : ramAt s 2 < 0x40) :
    let s' := ((CPU.runTo (σ := NES) 0xC046 60).run s).2
    s'.pc = 0xC046 ∧ s'.x = s.x ∧ s'.s = s.s ∧
    s'.a = gravityA s.a (ramAt s 0) (ramAt s 1) (ramAt s 2) (yvel16 (ramAt s) s.x) ∧
    s'.y = (bif s.a == 0 then (bif 0x80 ≤ ramAt s (ySpeedIdx s.x) then 0xFF else 0) else 0 - ramAt s 2) ∧
    s'.cyc = s.cyc + gravityCycles s.a (ramAt s 0) (ramAt s 1) (ramAt s 2) (yvel16 (ramAt s) s.x) ∧
    ypos24 (ramAt s') s.x = (ypos24 (ramAt s) s.x + sext16 (yvel16 (ramAt s) s.x)) &&& 0xFFFFFF ∧
    yvel16 (ramAt s') s.x =
      gravityVel s.a (ramAt s 0) (ramAt s 1) (ramAt s 2) (yvel16 (ramAt s) s.x) ∧
    (∀ i : UInt16, i < 0x800 → i ≠ 7 → i ≠ dummyIdx s.x → i ≠ yForceIdx s.x → i ≠ ySpeedIdx s.x →
      i ≠ yPosIdx s.x → i ≠ yHighIdx s.x → i ≠ (0x100 ||| s.s.toUInt16) &&& 0x7FF →
      ramAt s' i = ramAt s i) := by
  intro s'
  have ht : s.toPlain = ⟨⟨0xBFD7, s.a, s.x, s.y, s.s, s.p⟩, ramAt s,
      fun a => s.prg.get! (a &&& 0x7FFF).toNat, s.cyc, false⟩ := by
    simp only [NES.toPlain, hpc]; rfl
  have hcode : CodeAt (fun a => s.prg.get! (a &&& 0x7FFF).toNat) 0x3FD7 imposeGravityCode := by
    rw [hprg]; exact rom_imposeGravity
  have hsum := imposeGravity s.a s.x s.y s.s s.p (ramAt s) _ s.cyc hcode hp hx hspd hmax
  rw [← ht] at hsum
  obtain ⟨hbad, hpc', hx', hs', ha', hy', hcyc, hpos, hvel, hframe⟩ := hsum
  unfold imposeGravityRun at hbad hpc' hx' hs' ha' hy' hcyc hpos hvel hframe
  have hr := refine_runTo s hq 0xC046 60 hbad
  have hidem := and_idem
  -- RAM of the final NES state at a masked index is the plain run's RAM there.
  have e : ∀ i, i &&& 0x7FF = i → ramAt s' i = ((CPU.runTo (σ := Plain) 0xC046 60).run s.toPlain).2.ram i := by
    intro i hi; rw [ramAt_of_rel hr, hi]
  have m : ∀ (b : UInt16), (b &&& 0x7FF) &&& 0x7FF = b &&& 0x7FF := fun b => hidem b 0x7FF
  refine ⟨(congrArg Regs.pc hr.regs).trans hpc', (congrArg Regs.x hr.regs).trans hx',
    (congrArg Regs.s hr.regs).trans hs', (congrArg Regs.a hr.regs).trans ha',
    (congrArg Regs.y hr.regs).trans hy', hr.cyc.trans hcyc, ?_, ?_, ?_⟩
  · simp only [ypos24, yvel16] at hpos ⊢
    rw [e (yHighIdx s.x) (by simp only [yHighIdx, m]), e (yPosIdx s.x) (by simp only [yPosIdx, m]),
      e (dummyIdx s.x) (by simp only [dummyIdx, m])]
    exact hpos
  · simp only [yvel16] at hvel ⊢
    rw [e (ySpeedIdx s.x) (by simp only [ySpeedIdx, m]), e (yForceIdx s.x) (by simp only [yForceIdx, m])]
    exact hvel
  · intro i hi h0 h1 h2 h3 h4 h5 h6
    have hm : i &&& 0x7FF = i := and7ff_of_lt i hi
    rw [e i hm]
    exact hframe i h0 h1 h2 h3 h4 h5 h6

end Smb.Routine
