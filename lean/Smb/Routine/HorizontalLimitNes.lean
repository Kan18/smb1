import Smb.Routine.PlayerFrameNes
import Smb.Routine.HorizontalLimit

/-!
# Mario's horizontal limit on the full NES model

`frameK_EXIT_limit_nes`: for the game's actual ROM, the bounded run from `PlayerCtrlRoutine` to `PlayerHole` keeps the X
speed in [-40, 40] and advances `phi` by at most 2.5 pixels. The run's premises are those of `frameK_EXIT_nes`, including
`s.Quiet`, and `XInv` is a further hypothesis at entry.

It relates CPU and RAM while the PPU runs. It does not show the entry conditions hold on every legal frame, that
the PPU's unsupported flag stays false, or anything about the code after `$B179`.
-/
namespace Smb.Routine.HorizontalLimitNes
open Smb.Routine.HorizontalLimit

/-- `Rel` carries the bytes `XStep` reads. -/
theorem xstep_of_rel {r : UInt16 → UInt8} {s : NES} {t : Plain} (h : Rel s t) (hx : XStep r t.ram) : XStep r (ramAt s) := by
  have e (i : UInt16) (hi : i < 0x800) : ramAt s i = t.ram i := by rw [ramAt_of_rel h, and7ff_of_lt i hi]
  simp only [XStep, phi, pixelP, leftL, edgeR] at hx
  simp only [XStep, phi, pixelP, leftL, edgeR, e 0x57 (by decide), e 0x6D (by decide), e 0x86 (by decide), e 0x400 (by decide),
    e 0x71A (by decide), e 0x71B (by decide), e 0x71C (by decide), e 0x71D (by decide), e 0x3A1 (by decide), e 0x785 (by decide)]
  exact hx

theorem rom_climbTable : romFn 0x5F96 = 0x24 ∧ romFn 0x5F97 = 0x6D ∧ romFn 0x5F98 = 0x8A ∧ romFn 0x5F99 = 0xC6 := by
  have h := rom_climbTilesCode
  simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

set_option maxRecDepth 20000 in
theorem frame0_side_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 0)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR0 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS0 s.s))) (bgRam (frameR0 s.s (ramAt s) romFn)) romFn = 0xDD5E)
    (hx_eb : bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn) 0xEB < 0x16)
    (hx_coin : noSideCoin romFn (bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn)) = true)
    (hx_climb : noSideClimb romFn (bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn)) = true)
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn)) = true)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame0_side_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  exact xstep_of_rel hr (frame0_side_limit w s.s (ramAt s) romFn hinv hst hswim hsize hjs rom_climbTable hx_foot)

set_option maxRecDepth 20000 in
theorem frame0_impede_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 0)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR0 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS0 s.s))) (bgRam (frameR0 s.s (ramAt s) romFn)) romFn = 0xDF8A)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame0_impede_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  exact xstep_of_rel hr (frame0_impede_limit s.s (ramAt s) romFn hinv hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame0_exit_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 0)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 s.s (ramAt s) romFn) = 0xDC97)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame0_exit_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go
  exact xstep_of_rel hr (frame0_exit_limit s.s (ramAt s) romFn hinv hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame1_side_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 1)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR1 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS1 s.s))) (bgRam (frameR1 s.s (ramAt s) romFn)) romFn = 0xDD5E)
    (hx_eb : bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn) 0xEB < 0x16)
    (hx_coin : noSideCoin romFn (bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn)) = true)
    (hx_climb : noSideClimb romFn (bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn)) = true)
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn)) = true)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame1_side_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  exact xstep_of_rel hr (frame1_side_limit w s.s (ramAt s) romFn hinv hst hswim hsize hjs rom_climbTable hx_foot)

set_option maxRecDepth 20000 in
theorem frame1_impede_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 1)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR1 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS1 s.s))) (bgRam (frameR1 s.s (ramAt s) romFn)) romFn = 0xDF8A)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame1_impede_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  exact xstep_of_rel hr (frame1_impede_limit s.s (ramAt s) romFn hinv hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame1_exit_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 1)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 s.s (ramAt s) romFn) = 0xDC97)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame1_exit_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go
  exact xstep_of_rel hr (frame1_exit_limit s.s (ramAt s) romFn hinv hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame2_side_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 2)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR2 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS2 s.s))) (bgRam (frameR2 s.s (ramAt s) romFn)) romFn = 0xDD5E)
    (hx_eb : bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn) 0xEB < 0x16)
    (hx_coin : noSideCoin romFn (bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn)) = true)
    (hx_climb : noSideClimb romFn (bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn)) = true)
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn)) = true)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame2_side_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  exact xstep_of_rel hr (frame2_side_limit w s.s (ramAt s) romFn hinv hst hswim hsize hjs rom_climbTable hx_foot)

set_option maxRecDepth 20000 in
theorem frame2_impede_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 2)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR2 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS2 s.s))) (bgRam (frameR2 s.s (ramAt s) romFn)) romFn = 0xDF8A)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame2_impede_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  exact xstep_of_rel hr (frame2_impede_limit s.s (ramAt s) romFn hinv hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame2_exit_limit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 2)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 s.s (ramAt s) romFn) = 0xDC97)
    (hinv : XInv (ramAt s)) :
    XStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame2_exit_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go
  exact xstep_of_rel hr (frame2_exit_limit s.s (ramAt s) romFn hinv hst hswim hsize hjs)

end Smb.Routine.HorizontalLimitNes
