import Smb.Routine.PlayerFrameNes
import Smb.Routine.PlayerFramePosition

/-!
# Falling-player position on the full NES model

Three canonical RAM cells transfer the existing position property through `Rel`.
The bounded endpoint is $B179, before PlayerHole and enemy processing. The original
Quiet, ROM, entry-state and exceptional-path assumptions all remain explicit.

This relates the CPU/RAM result while the PPU runs. It does not assert that the PPU
unsupported flag is false or that the entry assumptions hold on every legal frame.
The position comparison is against modular old-velocity movement, not against the
initial coordinate across wrapping. No routine proof is reexecuted here.
-/
namespace Smb.Routine.PlayerFramePositionNes

/-- Rel equates canonical RAM cells, not arbitrary unmasked indices of Plain.ram. -/
theorem mario_position_of_rel {s : NES} {t : Plain} (h : Rel s t) :
    ypos24 (ramAt s) 0 = ypos24 t.ram 0 := by
  have hh : ramAt s 0xB5 = t.ram 0xB5 := ramAt_of_rel h 0xB5
  have hy : ramAt s 0xCE = t.ram 0xCE := ramAt_of_rel h 0xCE
  have hf : ramAt s 0x416 = t.ram 0x416 := ramAt_of_rel h 0x416
  change ((ramAt s 0xB5).toUInt32 <<< 16 ||| (ramAt s 0xCE).toUInt32 <<< 8 |||
      (ramAt s 0x416).toUInt32) =
    ((t.ram 0xB5).toUInt32 <<< 16 ||| (t.ram 0xCE).toUInt32 <<< 8 ||| (t.ram 0x416).toUInt32)
  rw [hh, hy, hf]

set_option maxRecDepth 20000 in
theorem frame2_side_position_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
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
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn)) = true) :
    let out := ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2
    let moved := nextPos (ypos24 (ramAt s) 0) (yvel16 (ramAt s) 0)
    (ypos24 (ramAt out) 0 = moved ∨ ypos24 (ramAt out) 0 = PlayerFramePosition.rowSnap moved) ∧
      ypos24 (ramAt out) 0 ≤ moved := by
  obtain ⟨p', a', x', y', c', w, hr, hflag⟩ := Smb.Routine.frame2_side_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  have hpos := mario_position_of_rel hr
  dsimp only
  rw [hpos]
  exact PlayerFramePosition.frame2_side_position w s.s (ramAt s) romFn hst hswim hsize hjs

set_option maxRecDepth 20000 in
theorem frame2_impede_position_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
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
    (hx_foot : footCheck_pc (bgY (frameR2 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS2 s.s))) (bgRam (frameR2 s.s (ramAt s) romFn)) romFn = 0xDF8A) :
    let out := ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2
    let moved := nextPos (ypos24 (ramAt s) 0) (yvel16 (ramAt s) 0)
    (ypos24 (ramAt out) 0 = moved ∨ ypos24 (ramAt out) 0 = PlayerFramePosition.rowSnap moved) ∧
      ypos24 (ramAt out) 0 ≤ moved := by
  obtain ⟨p', c', hr, hflag⟩ := Smb.Routine.frame2_impede_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  have hpos := mario_position_of_rel hr
  dsimp only
  rw [hpos]
  exact PlayerFramePosition.frame2_impede_position s.s (ramAt s) romFn hst hswim hsize hjs

set_option maxRecDepth 20000 in
theorem frame2_exit_position_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 2)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 s.s (ramAt s) romFn) = 0xDC97) :
    let out := ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2
    let moved := nextPos (ypos24 (ramAt s) 0) (yvel16 (ramAt s) 0)
    ypos24 (ramAt out) 0 = moved := by
  obtain ⟨p', c', hr, hflag⟩ := Smb.Routine.frame2_exit_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go
  have hpos := mario_position_of_rel hr
  dsimp only
  rw [hpos]
  exact PlayerFramePosition.frame2_exit_position s.s (ramAt s) romFn hst hswim hsize hjs

end Smb.Routine.PlayerFramePositionNes

