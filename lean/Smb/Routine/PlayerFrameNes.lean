import Smb.Summary
import Smb.Routine.PlayerFrame
import Smb.RefineRun
import Smb.Game

/-!
# The frame theorems on the full NES model

`frameK_EXIT_nes`: for the game's actual ROM, whenever `PlayerCtrlRoutine` is entered with NMI generation off and nothing pending
(`s.Quiet`, an explicit call-site assumption), the full model's run to `PlayerHole` `$B179` relates (`Rel`) to the end state of `frameK_EXIT_reach`:
registers, RAM and the cycle count. Through `refine_runTo`, which needs the plain run not to be `bad`: `frameK_EXIT_no_bad`.

As for `moveObjectHorizontally_nes`, this says nothing about the PPU side of the final state, and it does not show that the conditions hold at any
frame. `Quiet` is a hypothesis too.
-/
namespace Smb.Routine

/-- The game's ROM, addressed as the plain machine reads it. -/
abbrev romFn : UInt16 → UInt8 := fun a => Smb.prg.get! (a &&& 0x7FFF).toNat

theorem rom_ctrlPreCode : CodeAt romFn 0x30E9 ctrlPreCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_ctrlJsrCode : CodeAt romFn 0x312B ctrlJsrCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_ctrlMidCode : CodeAt romFn 0x312E ctrlMidCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_ctrlAuxCode : CodeAt romFn 0x314C ctrlAuxCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_movementSubsCode : CodeAt romFn 0x3329 movementSubsCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_jumpEngineCode : CodeAt romFn 0x0E04 jumpEngineCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_physicsCode : CodeAt romFn 0x3424 physicsCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_jumpStartCode : CodeAt romFn 0x3424 jumpStartCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_animSpeedCode : CodeAt romFn 0x358C animSpeedCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_imposeFrictionCode : CodeAt romFn 0x35CC imposeFrictionCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_movePlayerHorizontallyCode : CodeAt romFn 0x3F09 movePlayerHorizontallyCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_movePlayerVerticallyCode : CodeAt romFn 0x3F4D movePlayerVerticallyCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_imposeGravityCode : CodeAt romFn 0x3FD7 imposeGravityCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_scrollCode : CodeAt romFn 0x2F93 scrollCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_xOffscreenBitsData : CodeAt romFn 0x71E3 xOffscreenBitsData := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_getXOffscreenBitsCode : CodeAt romFn 0x71F3 getXOffscreenBitsCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_dividePDiffCode : CodeAt romFn 0x726D dividePDiffCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_getPlayerOffscreenBitsCode : CodeAt romFn 0x7180 getPlayerOffscreenBitsCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_getOffScreenBitsSetCode : CodeAt romFn 0x71C0 getOffScreenBitsSetCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_yOffscreenBitsData : CodeAt romFn 0x722B yOffscreenBitsData := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_getYOffscreenBitsCode : CodeAt romFn 0x7234 getYOffscreenBitsCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_relativePlayerPositionCode : CodeAt romFn 0x712A relativePlayerPositionCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_relWOfsCode : CodeAt romFn 0x7142 relWOfsCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_getObjRelativePositionCode : CodeAt romFn 0x7171 getObjRelativePositionCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_boundingBoxCoreCode : CodeAt romFn 0x629C boundingBoxCoreCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_ctrlJsrBgCode : CodeAt romFn 0x315A ctrlJsrBgCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_ctrlAttrCode : CodeAt romFn 0x315D ctrlAttrCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_bgPreCode : CodeAt romFn 0x5C64 bgPreCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_bgSizeCode : CodeAt romFn 0x5C98 bgSizeCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_gbbAdrCode : CodeAt romFn 0x5CAB gbbAdrCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_headChkCode : CodeAt romFn 0x5CBA headChkCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_doFootCheckCode : CodeAt romFn 0x5CF6 doFootCheckCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_tileClassCode : CodeAt romFn 0x5F8B tileClassCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_adderCode : CodeAt romFn 0x63AD adderCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_blockBufferCode : CodeAt romFn 0x63B0 blockBufferCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_getBlockBufferAddrCode : CodeAt romFn 0x1BDD getBlockBufferAddrCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_chkFootCode : CodeAt romFn 0x5D1D chkFootCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_landPlyrCode : CodeAt romFn 0x5D44 landPlyrCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_climbTilesCode : CodeAt romFn 0x5F96 climbTilesCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_invisibleTilesCode : CodeAt romFn 0x5EBD invisibleTilesCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_landCalleesCode : CodeAt romFn 0x5EC4 landCalleesCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_pipeTestCode : CodeAt romFn 0x5EEE pipeTestCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_hrts : romFn 0x5F4A = 0x60 := by native_decide
theorem rom_impedeCode : CodeAt romFn 0x5F4B impedeCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_sideCheckCode : CodeAt romFn 0x5D5E sideCheckCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_stopPlayerMoveCode : CodeAt romFn 0x5DFF stopPlayerMoveCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_chkInvisibleCode : CodeAt romFn 0x5EBD chkInvisibleCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_chkJumpspringCode : CodeAt romFn 0x5EDD chkJumpspringCode := codeAt_of_matches _ _ _ (by native_decide)
theorem rom_climbingCode : CodeAt romFn 0x33C7 climbingCode := codeAt_of_matches _ _ _ (by native_decide)

theorem toPlain_at_ctrl (s : NES) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) :
    s.toPlain = ⟨⟨0xB0E9, s.a, s.x, s.y, s.s, s.p⟩, ramAt s, romFn, s.cyc, false⟩ := by
  simp only [NES.toPlain, hpc, hprg]; rfl

/-- A plain run's known end state, not `bad`, is what the full model's run relates to. -/
theorem nes_of_reach (s : NES) (hq : s.Quiet) (stop : UInt16) (n : Nat) (F : Plain)
    (h : ((CPU.runTo (σ := Plain) stop n).run s.toPlain).2 = F) (hb : F.bad = false) :
    Rel ((CPU.runTo (σ := NES) stop n).run s).2 F := by
  subst h; exact refine_runTo s hq stop n hb

summary_regs chkFoot

theorem footCheck_bad_pass (y sp : UInt8) (ram prg : UInt16 → UInt8) (bad : Bool) :
    footCheck_bad y sp ram prg bad = bad := by
  delta footCheck_bad
  simp only [chkFoot_bad_eq]
  bv_decide (config := { enums := false })

theorem frame0_side_no_bad (sp : UInt8) (ram prg : UInt16 → UInt8) : frame0_side_bad sp ram prg = false := by
  delta frame0_side_bad bgSide_bad ctrlJ_bad ctrlA0_bad
  simp only [ctrlAttr_bad_eq, footCheck_bad_pass, bgSize_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame0_impede_no_bad (sp : UInt8) (ram prg : UInt16 → UInt8) : frame0_impede_bad sp ram prg = false := by
  delta frame0_impede_bad bgImpede_bad ctrlJ_bad ctrlA0_bad
  simp only [ctrlAttr_bad_eq, footCheck_bad_pass, bgSize_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame0_exit_no_bad : frame0_exit_bad = false := by
  delta frame0_exit_bad ctrlJ_bad ctrlA0_bad
  simp only [ctrlAttr_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame1_side_no_bad (sp : UInt8) (ram prg : UInt16 → UInt8) : frame1_side_bad sp ram prg = false := by
  delta frame1_side_bad bgSide_bad ctrlJ_bad ctrlA1_bad
  simp only [ctrlAttr_bad_eq, footCheck_bad_pass, bgSize_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame1_impede_no_bad (sp : UInt8) (ram prg : UInt16 → UInt8) : frame1_impede_bad sp ram prg = false := by
  delta frame1_impede_bad bgImpede_bad ctrlJ_bad ctrlA1_bad
  simp only [ctrlAttr_bad_eq, footCheck_bad_pass, bgSize_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame1_exit_no_bad : frame1_exit_bad = false := by
  delta frame1_exit_bad ctrlJ_bad ctrlA1_bad
  simp only [ctrlAttr_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame2_side_no_bad (sp : UInt8) (ram prg : UInt16 → UInt8) : frame2_side_bad sp ram prg = false := by
  delta frame2_side_bad bgSide_bad ctrlJ_bad ctrlA2_bad
  simp only [ctrlAttr_bad_eq, footCheck_bad_pass, bgSize_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame2_impede_no_bad (sp : UInt8) (ram prg : UInt16 → UInt8) : frame2_impede_bad sp ram prg = false := by
  delta frame2_impede_bad bgImpede_bad ctrlJ_bad ctrlA2_bad
  simp only [ctrlAttr_bad_eq, footCheck_bad_pass, bgSize_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame2_exit_no_bad : frame2_exit_bad = false := by
  delta frame2_exit_bad ctrlJ_bad ctrlA2_bad
  simp only [ctrlAttr_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame3_side_no_bad (sp : UInt8) (ram prg : UInt16 → UInt8) : frame3_side_bad sp ram prg = false := by
  delta frame3_side_bad bgSide_bad ctrlJ_bad ctrlA3_bad
  simp only [ctrlAttr_bad_eq, footCheck_bad_pass, bgSize_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame3_impede_no_bad (sp : UInt8) (ram prg : UInt16 → UInt8) : frame3_impede_bad sp ram prg = false := by
  delta frame3_impede_bad bgImpede_bad ctrlJ_bad ctrlA3_bad
  simp only [ctrlAttr_bad_eq, footCheck_bad_pass, bgSize_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

theorem frame3_exit_no_bad : frame3_exit_bad = false := by
  delta frame3_exit_bad ctrlJ_bad ctrlA3_bad
  simp only [ctrlAttr_bad_eq, bgPre_bad_eq, ctrlAux_bad_eq, ctrlMid_bad_eq]
  decide

set_option maxRecDepth 20000 in
theorem frame0_side_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
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
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn)) = true) :
    ∃ p' a' x' y' c' w, Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame0_side_pc, a', x', y', frame0_side_s s.s, p'⟩, frame0_side_ram w s.s (ramAt s) romFn, romFn, c', frame0_side_bad s.s (ramAt s) romFn⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', a', x', y', c', w, h, hf⟩ := frame0_side_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode rom_sideCheckCode rom_stopPlayerMoveCode rom_chkInvisibleCode rom_chkJumpspringCode hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  rw [← ht] at h
  exact ⟨p', a', x', y', c', w, nes_of_reach s hq _ _ _ h (frame0_side_no_bad _ _ _), hf⟩

set_option maxRecDepth 20000 in
theorem frame0_impede_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
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
    (hx_foot : footCheck_pc (bgY (frameR0 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS0 s.s))) (bgRam (frameR0 s.s (ramAt s) romFn)) romFn = 0xDF8A) :
    ∃ p' c', Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame0_impede_pc, frame0_impede_a s.s (ramAt s) romFn, frame0_impede_x s.s (ramAt s) romFn, frame0_impede_y s.s (ramAt s) romFn, frame0_impede_s s.s, p'⟩, frame0_impede_ram s.s (ramAt s) romFn, romFn, c', frame0_impede_bad s.s (ramAt s) romFn⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', c', h, hf⟩ := frame0_impede_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  rw [← ht] at h
  exact ⟨p', c', nes_of_reach s hq _ _ _ h (frame0_impede_no_bad _ _ _), hf⟩

set_option maxRecDepth 20000 in
theorem frame0_exit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 0)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 s.s (ramAt s) romFn) = 0xDC97) :
    ∃ p' c', Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame0_exit_pc, frame0_exit_a s.s (ramAt s) romFn, frame0_exit_x, frame0_exit_y s.s (ramAt s) romFn, frame0_exit_s s.s, p'⟩, frame0_exit_ram s.s (ramAt s) romFn, romFn, c', frame0_exit_bad⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', c', h, hf⟩ := frame0_exit_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode hI hst hsize hswim hjs hspd hx_go
  rw [← ht] at h
  exact ⟨p', c', nes_of_reach s hq _ _ _ h frame0_exit_no_bad, hf⟩

set_option maxRecDepth 20000 in
theorem frame1_side_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
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
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn)) = true) :
    ∃ p' a' x' y' c' w, Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame1_side_pc, a', x', y', frame1_side_s s.s, p'⟩, frame1_side_ram w s.s (ramAt s) romFn, romFn, c', frame1_side_bad s.s (ramAt s) romFn⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', a', x', y', c', w, h, hf⟩ := frame1_side_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode rom_sideCheckCode rom_stopPlayerMoveCode rom_chkInvisibleCode rom_chkJumpspringCode hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  rw [← ht] at h
  exact ⟨p', a', x', y', c', w, nes_of_reach s hq _ _ _ h (frame1_side_no_bad _ _ _), hf⟩

set_option maxRecDepth 20000 in
theorem frame1_impede_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
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
    (hx_foot : footCheck_pc (bgY (frameR1 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS1 s.s))) (bgRam (frameR1 s.s (ramAt s) romFn)) romFn = 0xDF8A) :
    ∃ p' c', Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame1_impede_pc, frame1_impede_a s.s (ramAt s) romFn, frame1_impede_x s.s (ramAt s) romFn, frame1_impede_y s.s (ramAt s) romFn, frame1_impede_s s.s, p'⟩, frame1_impede_ram s.s (ramAt s) romFn, romFn, c', frame1_impede_bad s.s (ramAt s) romFn⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', c', h, hf⟩ := frame1_impede_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  rw [← ht] at h
  exact ⟨p', c', nes_of_reach s hq _ _ _ h (frame1_impede_no_bad _ _ _), hf⟩

set_option maxRecDepth 20000 in
theorem frame1_exit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 1)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 s.s (ramAt s) romFn) = 0xDC97) :
    ∃ p' c', Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame1_exit_pc, frame1_exit_a s.s (ramAt s) romFn, frame1_exit_x, frame1_exit_y s.s (ramAt s) romFn, frame1_exit_s s.s, p'⟩, frame1_exit_ram s.s (ramAt s) romFn, romFn, c', frame1_exit_bad⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', c', h, hf⟩ := frame1_exit_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode hI hst hsize hswim hjs hspd hx_go
  rw [← ht] at h
  exact ⟨p', c', nes_of_reach s hq _ _ _ h frame1_exit_no_bad, hf⟩

set_option maxRecDepth 20000 in
theorem frame2_side_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
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
    ∃ p' a' x' y' c' w, Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame2_side_pc, a', x', y', frame2_side_s s.s, p'⟩, frame2_side_ram w s.s (ramAt s) romFn, romFn, c', frame2_side_bad s.s (ramAt s) romFn⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', a', x', y', c', w, h, hf⟩ := frame2_side_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode rom_sideCheckCode rom_stopPlayerMoveCode rom_chkInvisibleCode rom_chkJumpspringCode hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  rw [← ht] at h
  exact ⟨p', a', x', y', c', w, nes_of_reach s hq _ _ _ h (frame2_side_no_bad _ _ _), hf⟩

set_option maxRecDepth 20000 in
theorem frame2_impede_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
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
    ∃ p' c', Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame2_impede_pc, frame2_impede_a s.s (ramAt s) romFn, frame2_impede_x s.s (ramAt s) romFn, frame2_impede_y s.s (ramAt s) romFn, frame2_impede_s s.s, p'⟩, frame2_impede_ram s.s (ramAt s) romFn, romFn, c', frame2_impede_bad s.s (ramAt s) romFn⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', c', h, hf⟩ := frame2_impede_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  rw [← ht] at h
  exact ⟨p', c', nes_of_reach s hq _ _ _ h (frame2_impede_no_bad _ _ _), hf⟩

set_option maxRecDepth 20000 in
theorem frame2_exit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 2)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 s.s (ramAt s) romFn) = 0xDC97) :
    ∃ p' c', Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame2_exit_pc, frame2_exit_a s.s (ramAt s) romFn, frame2_exit_x, frame2_exit_y s.s (ramAt s) romFn, frame2_exit_s s.s, p'⟩, frame2_exit_ram s.s (ramAt s) romFn, romFn, c', frame2_exit_bad⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', c', h, hf⟩ := frame2_exit_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode hI hst hsize hswim hjs hspd hx_go
  rw [← ht] at h
  exact ⟨p', c', nes_of_reach s hq _ _ _ h frame2_exit_no_bad, hf⟩

set_option maxRecDepth 20000 in
theorem frame3_side_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 3)
    (hsize : (ramAt s) 0x70B = 0)
    (hx_go : bgPre_pc (frameR3 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR3 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS3 s.s))) (bgRam (frameR3 s.s (ramAt s) romFn)) romFn = 0xDD5E)
    (hx_eb : bgFootRam (frameS3 s.s) romFn (frameR3 s.s (ramAt s) romFn) 0xEB < 0x16)
    (hx_coin : noSideCoin romFn (bgFootRam (frameS3 s.s) romFn (frameR3 s.s (ramAt s) romFn)) = true)
    (hx_climb : noSideClimb romFn (bgFootRam (frameS3 s.s) romFn (frameR3 s.s (ramAt s) romFn)) = true)
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS3 s.s) romFn (frameR3 s.s (ramAt s) romFn)) = true) :
    ∃ p' a' x' y' c' w, Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame3_side_pc, a', x', y', frame3_side_s s.s, p'⟩, frame3_side_ram w s.s (ramAt s) romFn, romFn, c', frame3_side_bad s.s (ramAt s) romFn⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', a', x', y', c', w, h, hf⟩ := frame3_side_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode rom_sideCheckCode rom_stopPlayerMoveCode rom_chkInvisibleCode rom_chkJumpspringCode rom_climbingCode hI hst hsize hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  rw [← ht] at h
  exact ⟨p', a', x', y', c', w, nes_of_reach s hq _ _ _ h (frame3_side_no_bad _ _ _), hf⟩

set_option maxRecDepth 20000 in
theorem frame3_impede_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 3)
    (hsize : (ramAt s) 0x70B = 0)
    (hx_go : bgPre_pc (frameR3 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR3 s.s (ramAt s) romFn)) (bgY (frameR3 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR3 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS3 s.s))) (bgRam (frameR3 s.s (ramAt s) romFn)) romFn = 0xDF8A) :
    ∃ p', Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame3_impede_pc, frame3_impede_a s.s (ramAt s) romFn, frame3_impede_x s.s (ramAt s) romFn, frame3_impede_y s.s (ramAt s) romFn, frame3_impede_s s.s, p'⟩, frame3_impede_ram s.s (ramAt s) romFn, romFn, frame3_impede_cyc s.s (ramAt s) romFn s.cyc, frame3_impede_bad s.s (ramAt s) romFn⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', h, hf⟩ := frame3_impede_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode rom_climbingCode hI hst hsize hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  rw [← ht] at h
  exact ⟨p', nes_of_reach s hq _ _ _ h (frame3_impede_no_bad _ _ _), hf⟩

set_option maxRecDepth 20000 in
theorem frame3_exit_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 3)
    (hsize : (ramAt s) 0x70B = 0)
    (hx_go : bgPre_pc (frameR3 s.s (ramAt s) romFn) = 0xDC97) :
    ∃ p', Rel ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 ⟨⟨frame3_exit_pc, frame3_exit_a s.s (ramAt s) romFn, frame3_exit_x, frame3_exit_y s.s (ramAt s) romFn, frame3_exit_s s.s, p'⟩, frame3_exit_ram s.s (ramAt s) romFn, romFn, frame3_exit_cyc s.s (ramAt s) romFn s.cyc, frame3_exit_bad⟩ ∧ (p' &&& 4 == 0) = false := by
  have ht := toPlain_at_ctrl s hprg hpc
  obtain ⟨p', h, hf⟩ := frame3_exit_reach m s.a s.x s.y s.s s.p (ramAt s) romFn s.cyc rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode rom_boundingBoxCoreCode rom_ctrlJsrBgCode rom_ctrlAttrCode rom_bgPreCode rom_bgSizeCode rom_gbbAdrCode rom_headChkCode rom_doFootCheckCode rom_tileClassCode rom_adderCode rom_blockBufferCode rom_getBlockBufferAddrCode rom_chkFootCode rom_landPlyrCode rom_climbTilesCode rom_invisibleTilesCode rom_landCalleesCode rom_pipeTestCode rom_hrts rom_impedeCode rom_climbingCode hI hst hsize hx_go
  rw [← ht] at h
  exact ⟨p', nes_of_reach s hq _ _ _ h frame3_exit_no_bad, hf⟩

end Smb.Routine
