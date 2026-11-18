import Smb.Summary
import Smb.Routine.PlayerFrame
import Smb.Routine.MovementSwim

/-!
# The frame theorems while swimming (`$0704 ≠ 0`)

`frameKw_EXIT_call` and `frameKw_EXIT_reach`, K = 0, 1, as `PlayerFrame` with `ms0w`/`ms1w` in place of `ms0`/`ms1`.
-/
namespace Smb.Routine
set_option linter.unusedVariables false

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlA1w_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hprecode : CodeAt prg 0x30E9 ctrlPreCode) (hjcode0 : CodeAt prg 0x312B ctrlJsrCode)
    (hmidcode : CodeAt prg 0x312E ctrlMidCode) (hauxcode : CodeAt prg 0x314C ctrlAuxCode)
    (hmcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ((CPU.runTo (σ := Plain) stop (m + 2000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsPre : ∀ a : UInt16, (0xB0E9 ≤ a && a ≤ 0xB12B) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsMs : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsMid : ∀ a : UInt16, (0xB12E ≤ a && a ≤ 0xB14C) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAux : ∀ a : UInt16, (0xAF93 ≤ a && a ≤ 0xB049 || 0xB14C ≤ a && a ≤ 0xB15A ||
      0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have rg : prg 0x4046 = 0x60 := by
    have h := hgcode; simp only [CodeAt, imposeGravityCode, UInt16.reduceAdd] at h; simp [h]
  have ra : prg 0x336C = 0x60 := by
    have h := hmcode; simp only [CodeAt, movementSubsCode, UInt16.reduceAdd] at h; simp [h]
  have hj := hjcode0
  simp only [CodeAt, ctrlJsrCode, UInt16.reduceAdd] at hj
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 2000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ctrlA1w hrun [hj, rg, ra, hI, ctrlPre_ram_read, ctrlPre_writes, ctrlPre_s_eq, ctrlPre_bad_eq,
      ms1w_ram_read, ms1w_writes, ms1w_s_eq', ms1w_no_bad, ctrlMid_s_eq, ctrlMid_bad_eq, absIdx, dummyIdx, forceIdx, pageIdx,
      posIdx, speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx] until 45402
    calls [ctrlPre_call, ms1w_call, ctrlMid_call, ctrlAux_call]
    exact finish (clear hj rg ra; exact_finish ctrlA1w)
summary_interface ctrlA1w
summary_regs ctrlA1w


theorem ctrlA1w_s_eq' (sp : UInt8) : ctrlA1w_s sp = sp := by delta ctrlA1w_s ctrlAux_s ctrlMid_s; rfl

/-- The RAM and stack pointer at `PlayerBGCollision`, from state 1, swimming. -/
noncomputable abbrev frameR1w (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA1w_s sp) (ctrlA1w_ram sp ram prg)
noncomputable abbrev frameS1w (sp : UInt8) : UInt8 := ctrlJ_s (ctrlA1w_s sp)

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame1w_side_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0x9BDD ≤ a && a ≤ 0x9BF5 || 0xAF93 ≤ a && a ≤ 0xB049 ||
      0xB0E9 ≤ a && a ≤ 0xB178 || 0xB329 ≤ a && a ≤ 0xC046 || 0xDC64 ≤ a && a ≤ 0xDFB8 || 0xE29C ≤ a && a ≤ 0xE2DD ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hprecode : CodeAt prg 0x30E9 ctrlPreCode) (hjcode0 : CodeAt prg 0x312B ctrlJsrCode)
    (hmidcode : CodeAt prg 0x312E ctrlMidCode) (hauxcode : CodeAt prg 0x314C ctrlAuxCode)
    (hmcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hjbcode : CodeAt prg 0x315A ctrlJsrBgCode) (hattrcode : CodeAt prg 0x315D ctrlAttrCode)
    (hprecode2 : CodeAt prg 0x5C64 bgPreCode) (hszcode : CodeAt prg 0x5C98 bgSizeCode)
    (hgbcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode2 : CodeAt prg 0x5CBA headChkCode)
    (hfcode2 : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode2 : CodeAt prg 0x63AD adderCode)
    (hbcode2 : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode2 : CodeAt prg 0x5EC4 landCalleesCode) (hpcode2 : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
    (h1code : CodeAt prg 0x5D5E sideCheckCode) (h2code : CodeAt prg 0x5DFF stopPlayerMoveCode)
    (h3code : CodeAt prg 0x5EBD chkInvisibleCode) (h4code : CodeAt prg 0x5EDD chkJumpspringCode)
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1w sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR1w sp ram prg)) (bgSize_s (bgPre_s (frameS1w sp))) (bgRam (frameR1w sp ram prg)) prg = 0xDD5E)
    (hx_eb : bgFootRam (frameS1w sp) prg (frameR1w sp ram prg) 0xEB < 0x16)
    (hx_coin : noSideCoin prg (bgFootRam (frameS1w sp) prg (frameR1w sp ram prg)) = true)
    (hx_climb : noSideClimb prg (bgFootRam (frameS1w sp) prg (frameR1w sp ram prg)) = true)
    (hx_pipe : noSidePipeEntry prg (bgFootRam (frameS1w sp) prg (frameR1w sp ram prg)) = true) :
    ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsA : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsJ : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsB : ∀ a : UInt16, (0x9BDD ≤ a && a ≤ 0x9BF5 || a == 0xBCED || 0xDC64 ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAttr : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have r1 : prg 0x5D9B = 0x60 := by
    have h := h1code; simp only [CodeAt, sideCheckCode, UInt16.reduceAdd] at h; simp [h]
  have r2 : prg 0x5E02 = 0x60 := by
    have h := h2code; simp only [CodeAt, stopPlayerMoveCode, UInt16.reduceAdd] at h; simp [h]
  have hx_fs : bgSide_s (frameS1w sp) (frameR1w sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS1w sp) (frameR1w sp ram prg) prg hccode (Or.inl hx_foot)).1
    rw [h]; show ctrlJ_s (ctrlA1w_s sp) = sp + 254; delta ctrlJ_s ctrlA1w_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA1w_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA1w_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA1w_s ctrlAux_s ctrlMid_s; rfl
  have hfs' : footCheck_s (bgSize_y (bgPre_ram (frameR1w sp ram prg))) (bgSize_s (bgPre_s (frameS1w sp)))
      (bgSize_ram (bgPre_ram (frameR1w sp ram prg))) prg = sp + 254 := by
    have h := hx_fs; simp only [bgSide_s] at h; exact h
  have he0 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA1w_s sp).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he1 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA1w_s sp + 255).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he2 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA1w_s sp + 255).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  have he3 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA1w_s sp).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame1w_side hrun [r1, r2, hI, hx_fs, he0, he1, he2, he3, stackAt, bgSide_ram_read, bgSide_writes, ctrlJ_ram, bgSide_pc] until 45433
    calls [ctrlA1w_call, ctrlJ_call, bgSide_call, ctrlAttr_call]
    exact finish (clear r1 r2 he0 he1 he2 he3; exact_finish frame1w_side)
set_option maxRecDepth 20000 in
summary_interface frame1w_side
summary_reach frame1w_side 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame1w_impede_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0x9BDD ≤ a && a ≤ 0x9BF5 || 0xAF93 ≤ a && a ≤ 0xB049 ||
      0xB0E9 ≤ a && a ≤ 0xB178 || 0xB329 ≤ a && a ≤ 0xC046 || 0xDC64 ≤ a && a ≤ 0xDFB8 || 0xE29C ≤ a && a ≤ 0xE2DD ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hprecode : CodeAt prg 0x30E9 ctrlPreCode) (hjcode0 : CodeAt prg 0x312B ctrlJsrCode)
    (hmidcode : CodeAt prg 0x312E ctrlMidCode) (hauxcode : CodeAt prg 0x314C ctrlAuxCode)
    (hmcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hjbcode : CodeAt prg 0x315A ctrlJsrBgCode) (hattrcode : CodeAt prg 0x315D ctrlAttrCode)
    (hprecode2 : CodeAt prg 0x5C64 bgPreCode) (hszcode : CodeAt prg 0x5C98 bgSizeCode)
    (hgbcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode2 : CodeAt prg 0x5CBA headChkCode)
    (hfcode2 : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode2 : CodeAt prg 0x63AD adderCode)
    (hbcode2 : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode2 : CodeAt prg 0x5EC4 landCalleesCode) (hpcode2 : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1w sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR1w sp ram prg)) (bgY (frameR1w sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR1w sp ram prg)) (bgSize_s (bgPre_s (frameS1w sp))) (bgRam (frameR1w sp ram prg)) prg = 0xDF8A) :
    ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsA : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsJ : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsB : ∀ a : UInt16, (0x9BDD ≤ a && a ≤ 0x9BF5 || a == 0xBCED || 0xDC64 ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAttr : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have r1 : prg 0x5F8A = 0x60 := by
    have h := himcode; simp only [CodeAt, impedeCode, UInt16.reduceAdd] at h; simp [h]
  have hx_fs : bgImpede_s (frameS1w sp) (frameR1w sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS1w sp) (frameR1w sp ram prg) prg hccode (Or.inr hx_foot)).2
    rw [h]; show ctrlJ_s (ctrlA1w_s sp) = sp + 254; delta ctrlJ_s ctrlA1w_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA1w_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA1w_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA1w_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame1w_impede hrun [r1, hI, hx_fs, bgImpede_ram_read, bgImpede_writes, ctrlJ_ram] until 45433
    calls [ctrlA1w_call, ctrlJ_call, bgImpede_call, ctrlAttr_call]
    exact finish (clear r1; exact_finish frame1w_impede)
set_option maxRecDepth 20000 in
summary_interface frame1w_impede
summary_reach frame1w_impede 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame1w_exit_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0x9BDD ≤ a && a ≤ 0x9BF5 || 0xAF93 ≤ a && a ≤ 0xB049 ||
      0xB0E9 ≤ a && a ≤ 0xB178 || 0xB329 ≤ a && a ≤ 0xC046 || 0xDC64 ≤ a && a ≤ 0xDFB8 || 0xE29C ≤ a && a ≤ 0xE2DD ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hprecode : CodeAt prg 0x30E9 ctrlPreCode) (hjcode0 : CodeAt prg 0x312B ctrlJsrCode)
    (hmidcode : CodeAt prg 0x312E ctrlMidCode) (hauxcode : CodeAt prg 0x314C ctrlAuxCode)
    (hmcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hjbcode : CodeAt prg 0x315A ctrlJsrBgCode) (hattrcode : CodeAt prg 0x315D ctrlAttrCode)
    (hprecode2 : CodeAt prg 0x5C64 bgPreCode) (hszcode : CodeAt prg 0x5C98 bgSizeCode)
    (hgbcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode2 : CodeAt prg 0x5CBA headChkCode)
    (hfcode2 : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode2 : CodeAt prg 0x63AD adderCode)
    (hbcode2 : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode2 : CodeAt prg 0x5EC4 landCalleesCode) (hpcode2 : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1w sp ram prg) = 0xDC97) :
    ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsA : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsJ : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsB : ∀ a : UInt16, (0x9BDD ≤ a && a ≤ 0x9BF5 || a == 0xBCED || 0xDC64 ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAttr : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have r1 : prg 0x5C97 = 0x60 := by
    have h := hprecode2; simp only [CodeAt, bgPreCode, UInt16.reduceAdd] at h; simp [h]
  have hs0 := ctrlA1w_s_eq' sp
  have hs1 : bgPre_s (ctrlJ_s (ctrlA1w_s sp)) = sp + 254 := by
    delta bgPre_s ctrlJ_s ctrlA1w_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame1w_exit hrun [r1, hI, hs1, bgPre_ram_read, bgPre_writes, ctrlJ_ram] until 45433
    calls [ctrlA1w_call, ctrlJ_call, bgPre_exit_call, ctrlAttr_call]
    exact finish (clear r1 hs1; exact_finish frame1w_exit)
set_option maxRecDepth 20000 in
summary_interface frame1w_exit
summary_reach frame1w_exit 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlA0w_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hprecode : CodeAt prg 0x30E9 ctrlPreCode) (hjcode0 : CodeAt prg 0x312B ctrlJsrCode)
    (hmidcode : CodeAt prg 0x312E ctrlMidCode) (hauxcode : CodeAt prg 0x314C ctrlAuxCode)
    (hmcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ((CPU.runTo (σ := Plain) stop (m + 2000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsPre : ∀ a : UInt16, (0xB0E9 ≤ a && a ≤ 0xB12B) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsMs : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsMid : ∀ a : UInt16, (0xB12E ≤ a && a ≤ 0xB14C) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAux : ∀ a : UInt16, (0xAF93 ≤ a && a ≤ 0xB049 || 0xB14C ≤ a && a ≤ 0xB15A ||
      0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have rg : prg 0x4046 = 0x60 := by
    have h := hgcode; simp only [CodeAt, imposeGravityCode, UInt16.reduceAdd] at h; simp [h]
  have ra : prg 0x336C = 0x60 := by
    have h := hmcode; simp only [CodeAt, movementSubsCode, UInt16.reduceAdd] at h; simp [h]
  have hj := hjcode0
  simp only [CodeAt, ctrlJsrCode, UInt16.reduceAdd] at hj
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 2000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ctrlA0w hrun [hj, rg, ra, hI, ctrlPre_ram_read, ctrlPre_writes, ctrlPre_s_eq, ctrlPre_bad_eq,
      ms0w_ram_read, ms0w_writes, ms0w_s_eq', ms0w_no_bad, ctrlMid_s_eq, ctrlMid_bad_eq, absIdx, dummyIdx, forceIdx, pageIdx,
      posIdx, speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx] until 45402
    calls [ctrlPre_call, ms0w_call, ctrlMid_call, ctrlAux_call]
    exact finish (clear hj rg ra; exact_finish ctrlA0w)
summary_interface ctrlA0w
summary_regs ctrlA0w


theorem ctrlA0w_s_eq' (sp : UInt8) : ctrlA0w_s sp = sp := by delta ctrlA0w_s ctrlAux_s ctrlMid_s; rfl

/-- The RAM and stack pointer at `PlayerBGCollision`, from state 0, swimming. -/
noncomputable abbrev frameR0w (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA0w_s sp) (ctrlA0w_ram sp ram prg)
noncomputable abbrev frameS0w (sp : UInt8) : UInt8 := ctrlJ_s (ctrlA0w_s sp)

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame0w_side_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0x9BDD ≤ a && a ≤ 0x9BF5 || 0xAF93 ≤ a && a ≤ 0xB049 ||
      0xB0E9 ≤ a && a ≤ 0xB178 || 0xB329 ≤ a && a ≤ 0xC046 || 0xDC64 ≤ a && a ≤ 0xDFB8 || 0xE29C ≤ a && a ≤ 0xE2DD ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hprecode : CodeAt prg 0x30E9 ctrlPreCode) (hjcode0 : CodeAt prg 0x312B ctrlJsrCode)
    (hmidcode : CodeAt prg 0x312E ctrlMidCode) (hauxcode : CodeAt prg 0x314C ctrlAuxCode)
    (hmcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hjbcode : CodeAt prg 0x315A ctrlJsrBgCode) (hattrcode : CodeAt prg 0x315D ctrlAttrCode)
    (hprecode2 : CodeAt prg 0x5C64 bgPreCode) (hszcode : CodeAt prg 0x5C98 bgSizeCode)
    (hgbcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode2 : CodeAt prg 0x5CBA headChkCode)
    (hfcode2 : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode2 : CodeAt prg 0x63AD adderCode)
    (hbcode2 : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode2 : CodeAt prg 0x5EC4 landCalleesCode) (hpcode2 : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
    (h1code : CodeAt prg 0x5D5E sideCheckCode) (h2code : CodeAt prg 0x5DFF stopPlayerMoveCode)
    (h3code : CodeAt prg 0x5EBD chkInvisibleCode) (h4code : CodeAt prg 0x5EDD chkJumpspringCode)
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0w sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR0w sp ram prg)) (bgSize_s (bgPre_s (frameS0w sp))) (bgRam (frameR0w sp ram prg)) prg = 0xDD5E)
    (hx_eb : bgFootRam (frameS0w sp) prg (frameR0w sp ram prg) 0xEB < 0x16)
    (hx_coin : noSideCoin prg (bgFootRam (frameS0w sp) prg (frameR0w sp ram prg)) = true)
    (hx_climb : noSideClimb prg (bgFootRam (frameS0w sp) prg (frameR0w sp ram prg)) = true)
    (hx_pipe : noSidePipeEntry prg (bgFootRam (frameS0w sp) prg (frameR0w sp ram prg)) = true) :
    ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsA : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsJ : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsB : ∀ a : UInt16, (0x9BDD ≤ a && a ≤ 0x9BF5 || a == 0xBCED || 0xDC64 ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAttr : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have r1 : prg 0x5D9B = 0x60 := by
    have h := h1code; simp only [CodeAt, sideCheckCode, UInt16.reduceAdd] at h; simp [h]
  have r2 : prg 0x5E02 = 0x60 := by
    have h := h2code; simp only [CodeAt, stopPlayerMoveCode, UInt16.reduceAdd] at h; simp [h]
  have hx_fs : bgSide_s (frameS0w sp) (frameR0w sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS0w sp) (frameR0w sp ram prg) prg hccode (Or.inl hx_foot)).1
    rw [h]; show ctrlJ_s (ctrlA0w_s sp) = sp + 254; delta ctrlJ_s ctrlA0w_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA0w_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA0w_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA0w_s ctrlAux_s ctrlMid_s; rfl
  have hfs' : footCheck_s (bgSize_y (bgPre_ram (frameR0w sp ram prg))) (bgSize_s (bgPre_s (frameS0w sp)))
      (bgSize_ram (bgPre_ram (frameR0w sp ram prg))) prg = sp + 254 := by
    have h := hx_fs; simp only [bgSide_s] at h; exact h
  have he0 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA0w_s sp).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he1 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA0w_s sp + 255).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he2 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA0w_s sp + 255).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  have he3 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA0w_s sp).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame0w_side hrun [r1, r2, hI, hx_fs, he0, he1, he2, he3, stackAt, bgSide_ram_read, bgSide_writes, ctrlJ_ram, bgSide_pc] until 45433
    calls [ctrlA0w_call, ctrlJ_call, bgSide_call, ctrlAttr_call]
    exact finish (clear r1 r2 he0 he1 he2 he3; exact_finish frame0w_side)
set_option maxRecDepth 20000 in
summary_interface frame0w_side
summary_reach frame0w_side 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame0w_impede_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0x9BDD ≤ a && a ≤ 0x9BF5 || 0xAF93 ≤ a && a ≤ 0xB049 ||
      0xB0E9 ≤ a && a ≤ 0xB178 || 0xB329 ≤ a && a ≤ 0xC046 || 0xDC64 ≤ a && a ≤ 0xDFB8 || 0xE29C ≤ a && a ≤ 0xE2DD ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hprecode : CodeAt prg 0x30E9 ctrlPreCode) (hjcode0 : CodeAt prg 0x312B ctrlJsrCode)
    (hmidcode : CodeAt prg 0x312E ctrlMidCode) (hauxcode : CodeAt prg 0x314C ctrlAuxCode)
    (hmcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hjbcode : CodeAt prg 0x315A ctrlJsrBgCode) (hattrcode : CodeAt prg 0x315D ctrlAttrCode)
    (hprecode2 : CodeAt prg 0x5C64 bgPreCode) (hszcode : CodeAt prg 0x5C98 bgSizeCode)
    (hgbcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode2 : CodeAt prg 0x5CBA headChkCode)
    (hfcode2 : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode2 : CodeAt prg 0x63AD adderCode)
    (hbcode2 : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode2 : CodeAt prg 0x5EC4 landCalleesCode) (hpcode2 : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0w sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR0w sp ram prg)) (bgY (frameR0w sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR0w sp ram prg)) (bgSize_s (bgPre_s (frameS0w sp))) (bgRam (frameR0w sp ram prg)) prg = 0xDF8A) :
    ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsA : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsJ : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsB : ∀ a : UInt16, (0x9BDD ≤ a && a ≤ 0x9BF5 || a == 0xBCED || 0xDC64 ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAttr : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have r1 : prg 0x5F8A = 0x60 := by
    have h := himcode; simp only [CodeAt, impedeCode, UInt16.reduceAdd] at h; simp [h]
  have hx_fs : bgImpede_s (frameS0w sp) (frameR0w sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS0w sp) (frameR0w sp ram prg) prg hccode (Or.inr hx_foot)).2
    rw [h]; show ctrlJ_s (ctrlA0w_s sp) = sp + 254; delta ctrlJ_s ctrlA0w_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA0w_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA0w_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA0w_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame0w_impede hrun [r1, hI, hx_fs, bgImpede_ram_read, bgImpede_writes, ctrlJ_ram] until 45433
    calls [ctrlA0w_call, ctrlJ_call, bgImpede_call, ctrlAttr_call]
    exact finish (clear r1; exact_finish frame0w_impede)
set_option maxRecDepth 20000 in
summary_interface frame0w_impede
summary_reach frame0w_impede 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame0w_exit_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0x9BDD ≤ a && a ≤ 0x9BF5 || 0xAF93 ≤ a && a ≤ 0xB049 ||
      0xB0E9 ≤ a && a ≤ 0xB178 || 0xB329 ≤ a && a ≤ 0xC046 || 0xDC64 ≤ a && a ≤ 0xDFB8 || 0xE29C ≤ a && a ≤ 0xE2DD ||
      0xE3B0 ≤ a && a ≤ 0xE431 || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hprecode : CodeAt prg 0x30E9 ctrlPreCode) (hjcode0 : CodeAt prg 0x312B ctrlJsrCode)
    (hmidcode : CodeAt prg 0x312E ctrlMidCode) (hauxcode : CodeAt prg 0x314C ctrlAuxCode)
    (hmcode : CodeAt prg 0x3329 movementSubsCode) (hecode : CodeAt prg 0x0E04 jumpEngineCode)
    (hpcode : CodeAt prg 0x3424 physicsCode) (hjcode : CodeAt prg 0x3424 jumpStartCode)
    (hacode : CodeAt prg 0x358C animSpeedCode) (hfcode : CodeAt prg 0x35CC imposeFrictionCode)
    (hhcode : CodeAt prg 0x3F09 movePlayerHorizontallyCode)
    (hvcode : CodeAt prg 0x3F4D movePlayerVerticallyCode) (hgcode : CodeAt prg 0x3FD7 imposeGravityCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hjbcode : CodeAt prg 0x315A ctrlJsrBgCode) (hattrcode : CodeAt prg 0x315D ctrlAttrCode)
    (hprecode2 : CodeAt prg 0x5C64 bgPreCode) (hszcode : CodeAt prg 0x5C98 bgSizeCode)
    (hgbcode : CodeAt prg 0x5CAB gbbAdrCode) (hhcode2 : CodeAt prg 0x5CBA headChkCode)
    (hfcode2 : CodeAt prg 0x5CF6 doFootCheckCode)
    (htcode : CodeAt prg 0x5F8B tileClassCode) (hacode2 : CodeAt prg 0x63AD adderCode)
    (hbcode2 : CodeAt prg 0x63B0 blockBufferCode) (hbacode : CodeAt prg 0x1BDD getBlockBufferAddrCode)
    (hcode : CodeAt prg 0x5D1D chkFootCode) (hlcode : CodeAt prg 0x5D44 landPlyrCode)
    (hccode : CodeAt prg 0x5F96 climbTilesCode) (hicode : CodeAt prg 0x5EBD invisibleTilesCode)
    (hjcode2 : CodeAt prg 0x5EC4 landCalleesCode) (hpcode2 : CodeAt prg 0x5EEE pipeTestCode)
    (hrts : prg 0x5F4A = 0x60) (himcode : CodeAt prg 0x5F4B impedeCode)
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : (ram 0x704 == 0) = false)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0w sp ram prg) = 0xDC97) :
    ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsA : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsJ : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsB : ∀ a : UInt16, (0x9BDD ≤ a && a ≤ 0x9BF5 || a == 0xBCED || 0xDC64 ≤ a && a ≤ 0xDFB8 ||
      0xE3B0 ≤ a && a ≤ 0xE431) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAttr : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have r1 : prg 0x5C97 = 0x60 := by
    have h := hprecode2; simp only [CodeAt, bgPreCode, UInt16.reduceAdd] at h; simp [h]
  have hs0 := ctrlA0w_s_eq' sp
  have hs1 : bgPre_s (ctrlJ_s (ctrlA0w_s sp)) = sp + 254 := by
    delta bgPre_s ctrlJ_s ctrlA0w_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame0w_exit hrun [r1, hI, hs1, bgPre_ram_read, bgPre_writes, ctrlJ_ram] until 45433
    calls [ctrlA0w_call, ctrlJ_call, bgPre_exit_call, ctrlAttr_call]
    exact finish (clear r1 hs1; exact_finish frame0w_exit)
set_option maxRecDepth 20000 in
summary_interface frame0w_exit
summary_reach frame0w_exit 0xB179

end Smb.Routine
