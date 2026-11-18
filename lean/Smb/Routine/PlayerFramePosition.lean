import Smb.Routine.PlayerFrame
import Smb.Routine.BackgroundVertical
import Smb.Routine.FloorClip

/-!
# The falling player routine: movement followed by background collision

Under the existing state-2 execution premises, the bounded run from $B0E9 to $B179
ends at the old-velocity movement position, or at that position with the Y pixel
byte snapped to a tile row. Its final packed position is therefore no greater than
that moved position. The position subpixel survives a row snap.

Small byte contracts align controller preprocessing, movement, background collision
and the final attribute update. No whole-frame RAM expression is flattened and no
instruction sequence is executed again in these proofs.

This stops before PlayerHole and the enemy loop, and is a Plain-machine result.
It retains the original coin/axe/block-hit/pipe/climbing and route exclusions.
The unsigned position comparison is against the moved position, not the input
position across wraparound. It is not a global no-floor-clip theorem.
-/
namespace Smb.Routine.PlayerFramePosition
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Bytes needed to align the actual movement input and its vertical outputs. -/
def verticalByte (i : UInt16) : Bool :=
  i == 0x9F || i == 0x433 || i == 0x416 || i == 0xCE || i == 0xB5 ||
  i == 0x709 || i == 0x70A || i == 0x1D || i == 0x704 || i == 0x70B || i == 0x70E || i == 0x0E

/-- RAM at PlayerMovementSubs after controller preprocessing and the real JSR. -/
noncomputable def moveIn (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF then 0x2D
  else bif i == (0x100 ||| sp.toUInt16) &&& 0x7FF then 0xB1
  else ctrlPre_ram ram i

noncomputable def moveOut (sp : UInt8) (ram : UInt16 → UInt8) : UInt16 → UInt8 :=
  ms2_ram (sp + 254) (moveIn sp ram)

/-- Open only the short composition definition; constituent summaries stay opaque. -/
theorem ctrlA2_composition (sp : UInt8) (ram prg : UInt16 → UInt8) :
    ctrlA2_ram sp ram prg = ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (moveOut sp ram)) prg := by
  unfold ctrlA2_ram moveOut moveIn
  simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]

theorem moveIn_at (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16)
    (hi : verticalByte i = true) : moveIn sp ram i = ram i := by
  have hp : ctrlPre_ram ram i = ram i := by
    apply ctrlPre_ram_frame
    simp only [verticalByte] at hi
    simp only [ctrlPre_writes]
    bv_decide
  simp only [moveIn, hp]
  simp only [verticalByte] at hi
  bv_decide

/-- The post-movement control/auxiliary code does not alter these bytes, for any S. -/
theorem ctrlA2_at (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (hi : verticalByte i = true) : ctrlA2_ram sp ram prg i = moveOut sp ram i := by
  rw [ctrlA2_composition]
  have ha : ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (moveOut sp ram)) prg i =
      ctrlMid_ram (moveOut sp ram) i := by
    apply ctrlAux_ram_frame
    sym_exec [verticalByte] at hi
    sym_exec [ctrlAux_writes, absIdx]
    bv_decide
  rw [ha]
  apply ctrlMid_ram_frame
  simp only [verticalByte] at hi
  simp only [ctrlMid_writes]
  bv_decide

/-- Conditional old-velocity position transport; the only missing hypothesis is
    the position projection of the exact ms2 leaf, at its actual input RAM. -/
theorem ctrlA2_position_of_move (sp : UInt8) (ram prg : UInt16 → UInt8)
    (hm : ypos24 (moveOut sp ram) 0 = nextPos (ypos24 (moveIn sp ram) 0) (yvel16 (moveIn sp ram) 0)) :
    ypos24 (ctrlA2_ram sp ram prg) 0 = nextPos (ypos24 ram 0) (yvel16 ram 0) := by
  have hprepos : ypos24 (moveIn sp ram) 0 = ypos24 ram 0 := by
    sym_exec [ypos24, dummyIdx, yPosIdx, yHighIdx]
    rw [moveIn_at sp ram 0xB5 (by decide), moveIn_at sp ram 0xCE (by decide),
      moveIn_at sp ram 0x416 (by decide)]
  have hprevel : yvel16 (moveIn sp ram) 0 = yvel16 ram 0 := by
    sym_exec [yvel16, ySpeedIdx, yForceIdx]
    rw [moveIn_at sp ram 0x9F (by decide), moveIn_at sp ram 0x433 (by decide)]
  have hpost : ypos24 (ctrlA2_ram sp ram prg) 0 = ypos24 (moveOut sp ram) 0 := by
    sym_exec [ypos24, dummyIdx, yPosIdx, yHighIdx]
    rw [ctrlA2_at sp ram prg 0xB5 (by decide), ctrlA2_at sp ram prg 0xCE (by decide),
      ctrlA2_at sp ram prg 0x416 (by decide)]
  rw [hpost, hm, hprepos, hprevel]

/-- Open only the three position-byte reads of the existing ms2 leaf summary.
    No CPU interpreter, other end-state fields, or surrounding frame is unfolded. -/
theorem ms2_position (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ypos24 (ms2_ram sp ram) 0 = nextPos (ypos24 ram 0) (yvel16 ram 0) := by
  sym_exec [ypos24, dummyIdx, yPosIdx, yHighIdx]
  sym_exec [ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6,
    startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityRam,
    yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, bne] at *
  fun_congr
  bv_decide (config := { enums := false })

/-- Position at the end of actual ctrlA2's returned RAM: old position plus old
    velocity. The source call theorem retains its original code/I/speed premises. -/
theorem ctrlA2_position (sp : UInt8) (ram prg : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ypos24 (ctrlA2_ram sp ram prg) 0 = nextPos (ypos24 ram 0) (yvel16 ram 0) := by
  apply ctrlA2_position_of_move
  unfold moveOut
  apply ms2_position
  · rw [moveIn_at sp ram 0x1D (by decide)]; exact ht
  · rw [moveIn_at sp ram 0x704 (by decide)]; exact hs
  · rw [moveIn_at sp ram 0x70B (by decide)]; exact hz
  · rw [moveIn_at sp ram 0x70E (by decide)]; exact hjs



/-- Snap only the low nibble of the pixel Y byte. The position subpixel is kept. -/
def rowSnap (p : UInt32) : UInt32 := p &&& 0xFFF0FF

/-- Compose the small BG byte facts without opening any BG/full-frame summary. -/
theorem bg_position_shape (moved final : UInt16 → UInt8)
    (hhigh : final 0xB5 = moved 0xB5) (hsub : final 0x416 = moved 0x416)
    (hlow : final 0xCE = moved 0xCE ∨ final 0xCE = moved 0xCE &&& 0xF0) :
    (ypos24 final 0 = ypos24 moved 0 ∨ ypos24 final 0 = rowSnap (ypos24 moved 0)) ∧
    ypos24 final 0 ≤ ypos24 moved 0 := by
  sym_exec [ypos24, yHighIdx, yPosIdx, dummyIdx, rowSnap] at *
  rcases hlow with h | h <;> bv_decide

/-- A returned summary-state property, not a bounded runTo-at-endpoint theorem.
    hmove must be the old-velocity movement relation at the actual aligned RAM. -/
theorem final_position_from_movement (initial moved final : UInt16 → UInt8)
    (hmove : ypos24 moved 0 = nextPos (ypos24 initial 0) (yvel16 initial 0))
    (hhigh : final 0xB5 = moved 0xB5) (hsub : final 0x416 = moved 0x416)
    (hlow : final 0xCE = moved 0xCE ∨ final 0xCE = moved 0xCE &&& 0xF0) :
    let movedPos := nextPos (ypos24 initial 0) (yvel16 initial 0)
    (ypos24 final 0 = movedPos ∨ ypos24 final 0 = rowSnap movedPos) ∧
    ypos24 final 0 ≤ movedPos := by
  have h := bg_position_shape moved final hhigh hsub hlow
  rw [hmove] at h
  exact h


/-- Named BG-entry RAM is aligned to the input's old-velocity movement result. -/
theorem frameR2_position (sp : UInt8) (ram prg : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ypos24 (frameR2 sp ram prg) 0 = nextPos (ypos24 ram 0) (yvel16 ram 0) := by
  have hJ : ypos24 (frameR2 sp ram prg) 0 = ypos24 (ctrlA2_ram sp ram prg) 0 := by
    sym_exec [frameR2, ctrlJ_ram, ypos24, dummyIdx, yPosIdx, yHighIdx]
  rw [hJ]
  exact ctrlA2_position sp ram prg ht hs hz hjs

theorem attr_position (ram : UInt16 → UInt8) : ypos24 (ctrlAttr_ram ram) 0 = ypos24 ram 0 := by
  sym_exec [ctrlAttr_ram, ypos24, dummyIdx, yPosIdx, yHighIdx]

/-- Returned summary RAM property, consuming the checked BG Y-snap fact.
    All actual frame2_side_call execution/exclusion premises remain necessary. -/
theorem frame2_side_position (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    let g := nextPos (ypos24 ram 0) (yvel16 ram 0)
    (ypos24 (frame2_side_ram w sp ram prg) 0 = g ∨
      ypos24 (frame2_side_ram w sp ram prg) 0 = rowSnap g) ∧
    ypos24 (frame2_side_ram w sp ram prg) 0 ≤ g := by
  have hy := BackgroundVertical.side_y w (frameS2 sp) (frameR2 sp ram prg) prg
  have hh : bgSide_ram w (frameS2 sp) (frameR2 sp ram prg) prg 0xB5 = frameR2 sp ram prg 0xB5 := by
    apply bgSide_ram_frame
    simp only [bgSide_writes, stackAt]
    bv_decide
  have hq : bgSide_ram w (frameS2 sp) (frameR2 sp ram prg) prg 0x416 = frameR2 sp ram prg 0x416 := by
    apply bgSide_ram_frame
    simp only [bgSide_writes, stackAt]
    bv_decide
  have h := final_position_from_movement ram (frameR2 sp ram prg)
    (bgSide_ram w (frameS2 sp) (frameR2 sp ram prg) prg)
    (frameR2_position sp ram prg ht hs hz hjs) hh hq hy
  have hf : ypos24 (frame2_side_ram w sp ram prg) 0 =
      ypos24 (bgSide_ram w (frameS2 sp) (frameR2 sp ram prg) prg) 0 := by
    unfold frame2_side_ram
    exact attr_position _
  simpa only [hf] using h

/-- Same consumer for the normal foot-impede exit; no stronger stack bound. -/
theorem frame2_impede_position (sp : UInt8) (ram prg : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    let g := nextPos (ypos24 ram 0) (yvel16 ram 0)
    (ypos24 (frame2_impede_ram sp ram prg) 0 = g ∨
      ypos24 (frame2_impede_ram sp ram prg) 0 = rowSnap g) ∧
    ypos24 (frame2_impede_ram sp ram prg) 0 ≤ g := by
  have hy := BackgroundVertical.impede_y (frameS2 sp) (frameR2 sp ram prg) prg
  have hh : bgImpede_ram (frameS2 sp) (frameR2 sp ram prg) prg 0xB5 = frameR2 sp ram prg 0xB5 := by
    apply bgImpede_ram_frame
    simp only [bgImpede_writes]
    bv_decide
  have hq : bgImpede_ram (frameS2 sp) (frameR2 sp ram prg) prg 0x416 = frameR2 sp ram prg 0x416 := by
    apply bgImpede_ram_frame
    simp only [bgImpede_writes]
    bv_decide
  have h := final_position_from_movement ram (frameR2 sp ram prg)
    (bgImpede_ram (frameS2 sp) (frameR2 sp ram prg) prg)
    (frameR2_position sp ram prg ht hs hz hjs) hh hq hy
  have hf : ypos24 (frame2_impede_ram sp ram prg) 0 =
      ypos24 (bgImpede_ram (frameS2 sp) (frameR2 sp ram prg) prg) 0 := by
    unfold frame2_impede_ram
    exact attr_position _
  simpa only [hf] using h

/-- The early-exit returned RAM needs no outstanding snap fact: it keeps Y. -/
theorem frame2_exit_position (sp : UInt8) (ram prg : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ypos24 (frame2_exit_ram sp ram prg) 0 = nextPos (ypos24 ram 0) (yvel16 ram 0) := by
  have hb (i : UInt16) (hi : i = 0xB5 ∨ i = 0xCE ∨ i = 0x416) :
      bgPre_ram (frameR2 sp ram prg) i = frameR2 sp ram prg i := by
    apply bgPre_ram_frame
    simp only [bgPre_writes]
    bv_decide
  have hp : ypos24 (bgPre_ram (frameR2 sp ram prg)) 0 = ypos24 (frameR2 sp ram prg) 0 := by
    sym_exec [ypos24, yHighIdx, yPosIdx, dummyIdx]
    rw [hb 0xB5 (by simp), hb 0xCE (by simp), hb 0x416 (by simp)]
  have hf : ypos24 (frame2_exit_ram sp ram prg) 0 = ypos24 (bgPre_ram (frameR2 sp ram prg)) 0 := by
    unfold frame2_exit_ram
    exact attr_position _
  rw [hf, hp]
  exact frameR2_position sp ram prg ht hs hz hjs
/-- Direct bounded endpoint property using the newly checked reach wrapper. -/
theorem frame2_side_y_reach
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
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 2) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR2 sp ram prg)) (bgSize_s (bgPre_s (frameS2 sp))) (bgRam (frameR2 sp ram prg)) prg = 0xDD5E)
    (hx_eb : bgFootRam (frameS2 sp) prg (frameR2 sp ram prg) 0xEB < 0x16)
    (hx_coin : noSideCoin prg (bgFootRam (frameS2 sp) prg (frameR2 sp ram prg)) = true)
    (hx_climb : noSideClimb prg (bgFootRam (frameS2 sp) prg (frameR2 sp ram prg)) = true)
    (hx_pipe : noSidePipeEntry prg (bgFootRam (frameS2 sp) prg (frameR2 sp ram prg)) = true) :
    let out := ((CPU.runTo (σ := Plain) 0xB179 (m + 3000)).run
      ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    let g := nextPos (ypos24 ram 0) (yvel16 ram 0)
    (ypos24 out.ram 0 = g ∨ ypos24 out.ram 0 = rowSnap g) ∧ ypos24 out.ram 0 ≤ g := by
  obtain ⟨p', a', x', y', c', w, hr, hp'⟩ := Smb.Routine.frame2_side_reach m a x y sp p ram prg cyc
    hprecode hjcode0 hmidcode hauxcode hmcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hscode htab hgxcode hdcode hocode hsetcode hytab hycode hrcode hwcode hobjcode hbcode hjbcode hattrcode hprecode2 hszcode hgbcode hhcode2 hfcode2 htcode hacode2 hbcode2 hbacode hcode hlcode hccode hicode hjcode2 hpcode2 hrts himcode h1code h2code h3code h4code hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  dsimp only
  rw [hr]
  exact frame2_side_position w sp ram prg hst hswim hsize hjs


/-- Direct bounded endpoint property using the newly checked reach wrapper. -/
theorem frame2_impede_y_reach
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
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 2) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR2 sp ram prg)) (bgSize_s (bgPre_s (frameS2 sp))) (bgRam (frameR2 sp ram prg)) prg = 0xDF8A) :
    let out := ((CPU.runTo (σ := Plain) 0xB179 (m + 3000)).run
      ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    let g := nextPos (ypos24 ram 0) (yvel16 ram 0)
    (ypos24 out.ram 0 = g ∨ ypos24 out.ram 0 = rowSnap g) ∧ ypos24 out.ram 0 ≤ g := by
  obtain ⟨p', c', hr, hp'⟩ := Smb.Routine.frame2_impede_reach m a x y sp p ram prg cyc
    hprecode hjcode0 hmidcode hauxcode hmcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hscode htab hgxcode hdcode hocode hsetcode hytab hycode hrcode hwcode hobjcode hbcode hjbcode hattrcode hprecode2 hszcode hgbcode hhcode2 hfcode2 htcode hacode2 hbcode2 hbacode hcode hlcode hccode hicode hjcode2 hpcode2 hrts himcode hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  dsimp only
  rw [hr]
  exact frame2_impede_position sp ram prg hst hswim hsize hjs


/-- Direct bounded endpoint property using the newly checked reach wrapper. -/
theorem frame2_exit_y_reach
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
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 2) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 sp ram prg) = 0xDC97) :
    let out := ((CPU.runTo (σ := Plain) 0xB179 (m + 3000)).run
      ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2
    ypos24 out.ram 0 = nextPos (ypos24 ram 0) (yvel16 ram 0) := by
  obtain ⟨p', c', hr, hp'⟩ := Smb.Routine.frame2_exit_reach m a x y sp p ram prg cyc
    hprecode hjcode0 hmidcode hauxcode hmcode hecode hpcode hjcode hacode hfcode hhcode hvcode hgcode hscode htab hgxcode hdcode hocode hsetcode hytab hycode hrcode hwcode hobjcode hbcode hjbcode hattrcode hprecode2 hszcode hgbcode hhcode2 hfcode2 htcode hacode2 hbcode2 hbacode hcode hlcode hccode hicode hjcode2 hpcode2 hrts himcode hI hst hsize hswim hjs hspd hx_go
  dsimp only
  rw [hr]
  exact frame2_exit_position sp ram prg hst hswim hsize hjs

end Smb.Routine.PlayerFramePosition
