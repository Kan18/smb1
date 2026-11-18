import Smb.Data.ProofRom
import Smb.Summary
import Smb.Routine.PlayerCtrlA
import Smb.Routine.PlayerBG

/-!
# A frame of Mario's control and collision, from the machine code

`frameK_EXIT_call`: `PlayerCtrlRoutine` from its entry `$B0E9` to `PlayerHole` `$B179`, with Mario in state `K` (0 on the
ground, 1 jumping, 2 falling, 3 climbing) and `PlayerBGCollision` leaving by `EXIT`: `side` (through the side checks), `impede` (a foot
in a wall, `ImpedePlayerMove`) or `exit` (its early exit). Each is one call theorem whose end state is a
composition of named summaries, so that a property of the frame reads one byte through them.

The conditions are hypotheses on the state where the code reads them:
- movement (`ms*_call`): `Player_State = K`, not changing size (`$070B = 0`); except when climbing, also not swimming
  (`$0704 = 0`), no jumpspring (`$070E = 0`), downward speed byte below `$40`;
- `hgo`/`hx_foot`: which way `PlayerBGCollision` goes;
- `hx_hc`…`hx_pe`, `hx_coin`…: no coin, axe, climbable metatile, block hit, or pipe entry, the routes these theorems exclude;
- `hx_eb`: `$EB < $16`, on the RAM after the foot check.

The stack pointer needs no condition: the foot check restores it on both exits used here (`background_stack_normal`;
only the pipe-entry stop `$DEFA` keeps a pushed return address).

The flags, the cycle count and, where a callee leaves them open, `A`, `X`, `Y` and the side check's scratch bytes (`w`) are
existential. `w` covers only those scratch bytes: the theorem does not carry the callee's other facts about it.
`frameK_EXIT_reach` says the same directly: running to `$B179` gives exactly the end state. `ctrlHole_call` is what follows, from `$B179`.
-/

namespace Smb.Routine
set_option linter.unusedVariables false

/-- `$B15A`: `jsr PlayerBGCollision`. -/
def ctrlJsrBgCode : List UInt8 := smbPrg% 0xB15A 3
/-- `$B15D`–`$B178`: `Player_SprAttrib`'s background priority, after the collisions. -/
def ctrlAttrCode : List UInt8 := smbPrg% 0xB15D 28
/-- `$B179`–`$B1C6`: `PlayerHole`, below the screen. -/
def ctrlHoleCode : List UInt8 := smbPrg% 0xB179 78
/-- `$B1DD`–`$B1E4`: `SetEntr`. -/
def setEntrCode : List UInt8 := smbPrg% 0xB1DD 8
/-- `$B213`–`$B21E`: `ChgAreaMode`. -/
def chgAreaModeCode : List UInt8 := smbPrg% 0xB213 12

set_option maxHeartbeats 8000000 in
sym_theorem ctrlJ_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x315A ctrlJsrBgCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 4)).run ⟨⟨0xB15A, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, ctrlJsrBgCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 4)).run ⟨⟨0xB15A, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary ctrlJ hrun [hcode, hI] until 56420 exact finish (clear hcode; exact_finish ctrlJ)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlAttr_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x315D ctrlAttrCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xB15D, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, ctrlAttrCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xB15D, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary ctrlAttr hrun [hcode, hI] until 45433 exact finish (clear hcode; exact_finish ctrlAttr)
summary_regs ctrlAttr

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlHole_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xB179 ≤ a && a ≤ 0xB1C6 || 0xB1DD ≤ a && a ≤ 0xB1E4 || 0xB213 ≤ a && a ≤ 0xB21E) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x3179 ctrlHoleCode) (h1code : CodeAt prg 0x31DD setEntrCode) (h2code : CodeAt prg 0x3213 chgAreaModeCode)
    (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xB179, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, ctrlHoleCode, UInt16.reduceAdd] at hcode
  simp only [CodeAt, setEntrCode, UInt16.reduceAdd] at h1code
  simp only [CodeAt, chgAreaModeCode, UInt16.reduceAdd] at h2code
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 60)).run ⟨⟨0xB179, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary ctrlHole hrun [hcode, h1code, h2code, hI] until [45498, 45510]
    exact finish (clear hcode h1code h2code; exact_finish ctrlHole)
summary_regs ctrlHole


theorem ctrlA0_s_eq' (sp : UInt8) : ctrlA0_s sp = sp := by delta ctrlA0_s ctrlAux_s ctrlMid_s; rfl

/-- The RAM and stack pointer at `PlayerBGCollision`, from state 0. -/
noncomputable abbrev frameR0 (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA0_s sp) (ctrlA0_ram sp ram prg)
noncomputable abbrev frameS0 (sp : UInt8) : UInt8 := ctrlJ_s (ctrlA0_s sp)

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame0_side_call (stop : UInt16)
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
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR0 sp ram prg)) (bgSize_s (bgPre_s (frameS0 sp))) (bgRam (frameR0 sp ram prg)) prg = 0xDD5E)
    (hx_eb : bgFootRam (frameS0 sp) prg (frameR0 sp ram prg) 0xEB < 0x16)
    (hx_coin : noSideCoin prg (bgFootRam (frameS0 sp) prg (frameR0 sp ram prg)) = true)
    (hx_climb : noSideClimb prg (bgFootRam (frameS0 sp) prg (frameR0 sp ram prg)) = true)
    (hx_pipe : noSidePipeEntry prg (bgFootRam (frameS0 sp) prg (frameR0 sp ram prg)) = true) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hx_fs : bgSide_s (frameS0 sp) (frameR0 sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS0 sp) (frameR0 sp ram prg) prg hccode (Or.inl hx_foot)).1
    rw [h]; show ctrlJ_s (ctrlA0_s sp) = sp + 254; delta ctrlJ_s ctrlA0_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA0_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA0_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA0_s ctrlAux_s ctrlMid_s; rfl
  have hfs' : footCheck_s (bgSize_y (bgPre_ram (frameR0 sp ram prg))) (bgSize_s (bgPre_s (frameS0 sp)))
      (bgSize_ram (bgPre_ram (frameR0 sp ram prg))) prg = sp + 254 := by
    have h := hx_fs; simp only [bgSide_s] at h; exact h
  have he0 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA0_s sp).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he1 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA0_s sp + 255).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he2 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA0_s sp + 255).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  have he3 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA0_s sp).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame0_side hrun [r1, r2, hI, hx_fs, he0, he1, he2, he3, stackAt, bgSide_ram_read, bgSide_writes, ctrlJ_ram, bgSide_pc] until 45433
    calls [ctrlA0_call, ctrlJ_call, bgSide_call, ctrlAttr_call]
    exact finish (clear r1 r2 he0 he1 he2 he3; exact_finish frame0_side)
set_option maxRecDepth 20000 in
summary_interface frame0_side
summary_reach frame0_side 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame0_impede_call (stop : UInt16)
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
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR0 sp ram prg)) (bgSize_s (bgPre_s (frameS0 sp))) (bgRam (frameR0 sp ram prg)) prg = 0xDF8A) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hx_fs : bgImpede_s (frameS0 sp) (frameR0 sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS0 sp) (frameR0 sp ram prg) prg hccode (Or.inr hx_foot)).2
    rw [h]; show ctrlJ_s (ctrlA0_s sp) = sp + 254; delta ctrlJ_s ctrlA0_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA0_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA0_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA0_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame0_impede hrun [r1, hI, hx_fs, bgImpede_ram_read, bgImpede_writes, ctrlJ_ram] until 45433
    calls [ctrlA0_call, ctrlJ_call, bgImpede_call, ctrlAttr_call]
    exact finish (clear r1; exact_finish frame0_impede)
set_option maxRecDepth 20000 in
summary_interface frame0_impede
summary_reach frame0_impede 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame0_exit_call (stop : UInt16)
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
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 sp ram prg) = 0xDC97) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hs0 := ctrlA0_s_eq' sp
  have hs1 : bgPre_s (ctrlJ_s (ctrlA0_s sp)) = sp + 254 := by
    delta bgPre_s ctrlJ_s ctrlA0_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame0_exit hrun [r1, hI, hs1, bgPre_ram_read, bgPre_writes, ctrlJ_ram] until 45433
    calls [ctrlA0_call, ctrlJ_call, bgPre_exit_call, ctrlAttr_call]
    exact finish (clear r1 hs1; exact_finish frame0_exit)
set_option maxRecDepth 20000 in
summary_interface frame0_exit
summary_reach frame0_exit 0xB179

theorem ctrlA1_s_eq' (sp : UInt8) : ctrlA1_s sp = sp := by delta ctrlA1_s ctrlAux_s ctrlMid_s; rfl

/-- The RAM and stack pointer at `PlayerBGCollision`, from state 1. -/
noncomputable abbrev frameR1 (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA1_s sp) (ctrlA1_ram sp ram prg)
noncomputable abbrev frameS1 (sp : UInt8) : UInt8 := ctrlJ_s (ctrlA1_s sp)

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame1_side_call (stop : UInt16)
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
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR1 sp ram prg)) (bgSize_s (bgPre_s (frameS1 sp))) (bgRam (frameR1 sp ram prg)) prg = 0xDD5E)
    (hx_eb : bgFootRam (frameS1 sp) prg (frameR1 sp ram prg) 0xEB < 0x16)
    (hx_coin : noSideCoin prg (bgFootRam (frameS1 sp) prg (frameR1 sp ram prg)) = true)
    (hx_climb : noSideClimb prg (bgFootRam (frameS1 sp) prg (frameR1 sp ram prg)) = true)
    (hx_pipe : noSidePipeEntry prg (bgFootRam (frameS1 sp) prg (frameR1 sp ram prg)) = true) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hx_fs : bgSide_s (frameS1 sp) (frameR1 sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS1 sp) (frameR1 sp ram prg) prg hccode (Or.inl hx_foot)).1
    rw [h]; show ctrlJ_s (ctrlA1_s sp) = sp + 254; delta ctrlJ_s ctrlA1_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA1_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA1_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA1_s ctrlAux_s ctrlMid_s; rfl
  have hfs' : footCheck_s (bgSize_y (bgPre_ram (frameR1 sp ram prg))) (bgSize_s (bgPre_s (frameS1 sp)))
      (bgSize_ram (bgPre_ram (frameR1 sp ram prg))) prg = sp + 254 := by
    have h := hx_fs; simp only [bgSide_s] at h; exact h
  have he0 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA1_s sp).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he1 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA1_s sp + 255).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he2 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA1_s sp + 255).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  have he3 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA1_s sp).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame1_side hrun [r1, r2, hI, hx_fs, he0, he1, he2, he3, stackAt, bgSide_ram_read, bgSide_writes, ctrlJ_ram, bgSide_pc] until 45433
    calls [ctrlA1_call, ctrlJ_call, bgSide_call, ctrlAttr_call]
    exact finish (clear r1 r2 he0 he1 he2 he3; exact_finish frame1_side)
set_option maxRecDepth 20000 in
summary_interface frame1_side
summary_reach frame1_side 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame1_impede_call (stop : UInt16)
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
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR1 sp ram prg)) (bgSize_s (bgPre_s (frameS1 sp))) (bgRam (frameR1 sp ram prg)) prg = 0xDF8A) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hx_fs : bgImpede_s (frameS1 sp) (frameR1 sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS1 sp) (frameR1 sp ram prg) prg hccode (Or.inr hx_foot)).2
    rw [h]; show ctrlJ_s (ctrlA1_s sp) = sp + 254; delta ctrlJ_s ctrlA1_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA1_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA1_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA1_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame1_impede hrun [r1, hI, hx_fs, bgImpede_ram_read, bgImpede_writes, ctrlJ_ram] until 45433
    calls [ctrlA1_call, ctrlJ_call, bgImpede_call, ctrlAttr_call]
    exact finish (clear r1; exact_finish frame1_impede)
set_option maxRecDepth 20000 in
summary_interface frame1_impede
summary_reach frame1_impede 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame1_exit_call (stop : UInt16)
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
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 sp ram prg) = 0xDC97) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hs0 := ctrlA1_s_eq' sp
  have hs1 : bgPre_s (ctrlJ_s (ctrlA1_s sp)) = sp + 254 := by
    delta bgPre_s ctrlJ_s ctrlA1_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame1_exit hrun [r1, hI, hs1, bgPre_ram_read, bgPre_writes, ctrlJ_ram] until 45433
    calls [ctrlA1_call, ctrlJ_call, bgPre_exit_call, ctrlAttr_call]
    exact finish (clear r1 hs1; exact_finish frame1_exit)
set_option maxRecDepth 20000 in
summary_interface frame1_exit
summary_reach frame1_exit 0xB179

theorem ctrlA2_s_eq' (sp : UInt8) : ctrlA2_s sp = sp := by delta ctrlA2_s ctrlAux_s ctrlMid_s; rfl

/-- The RAM and stack pointer at `PlayerBGCollision`, from state 2. -/
noncomputable abbrev frameR2 (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA2_s sp) (ctrlA2_ram sp ram prg)
noncomputable abbrev frameS2 (sp : UInt8) : UInt8 := ctrlJ_s (ctrlA2_s sp)

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame2_side_call (stop : UInt16)
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
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hx_fs : bgSide_s (frameS2 sp) (frameR2 sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS2 sp) (frameR2 sp ram prg) prg hccode (Or.inl hx_foot)).1
    rw [h]; show ctrlJ_s (ctrlA2_s sp) = sp + 254; delta ctrlJ_s ctrlA2_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA2_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA2_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA2_s ctrlAux_s ctrlMid_s; rfl
  have hfs' : footCheck_s (bgSize_y (bgPre_ram (frameR2 sp ram prg))) (bgSize_s (bgPre_s (frameS2 sp)))
      (bgSize_ram (bgPre_ram (frameR2 sp ram prg))) prg = sp + 254 := by
    have h := hx_fs; simp only [bgSide_s] at h; exact h
  have he0 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA2_s sp).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he1 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA2_s sp + 255).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he2 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA2_s sp + 255).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  have he3 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA2_s sp).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame2_side hrun [r1, r2, hI, hx_fs, he0, he1, he2, he3, stackAt, bgSide_ram_read, bgSide_writes, ctrlJ_ram, bgSide_pc] until 45433
    calls [ctrlA2_call, ctrlJ_call, bgSide_call, ctrlAttr_call]
    exact finish (clear r1 r2 he0 he1 he2 he3; exact_finish frame2_side)
set_option maxRecDepth 20000 in
summary_interface frame2_side
summary_reach frame2_side 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame2_impede_call (stop : UInt16)
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
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 2) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR2 sp ram prg)) (bgSize_s (bgPre_s (frameS2 sp))) (bgRam (frameR2 sp ram prg)) prg = 0xDF8A) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hx_fs : bgImpede_s (frameS2 sp) (frameR2 sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS2 sp) (frameR2 sp ram prg) prg hccode (Or.inr hx_foot)).2
    rw [h]; show ctrlJ_s (ctrlA2_s sp) = sp + 254; delta ctrlJ_s ctrlA2_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA2_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA2_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA2_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame2_impede hrun [r1, hI, hx_fs, bgImpede_ram_read, bgImpede_writes, ctrlJ_ram] until 45433
    calls [ctrlA2_call, ctrlJ_call, bgImpede_call, ctrlAttr_call]
    exact finish (clear r1; exact_finish frame2_impede)
set_option maxRecDepth 20000 in
summary_interface frame2_impede
summary_reach frame2_impede 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame2_exit_call (stop : UInt16)
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
        (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 2) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 sp ram prg) = 0xDC97) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hs0 := ctrlA2_s_eq' sp
  have hs1 : bgPre_s (ctrlJ_s (ctrlA2_s sp)) = sp + 254 := by
    delta bgPre_s ctrlJ_s ctrlA2_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame2_exit hrun [r1, hI, hs1, bgPre_ram_read, bgPre_writes, ctrlJ_ram] until 45433
    calls [ctrlA2_call, ctrlJ_call, bgPre_exit_call, ctrlAttr_call]
    exact finish (clear r1 hs1; exact_finish frame2_exit)
set_option maxRecDepth 20000 in
summary_interface frame2_exit
summary_reach frame2_exit 0xB179

theorem ctrlA3_s_eq' (sp : UInt8) : ctrlA3_s sp = sp := by delta ctrlA3_s ctrlAux_s ctrlMid_s; rfl

/-- The RAM and stack pointer at `PlayerBGCollision`, from state 3. -/
noncomputable abbrev frameR3 (sp : UInt8) (ram prg : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA3_s sp) (ctrlA3_ram sp ram prg)
noncomputable abbrev frameS3 (sp : UInt8) : UInt8 := ctrlJ_s (ctrlA3_s sp)

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame3_side_call (stop : UInt16)
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
        (hclcode : CodeAt prg 0x33C7 climbingCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 3) (hsize : ram 0x70B = 0)
    (hx_go : bgPre_pc (frameR3 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR3 sp ram prg)) (bgSize_s (bgPre_s (frameS3 sp))) (bgRam (frameR3 sp ram prg)) prg = 0xDD5E)
    (hx_eb : bgFootRam (frameS3 sp) prg (frameR3 sp ram prg) 0xEB < 0x16)
    (hx_coin : noSideCoin prg (bgFootRam (frameS3 sp) prg (frameR3 sp ram prg)) = true)
    (hx_climb : noSideClimb prg (bgFootRam (frameS3 sp) prg (frameR3 sp ram prg)) = true)
    (hx_pipe : noSidePipeEntry prg (bgFootRam (frameS3 sp) prg (frameR3 sp ram prg)) = true) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hx_fs : bgSide_s (frameS3 sp) (frameR3 sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS3 sp) (frameR3 sp ram prg) prg hccode (Or.inl hx_foot)).1
    rw [h]; show ctrlJ_s (ctrlA3_s sp) = sp + 254; delta ctrlJ_s ctrlA3_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA3_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA3_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA3_s ctrlAux_s ctrlMid_s; rfl
  have hfs' : footCheck_s (bgSize_y (bgPre_ram (frameR3 sp ram prg))) (bgSize_s (bgPre_s (frameS3 sp)))
      (bgSize_ram (bgPre_ram (frameR3 sp ram prg))) prg = sp + 254 := by
    have h := hx_fs; simp only [bgSide_s] at h; exact h
  have he0 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA3_s sp).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he1 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA3_s sp + 255).toUInt16) &&& 2047) = true := by
    rw [hs0]; simp
  have he2 : ((256 ||| sp.toUInt16) &&& 2047 == (256 ||| (ctrlA3_s sp + 255).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  have he3 : ((256 ||| (sp + 255).toUInt16) &&& 2047 == (256 ||| (ctrlA3_s sp).toUInt16) &&& 2047) = false := by
    rw [hs0]; bv_decide
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame3_side hrun [r1, r2, hI, hx_fs, he0, he1, he2, he3, stackAt, bgSide_ram_read, bgSide_writes, ctrlJ_ram, bgSide_pc] until 45433
    calls [ctrlA3_call, ctrlJ_call, bgSide_call, ctrlAttr_call]
    exact finish (clear r1 r2 he0 he1 he2 he3; exact_finish frame3_side)
set_option maxRecDepth 20000 in
summary_interface frame3_side
summary_reach frame3_side 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame3_impede_call (stop : UInt16)
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
        (hclcode : CodeAt prg 0x33C7 climbingCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 3) (hsize : ram 0x70B = 0)
    (hx_go : bgPre_pc (frameR3 sp ram prg) = 0xDC98)
    (hx_hc : headCoin prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_hh : headHit prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_fc : footCoin prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_fa : footAxeAt prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_pe : pipeEntryAt prg (bgRam (frameR3 sp ram prg)) (bgY (frameR3 sp ram prg)) = false)
    (hx_foot : footCheck_pc (bgY (frameR3 sp ram prg)) (bgSize_s (bgPre_s (frameS3 sp))) (bgRam (frameR3 sp ram prg)) prg = 0xDF8A) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hx_fs : bgImpede_s (frameS3 sp) (frameR3 sp ram prg) prg = sp + 254 := by
    have h := (background_stack_normal (frameS3 sp) (frameR3 sp ram prg) prg hccode (Or.inr hx_foot)).2
    rw [h]; show ctrlJ_s (ctrlA3_s sp) = sp + 254; delta ctrlJ_s ctrlA3_s ctrlAux_s ctrlMid_s; rfl
  have hs0 := ctrlA3_s_eq' sp
  have hs1 : bgSize_s (bgPre_s (ctrlJ_s (ctrlA3_s sp))) = sp + 254 := by
    delta bgSize_s bgPre_s ctrlJ_s ctrlA3_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame3_impede hrun [r1, hI, hx_fs, bgImpede_ram_read, bgImpede_writes, ctrlJ_ram] until 45433
    calls [ctrlA3_call, ctrlJ_call, bgImpede_call, ctrlAttr_call]
    exact finish (clear r1; exact_finish frame3_impede)
set_option maxRecDepth 20000 in
summary_interface frame3_impede
summary_reach frame3_impede 0xB179

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem frame3_exit_call (stop : UInt16)
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
        (hclcode : CodeAt prg 0x33C7 climbingCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 3) (hsize : ram 0x70B = 0)
    (hx_go : bgPre_pc (frameR3 sp ram prg) = 0xDC97) :
    ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hs0 := ctrlA3_s_eq' sp
  have hs1 : bgPre_s (ctrlJ_s (ctrlA3_s sp)) = sp + 254 := by
    delta bgPre_s ctrlJ_s ctrlA3_s ctrlAux_s ctrlMid_s; rfl
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 3000)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary frame3_exit hrun [r1, hI, hs1, bgPre_ram_read, bgPre_writes, ctrlJ_ram] until 45433
    calls [ctrlA3_call, ctrlJ_call, bgPre_exit_call, ctrlAttr_call]
    exact finish (clear r1 hs1; exact_finish frame3_exit)
set_option maxRecDepth 20000 in
summary_interface frame3_exit
summary_reach frame3_exit 0xB179

end Smb.Routine
