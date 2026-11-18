import Smb.Data.ProofRom
import Smb.Summary
import Smb.Routine.MovementSubs
import Smb.Routine.Climbing
import Smb.Routine.PlayerAux

/-!
# `PlayerCtrlRoutine` (`$B0E9`) up to its `jsr PlayerBGCollision` (`$B15A`), per state

Segments, each summarized to one end state whatever its branches: the controller bits (`ctrlPre`, 11 paths), the
bounding-box control and moving direction (`ctrlMid`, 9), the calls from `ScrollHandler` on (`ctrlAux`, 2).
Composed with `PlayerMovementSubs` (`ms0`-`ms2`), each `ctrlA*` has one path: run flat, the branches multiply past
100 paths, and each repeats the calls. Conditions: those of `ms*_call`.
-/
namespace Smb.Routine
set_option linter.unusedVariables false

/-- `$B0E9`–`$B12A`: `PlayerCtrlRoutine`, the controller bits, up to `jsr PlayerMovementSubs`. -/
def ctrlPreCode : List UInt8 := smbPrg% 0xB0E9 66
/-- `$B12E`–`$B14B`: bounding-box control and moving direction, after the movement. -/
def ctrlMidCode : List UInt8 := smbPrg% 0xB12E 30
/-- `$B14C`–`$B159`: the calls from `ScrollHandler` to `BoundingBoxCore`. -/
def ctrlAuxCode : List UInt8 := smbPrg% 0xB14C 14

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlPre_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB0E9 ≤ a && a ≤ 0xB12B) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hcode : CodeAt prg 0x30E9 ctrlPreCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  simp only [CodeAt, ctrlPreCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 40)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ctrlPre hrun [hcode, hI] until 45355 exact finish (clear hcode; exact_finish ctrlPre)
summary_interface ctrlPre
summary_regs ctrlPre

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlMid_call (stop : UInt16) (hstop : ∀ a : UInt16, (0xB12E ≤ a && a ≤ 0xB14C) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x312E ctrlMidCode) (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xB12E, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  simp only [CodeAt, ctrlMidCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 20)).run ⟨⟨0xB12E, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary ctrlMid hrun [hcode, hI] until 45388 exact finish (clear hcode; exact_finish ctrlMid)
summary_interface ctrlMid
summary_regs ctrlMid

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlAux_call (stop : UInt16)
    (hstop : ∀ a : UInt16, (0xAF93 ≤ a && a ≤ 0xB049 || 0xB14C ≤ a && a ≤ 0xB15A ||
      0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop)
    (m : Nat) (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x314C ctrlAuxCode)
    (hscode : CodeAt prg 0x2F93 scrollCode) (htab : CodeAt prg 0x71E3 xOffscreenBitsData)
    (hgxcode : CodeAt prg 0x71F3 getXOffscreenBitsCode) (hdcode : CodeAt prg 0x726D dividePDiffCode)
    (hocode : CodeAt prg 0x7180 getPlayerOffscreenBitsCode) (hsetcode : CodeAt prg 0x71C0 getOffScreenBitsSetCode)
    (hytab : CodeAt prg 0x722B yOffscreenBitsData) (hycode : CodeAt prg 0x7234 getYOffscreenBitsCode)
    (hrcode : CodeAt prg 0x712A relativePlayerPositionCode) (hwcode : CodeAt prg 0x7142 relWOfsCode)
    (hobjcode : CodeAt prg 0x7171 getObjRelativePositionCode) (hbcode : CodeAt prg 0x629C boundingBoxCoreCode)
    (hI : (p &&& 4 == 0) = false) :
    ((CPU.runTo (σ := Plain) stop (m + 700)).run ⟨⟨0xB14C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 := by
  have hsScr : ∀ a : UInt16, (0xAF93 ≤ a && a ≤ 0xB033 || 0xB038 ≤ a && a ≤ 0xB049 ||
      0xF1F6 ≤ a && a ≤ 0xF22A || 0xF26D ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsGpo : ∀ a : UInt16, (0xF180 ≤ a && a ≤ 0xF186 || 0xF1C0 ≤ a && a ≤ 0xF1E2 ||
      0xF1F6 ≤ a && a ≤ 0xF22A || 0xF239 ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsRpp : ∀ a : UInt16, (0xF12A ≤ a && a ≤ 0xF130 || 0xF142 ≤ a && a ≤ 0xF147 ||
      0xF171 ≤ a && a ≤ 0xF17F) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsBbc : ∀ a : UInt16, (0xE29C ≤ a && a ≤ 0xE2DD) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have rs : prg 0x3033 = 0x60 := by
    have h := hscode; simp only [CodeAt, scrollCode, UInt16.reduceAdd] at h; simp [h]
  have ro : prg 0x71D6 = 0x60 := by
    have h := hsetcode; simp only [CodeAt, getOffScreenBitsSetCode, UInt16.reduceAdd] at h; simp [h]
  have rr : prg 0x7147 = 0x60 := by
    have h := hwcode; simp only [CodeAt, relWOfsCode, UInt16.reduceAdd] at h; simp [h]
  have rb : prg 0x62DD = 0x60 := by
    have h := hbcode; simp only [CodeAt, boundingBoxCoreCode, UInt16.reduceAdd] at h; simp [h]
  simp only [CodeAt, ctrlAuxCode, UInt16.reduceAdd] at hcode
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 700)).run ⟨⟨0xB14C, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = f
  sym_summary ctrlAux hrun [hcode, rs, ro, rr, rb, hI, scrollRam, gxoRam, scrMid, gpoRam, gpoMid, gyoRam, rppRam, bbcRam,
      absIdx, dummyIdx, forceIdx, pageIdx, posIdx, speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx] until 45402
    calls [scrollHandler_call, getPlayerOffscreenBits_call, relativePlayerPosition_call, boundingBoxCore_call_player]
    exact finish (clear hcode rs ro rr rb; exact_finish ctrlAux)
summary_interface ctrlAux
summary_regs ctrlAux

/-- `$B12B`: `jsr PlayerMovementSubs`. -/
def ctrlJsrCode : List UInt8 := smbPrg% 0xB12B 3

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlA0_call (stop : UInt16)
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
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 0) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ((CPU.runTo (σ := Plain) stop (m + 1500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 1500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ctrlA0 hrun [hj, rg, ra, hI, ctrlPre_ram_read, ctrlPre_writes, ctrlPre_s_eq, ctrlPre_bad_eq,
      ms0_ram_read, ms0_writes, ms0_s_eq, ms0_bad_eq, ctrlMid_s_eq, ctrlMid_bad_eq, absIdx, dummyIdx, forceIdx, pageIdx,
      posIdx, speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx] until 45402
    calls [ctrlPre_call, ms0_call, ctrlMid_call, ctrlAux_call]
    exact finish (clear hj rg ra; exact_finish ctrlA0)
summary_interface ctrlA0
summary_regs ctrlA0


set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlA1_call (stop : UInt16)
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
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 1) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ((CPU.runTo (σ := Plain) stop (m + 1500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 1500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ctrlA1 hrun [hj, rg, ra, hI, ctrlPre_ram_read, ctrlPre_writes, ctrlPre_s_eq, ctrlPre_bad_eq,
      ms1_ram_read, ms1_writes, ms1_s_eq, ms1_bad_eq, ctrlMid_s_eq, ctrlMid_bad_eq, absIdx, dummyIdx, forceIdx, pageIdx,
      posIdx, speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx] until 45402
    calls [ctrlPre_call, ms1_call, ctrlMid_call, ctrlAux_call]
    exact finish (clear hj rg ra; exact_finish ctrlA1)
summary_interface ctrlA1
summary_regs ctrlA1


set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlA2_call (stop : UInt16)
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
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 2) (hsize : ram 0x70B = 0) (hswim : ram 0x704 = 0)
    (hjs : ram 0x70E = 0) (hspd : ram 0x9F + 0x40 < 0x80) :
    ((CPU.runTo (σ := Plain) stop (m + 1500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
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
  have hj := hjcode0
  simp only [CodeAt, ctrlJsrCode, UInt16.reduceAdd] at hj
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 1500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ctrlA2 hrun [hj, rg, hI, ctrlPre_ram_read, ctrlPre_writes, ctrlPre_s_eq, ctrlPre_bad_eq,
      ms2_ram_read, ms2_writes, ms2_s_eq, ms2_bad_eq, ctrlMid_s_eq, ctrlMid_bad_eq, absIdx, dummyIdx, forceIdx, pageIdx,
      posIdx, speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx] until 45402
    calls [ctrlPre_call, ms2_call, ctrlMid_call, ctrlAux_call]
    exact finish (clear hj rg; exact_finish ctrlA2)
summary_interface ctrlA2
summary_regs ctrlA2

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
sym_theorem ctrlA3_call (stop : UInt16)
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
    (hclcode : CodeAt prg 0x33C7 climbingCode)
    (hI : (p &&& 4 == 0) = false) (hst : ram 0x1D = 3) (hsize : ram 0x70B = 0) :
    ((CPU.runTo (σ := Plain) stop (m + 1500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 := by
  have hsPre : ∀ a : UInt16, (0xB0E9 ≤ a && a ≤ 0xB12B) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsMs : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xB329 ≤ a && a ≤ 0xC046) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsMid : ∀ a : UInt16, (0xB12E ≤ a && a ≤ 0xB14C) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have hsAux : ∀ a : UInt16, (0xAF93 ≤ a && a ≤ 0xB049 || 0xB14C ≤ a && a ≤ 0xB15A ||
      0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ stop := by
    intro a h; apply hstop; revert h; bv_decide
  have rg : prg 0x341F = 0x60 := by
    have h := hclcode; simp only [CodeAt, climbingCode, UInt16.reduceAdd] at h; simp [h]
  have ra : prg 0x3423 = 0x60 := by
    have h := hclcode; simp only [CodeAt, climbingCode, UInt16.reduceAdd] at h; simp [h]
  have hj := hjcode0
  simp only [CodeAt, ctrlJsrCode, UInt16.reduceAdd] at hj
  generalize hrun : ((CPU.runTo (σ := Plain) stop (m + 1500)).run ⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = f
  sym_summary ctrlA3 hrun [hj, rg, ra, hI, ctrlPre_ram_read, ctrlPre_writes, ctrlPre_s_eq, ctrlPre_bad_eq,
      ms3_ram_read, ms3_writes, ms3_s_eq, ms3_bad_eq, ctrlMid_s_eq, ctrlMid_bad_eq, absIdx, dummyIdx, forceIdx, pageIdx,
      posIdx, speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx] until 45402
    calls [ctrlPre_call, ms3_call, ctrlMid_call, ctrlAux_call]
    exact finish (clear hj rg ra; exact_finish ctrlA3)
summary_interface ctrlA3
summary_regs ctrlA3

end Smb.Routine
