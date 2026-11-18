import Smb.Routine.PlayerBlock
import Smb.PlayerCtrlData

/-!
# The collision region's entry conditions, from `PlayerCtrlRoutine`'s entry

`block0` takes the collision region's entry conditions as hypotheses on the RAM at `PlayerBGCollision` (`bg0 ram`).
The checked region `PlayerCtrl` (`$B0E9` to `$DC64`, bounds only) gives them from its entry box at `$B0E9`
instead: the run to `$DC64` stays in its invariant, the summaries say the state there has RAM `bg0 ram` (the last
step is the `jsr` at `$B15A`, `jsr_bg`), and its boxes at `$DC64` lie in the collision region's entry, under bounds
inside the collision region's (`ctrl_links`).

So `block0c`, `block1c` and `block2c` need nothing about the RAM beyond the frame's own entry at `$B0E9`.
-/
namespace Smb.Routine.PlayerCtrlLink
open Smb Smb.Abs Smb.Routine Smb.Routine.HorizontalLimit Smb.Routine.FrameCollision Smb.Routine.Launch

theorem ctrl_accepted : PlayerCtrl.accepted Smb.prg = true := by native_decide
theorem ctrl_top : gAt PlayerCtrl.conf.globals 0x300 = .top := eq_top_of_topB (by native_decide)
theorem ctrl_top2 : gAt PlayerCtrl.conf.globals 0x340 = .top := eq_top_of_topB (by native_decide)
theorem ctrl_exit_eq : PlayerCtrl.conf.exit = [0xDC64] := by native_decide

/-- The region's boxes at `$DC64` are inside the collision region's entry, and its bounds inside the collision
region's. -/
def links (prg : ByteArray) : Bool :=
  ((PlayerCtrl.conf.table prg).at 0xDC64).all (fun b => Collision.conf.entries.any (Box.le PlayerCtrl.conf.globals b)) &&
  (List.range 0x800).all fun i => (List.range 256).all fun v =>
    !(gAt PlayerCtrl.conf.globals (UInt16.ofNat i)).mem (UInt8.ofNat v) ||
      (gAt Collision.conf.globals (UInt16.ofNat i)).mem (UInt8.ofNat v)

theorem links_true : links Smb.prg = true := by native_decide
theorem coll_size : Collision.conf.globals.size = 0x800 := by native_decide

theorem ctrl_plain (s : Plain) (hc : Code (romOf Smb.prg) s) (e : Box) (he : e ∈ PlayerCtrl.conf.entries)
    (hh : Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals s.ram e s) (n : Nat) :
    Inv PlayerCtrl.conf.protFn PlayerCtrl.conf.globals s.ram (PlayerCtrl.conf.table Smb.prg)
      ((CPU.runTo (σ := Plain) 0xDC64 n).run s).2 := by
  have hacc := ctrl_accepted
  simp only [PlayerCtrl.accepted, Bool.and_eq_true, List.all_eq_true] at hacc
  obtain ⟨hchk, hin⟩ := hacc
  have hexit : ∀ a, PlayerCtrl.conf.exitFn a = true → a = 0xDC64 := by
    intro a h
    simpa [Config.C.exitFn, ctrl_exit_eq] using h
  exact (inv_runTo hchk ctrl_top ctrl_top2 0xDC64 hexit n s hc (inv_of_entry (hin e he) hh)).2

set_option maxHeartbeats 4000000 in
/-- The `jsr PlayerBGCollision` at `$B15A`. -/
theorem jsr_bg (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (bad : Bool)
    (hcode : CodeAt prg 0x315A ctrlJsrBgCode) :
    let t := ((CPU.runTo (σ := Plain) 0xDC64 1).run ⟨⟨0xB15A, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2
    t.regs.pc = 0xDC64 ∧ t.ram = ctrlJ_ram sp ram := by
  simp only [CodeAt, ctrlJsrBgCode, UInt16.reduceAdd] at hcode
  obtain ⟨h0, h1, h2, -⟩ := hcode
  dsimp only
  generalize hr : ((CPU.runTo (σ := Plain) 0xDC64 1).run ⟨⟨0xB15A, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩).2 = t
  sym_run hr [h0, h1, h2] until 56420
  all_goals
    intros
    subst hr
    refine ⟨rfl, ?_⟩
    funext i
    delta ctrlJ_ram
    rfl

theorem stopD : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ 0xDC64 := by
  intro a h; revert h; bv_decide (config := { enums := false })

theorem code_st (a x y sp p : UInt8) (ram : UInt16 → UInt8) (c : UInt64) :
    Code (romOf Smb.prg) (⟨⟨0xB0E9, a, x, y, sp, p⟩, ram, romFn, c, false⟩ : Plain) :=
  code_romFn _ _ _ _ _ _ _ _ _

/-- What the region's invariant at the `jsr`'s target gives: the collision region's entry conditions. -/
theorem entry_of_ctrl {s : Plain} {ram0 : UInt16 → UInt8} (hpc : s.regs.pc = 0xDC64)
    (hi : Inv PlayerCtrl.conf.protFn PlayerCtrl.conf.globals ram0 (PlayerCtrl.conf.table Smb.prg) s) :
    (∀ e ∈ Collision.conf.entries, ∀ c ∈ e.cells, c.2.mem (s.ram c.1) = true) ∧
      (∀ i, (gAt Collision.conf.globals i).mem (s.ram i) = true) := by
  obtain ⟨b, hbm, hh⟩ := hi
  rw [hpc] at hbm
  have hl := links_true
  simp only [links, Bool.and_eq_true, List.all_eq_true] at hl
  obtain ⟨hl1, hw⟩ := hl
  obtain ⟨e', he', hle⟩ := List.any_eq_true.mp (hl1 b hbm)
  have hh' := holds_of_le hle hh
  refine ⟨fun e he c hc => ?_, fun i => ?_⟩
  · have hee : e = e' := by
      have := entry_eq
      match h : Collision.conf.entries, he, he' with
      | [x], he, he' =>
        simp only [List.mem_singleton] at he he'
        rw [he, he']
      | [], he, _ => simp at he
      | _ :: _ :: _, _, _ => rw [h] at this; simp at this
    subst hee
    exact hh'.cells c hc
  · by_cases hi : i.toNat < 0x800
    · have h1 := hw i.toNat (List.mem_range.mpr hi)
      have h2 := h1 (s.ram i).toNat (List.mem_range.mpr (s.ram i).toNat_lt)
      simp only [UInt16.ofNat_toNat, UInt8.ofNat_toNat, hh.glob i, Bool.not_true, Bool.false_or] at h2
      exact h2
    · unfold gAt Array.getD
      rw [dif_neg (by rw [coll_size]; omega)]
      rfl

set_option maxHeartbeats 4000000 in
theorem bg0_of_ctrl (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false) (e : Box) (he : e ∈ PlayerCtrl.conf.entries)
    (hh : Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals ram e ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩) :
    (∀ e ∈ Collision.conf.entries, ∀ c ∈ e.cells, c.2.mem (bg0 ram c.1) = true) ∧
      (∀ i, (gAt Collision.conf.globals i).mem (bg0 ram i) = true) := by
  obtain ⟨j1, p1, c1, heq1, _⟩ := ctrlA0_call 0xDC64 stopD 1 a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  have hpc1 : ctrlA0_pc = 45402 := by delta ctrlA0_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨jp, jr⟩ := jsr_bg ctrlA0_a ctrlA0_x ctrlA0_y (ctrlA0_s 0xF7) p1 (ctrlA0_ram 0xF7 ram romFn) romFn c1 ctrlA0_bad
    rom_ctrlJsrBgCode
  rw [runTo_one _ _ (by simp)] at jp jr
  rw [runTo_succ 0xDC64 j1 _ (by simp), runTo_at _ _ _ jp] at heq1
  have hi := ctrl_plain _ (code_st _ _ _ _ _ _ _) e he hh (1 + 1500)
  rw [heq1] at hi
  have := entry_of_ctrl jp hi
  rw [jr] at this
  exact this

/-- **`block0` from the frame's own entry**: the ground-state frame's block, with the collision region's entry
conditions from the routine's region at `$B0E9`. -/
theorem block0c (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hctrl : ∃ e ∈ PlayerCtrl.conf.entries,
      Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals ram e ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xAF01) :
    (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∧
      (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram) ∧
      ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.bad = false) ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88 ∨ u.regs.pc = 0xB1B8) ∧
        ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  obtain ⟨e, he, hh⟩ := hctrl
  obtain ⟨hc, hg⟩ := bg0_of_ctrl a x y p ram cyc ht hs hz hjs hspd hI e he hh
  exact PlayerBlock.block0 a x y p ram cyc hinv ht hs hz hjs hspd hI hc hg n hreach

set_option maxHeartbeats 4000000 in
theorem bg1_of_ctrl (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false) (e : Box) (he : e ∈ PlayerCtrl.conf.entries)
    (hh : Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals ram e ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩) :
    (∀ e ∈ Collision.conf.entries, ∀ c ∈ e.cells, c.2.mem (bg1 ram c.1) = true) ∧
      (∀ i, (gAt Collision.conf.globals i).mem (bg1 ram i) = true) := by
  obtain ⟨j1, p1, c1, heq1, _⟩ := ctrlA1_call 0xDC64 stopD 1 a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  have hpc1 : ctrlA1_pc = 45402 := by delta ctrlA1_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨jp, jr⟩ := jsr_bg ctrlA1_a ctrlA1_x ctrlA1_y (ctrlA1_s 0xF7) p1 (ctrlA1_ram 0xF7 ram romFn) romFn c1 ctrlA1_bad
    rom_ctrlJsrBgCode
  rw [runTo_one _ _ (by simp)] at jp jr
  rw [runTo_succ 0xDC64 j1 _ (by simp), runTo_at _ _ _ jp] at heq1
  have hi := ctrl_plain _ (code_st _ _ _ _ _ _ _) e he hh (1 + 1500)
  rw [heq1] at hi
  have := entry_of_ctrl jp hi
  rw [jr] at this
  exact this

/-- **`block1` from the frame's own entry**: the jumping frame's block, with the collision region's entry
conditions from the routine's region at `$B0E9`. -/
theorem block1c (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hctrl : ∃ e ∈ PlayerCtrl.conf.entries,
      Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals ram e ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xAF01) :
    (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∧
      (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram) ∧
      ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.bad = false) ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88 ∨ u.regs.pc = 0xB1B8) ∧
        ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  obtain ⟨e, he, hh⟩ := hctrl
  obtain ⟨hc, hg⟩ := bg1_of_ctrl a x y p ram cyc ht hs hz hjs hspd hI e he hh
  exact PlayerBlock.block1 a x y p ram cyc hinv ht hs hz hjs hspd hI hc hg n hreach

set_option maxHeartbeats 4000000 in
theorem bg2_of_ctrl (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false) (e : Box) (he : e ∈ PlayerCtrl.conf.entries)
    (hh : Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals ram e ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩) :
    (∀ e ∈ Collision.conf.entries, ∀ c ∈ e.cells, c.2.mem (bg2 ram c.1) = true) ∧
      (∀ i, (gAt Collision.conf.globals i).mem (bg2 ram i) = true) := by
  obtain ⟨j1, p1, c1, heq1, _⟩ := ctrlA2_call 0xDC64 stopD 1 a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  have hpc1 : ctrlA2_pc = 45402 := by delta ctrlA2_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨jp, jr⟩ := jsr_bg ctrlA2_a ctrlA2_x ctrlA2_y (ctrlA2_s 0xF7) p1 (ctrlA2_ram 0xF7 ram romFn) romFn c1 ctrlA2_bad
    rom_ctrlJsrBgCode
  rw [runTo_one _ _ (by simp)] at jp jr
  rw [runTo_succ 0xDC64 j1 _ (by simp), runTo_at _ _ _ jp] at heq1
  have hi := ctrl_plain _ (code_st _ _ _ _ _ _ _) e he hh (1 + 1500)
  rw [heq1] at hi
  have := entry_of_ctrl jp hi
  rw [jr] at this
  exact this

/-- **`block2` from the frame's own entry**: the falling frame's block, with the collision region's entry
conditions from the routine's region at `$B0E9`. -/
theorem block2c (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hctrl : ∃ e ∈ PlayerCtrl.conf.entries,
      Holds PlayerCtrl.conf.protFn PlayerCtrl.conf.globals ram e ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xAF01) :
    (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∧
      (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram) ∧
      ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.bad = false) ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88 ∨ u.regs.pc = 0xB1B8) ∧
        ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  obtain ⟨e, he, hh⟩ := hctrl
  obtain ⟨hc, hg⟩ := bg2_of_ctrl a x y p ram cyc ht hs hz hjs hspd hI e he hh
  exact PlayerBlock.block2 a x y p ram cyc hinv ht hs hz hjs hspd hI hc hg n hreach

end Smb.Routine.PlayerCtrlLink
