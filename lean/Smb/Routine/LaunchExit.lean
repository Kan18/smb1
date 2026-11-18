import Smb.Routine.ModelFrame

/-!
# What `PlayerCtrlRoutine` leaves of the launch's bounds

The launch's regions stop at `$B0E9` and pick up at `$B179`. The shared bounds have to hold across the stretch between, which is `ModelFrame`'s. `side0_keep` and its siblings say what the routine doesn't touch: everything outside `written`, from the routine's entry with the stack pointer at `$F7`. Of what it does touch, these are the cells with a bound:

* `$714` stays 0 for small Mario, and `$B5` at 1 while Mario stays on the screen.
* `$3A1` is cleared, and with no scroll the screen's edges, `$73D` and `$778` stay.
* `$490` and `$70E` stay, in a frame with no wall and no spring.
* `$3AD` is Mario's position on the screen.
-/
namespace Smb.Routine.LaunchExit
open Smb.Routine Smb.Routine.HorizontalLimit Smb.Routine.ModelFrame Smb.Routine.PlayerFramePosition

/-- What the routine may write, from `$B0E9` to `$B179` with the stack pointer at `$F7`. -/
def written (i : UInt16) : Bool :=
  (0x100 ≤ i && i ≤ 0x1F7) || i == 0x0 || i == 0x1 || i == 0x2 || i == 0x3 || i == 0x4 || i == 0x5 || i == 0x6 || i == 0x7 || i == 0xA || i == 0xB || i == 0xC || i == 0x1D || i == 0x33 || i == 0x45 || i == 0x57 || i == 0x6D || i == 0x86 || i == 0x9F || i == 0xB5 || i == 0xCE || i == 0xEB || i == 0xFE || i == 0xFF || i == 0x3A1 || i == 0x3AD || i == 0x3B8 || i == 0x3C4 || i == 0x3D0 || i == 0x400 || i == 0x416 || i == 0x433 || i == 0x450 || i == 0x456 || i == 0x484 || i == 0x490 || i == 0x499 || i == 0x4AC || i == 0x4AD || i == 0x4AE || i == 0x4AF || i == 0x6DB || i == 0x6FC || i == 0x6FF || i == 0x700 || i == 0x701 || i == 0x702 || i == 0x703 || i == 0x705 || i == 0x706 || i == 0x707 || i == 0x708 || i == 0x709 || i == 0x70A || i == 0x70C || i == 0x70E || i == 0x714 || i == 0x71A || i == 0x71B || i == 0x71C || i == 0x71D || i == 0x73D || i == 0x73F || i == 0x775 || i == 0x778 || i == 0x782 || i == 0x783 || i == 0x785 || i == 0x786 || i == 0x789 || i == 0x795

/-- What's written after `PlayerMovementSubs`. -/
def writtenPost (i : UInt16) : Bool :=
  (0x100 ≤ i && i ≤ 0x1F7) || i == 0x0 || i == 0x1 || i == 0x2 || i == 0x3 || i == 0x4 || i == 0x5 || i == 0x6 || i == 0x7 || i == 0x1D || i == 0x45 || i == 0x57 || i == 0x6D || i == 0x86 || i == 0x9F || i == 0xCE || i == 0xEB || i == 0xFE || i == 0xFF || i == 0x3A1 || i == 0x3AD || i == 0x3B8 || i == 0x3C4 || i == 0x3D0 || i == 0x433 || i == 0x484 || i == 0x490 || i == 0x499 || i == 0x4AC || i == 0x4AD || i == 0x4AE || i == 0x4AF || i == 0x6DB || i == 0x6FF || i == 0x709 || i == 0x70E || i == 0x71A || i == 0x71B || i == 0x71C || i == 0x71D || i == 0x73D || i == 0x73F || i == 0x775 || i == 0x778 || i == 0x785 || i == 0x786 || i == 0x795

/-- What's written after `ctrlAux`. -/
def writtenTail (i : UInt16) : Bool :=
  (0x100 ≤ i && i ≤ 0x1F7) || i == 0x0 || i == 0x1 || i == 0x2 || i == 0x3 || i == 0x4 || i == 0x5 || i == 0x6 || i == 0x7 || i == 0x1D || i == 0x57 || i == 0x6D || i == 0x86 || i == 0x9F || i == 0xCE || i == 0xEB || i == 0xFE || i == 0xFF || i == 0x3C4 || i == 0x3D0 || i == 0x433 || i == 0x484 || i == 0x490 || i == 0x4AC || i == 0x4AD || i == 0x4AE || i == 0x4AF || i == 0x6DB || i == 0x709 || i == 0x70E || i == 0x785 || i == 0x786

theorem post_of_written (i : UInt16) (hi : written i = false) : writtenPost i = false := by
  simp only [written, writtenPost] at *
  revert hi
  bv_decide (config := { enums := false })

theorem tail_of_post (i : UInt16) (hi : writtenPost i = false) : writtenTail i = false := by
  simp only [writtenPost, writtenTail] at *
  revert hi
  bv_decide (config := { enums := false })

theorem ctrlAttr_keep (r : UInt16 → UInt8) (i : UInt16) (hi : writtenTail i = false) : ctrlAttr_ram r i = r i := by
  simp only [writtenTail] at hi
  sym_exec [ctrlAttr_ram]
  revert hi
  bv_decide (config := { enums := false })

theorem ctrlJ_keep (r : UInt16 → UInt8) (i : UInt16) (hi : writtenTail i = false) : ctrlJ_ram 0xF7 r i = r i := by
  simp only [writtenTail] at hi
  sym_exec [ctrlJ_ram]
  revert hi
  bv_decide (config := { enums := false })

theorem moveIn_keep (ram : UInt16 → UInt8) (i : UInt16) (hi : written i = false) : moveIn 0xF7 ram i = ram i := by
  simp only [written] at hi
  have hp : ctrlPre_ram ram i = ram i := by
    apply ctrlPre_ram_frame
    simp only [ctrlPre_writes]
    revert hi
    bv_decide (config := { enums := false })
  simp only [moveIn, hp]
  revert hi
  bv_decide (config := { enums := false })

theorem aux_keep (ram prg : UInt16 → UInt8) (i : UInt16) (hi : writtenPost i = false) : ctrlAux_ram (ctrlMid_s 0xF7) (ctrlMid_ram ram) prg i = ram i := by
  simp only [writtenPost] at hi
  rw [ctrlAux_ram_frame _ _ _ _ (by simp only [ctrlAux_writes, absIdx]; delta ctrlMid_s; revert hi; bv_decide (config := { enums := false })),
    ctrlMid_ram_frame _ _ (by simp only [ctrlMid_writes]; revert hi; bv_decide (config := { enums := false }))]

theorem bg_keep (w R prg : UInt16 → UInt8) (i : UInt16) (hi : writtenTail i = false)
    (hs : footCheck_s (bgSize_y (bgPre_ram R)) (bgSize_s (bgPre_s 0xF5)) (bgSize_ram (bgPre_ram R)) prg = 0xF5) :
    bgSide_ram w 0xF5 R prg i = R i := by
  simp only [writtenTail] at hi
  apply bgSide_ram_frame
  simp only [bgSide_writes, stackAt, hs]
  delta bgSize_s bgPre_s
  revert hi
  bv_decide (config := { enums := false })

theorem stack_foot (R prg : UInt16 → UInt8) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (h : footCheck_pc (bgY R) (bgSize_s (bgPre_s 0xF5)) (bgRam R) prg = 0xDD5E) :
    footCheck_s (bgSize_y (bgPre_ram R)) (bgSize_s (bgPre_s 0xF5)) (bgSize_ram (bgPre_ram R)) prg = 0xF5 :=
  by
    have h2 := (background_stack_normal 0xF5 R prg hc (Or.inl h)).1
    simp only [bgSide_s] at h2
    exact h2

/-! ### With no scroll -/

theorem scroll_cell (sp : UInt8) (r : UInt16 → UInt8) (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778)
    (hn : r 0x755 < 0x50) : scrollRam sp r i = r i := by
  have h : scrolls r = false := by
    simp only [scrolls, Bool.and_eq_false_iff]
    left; left; right
    simp only [decide_eq_false_iff_not, UInt8.not_le]
    exact hn
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [scrollRam, gxoRam, scrMid, scrLeftX, scrLeftPage, scrRightX, scrRightPage, h, bne]
    fun_congr
    bv_decide (config := { enums := false })

theorem aux_scroll (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hi : i = 0x73D ∨ i = 0x778) :
    ctrlAux_ram sp ram prg i = scrollRam sp (auxIn sp ram) i := by
  have a := auxIn_at sp ram
  rcases hi with rfl | rfl <;>
  · sym_exec [ctrlAux_ram, bbcRam, rppRam, gpoRam, gpoMid, gyoRam, absIdx, dummyIdx, forceIdx, pageIdx, posIdx,
      speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx, scrollRam, gxoRam, auxIn_eta, scrMid, a, bne]

theorem aux_rel (sp : UInt8) (ram prg : UInt16 → UInt8) :
    ctrlAux_ram sp ram prg 0x3AD = scrollRam sp (auxIn sp ram) 0x86 - scrollRam sp (auxIn sp ram) 0x71C := by
  have a := auxIn_at sp ram
  sym_exec [ctrlAux_ram, bbcRam, rppRam, relX, gpoRam, gpoMid, gyoRam, absIdx, dummyIdx, forceIdx, pageIdx, posIdx,
      speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx, scrollRam, gxoRam, auxIn_eta, scrMid, a, bne]

/-- The screen's cells, and the rest of the frame's, when `$755` doesn't reach the scroll's threshold. -/
theorem aux_edge (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778)
    (hn : ram 0x755 < 0x50) : ctrlAux_ram sp ram prg i = ram i := by
  have e : ctrlAux_ram sp ram prg i = scrollRam sp (auxIn sp ram) i := by
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Smb.Routine.HorizontalLimit.ctrlAux_x sp ram prg _ (by decide)
    · exact Smb.Routine.HorizontalLimit.ctrlAux_x sp ram prg _ (by decide)
    · exact Smb.Routine.HorizontalLimit.ctrlAux_x sp ram prg _ (by decide)
    · exact Smb.Routine.HorizontalLimit.ctrlAux_x sp ram prg _ (by decide)
    · exact aux_scroll sp ram prg _ (Or.inl rfl)
    · exact aux_scroll sp ram prg _ (Or.inr rfl)
  have a := auxIn_at sp ram
  rw [e, scroll_cell sp _ i hi (by rw [a 0x755 (by decide)]; exact hn)]
  apply a
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ### The foot check, on `$490` and `$70E` -/

set_option maxHeartbeats 8000000 in
theorem foot_kept (y sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hi : i = 0x490 ∨ i = 0x70E)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : headBlocked prg ram y = false) (hhc : headCoin prg ram y = false) (hc : footCoin prg ram y = false) (ha : footAxeAt prg ram y = false)
    (hp : pipeEntryAt prg ram y = false) (hn : impeded prg ram y = false) (he : ram 0x70E = 0)
    (hs : (footTile prg ram y != 0x67 && footTile prg ram y != 0x68) = true) :
    footCheck_ram y sp ram prg i = ram i := by
  have hsp := headPart_speed y sp ram prg hb
  have hkd := headPart_keeps y sp 4 ram prg (by decide) 0x0D (by decide)
  have hkp1 := headPart_keeps y sp 4 ram prg (by decide) 0x86 (by decide)
  have hkp2 := headPart_keeps y sp 4 ram prg (by decide) 0x6D (by decide)
  have hkp3 := headPart_keeps y sp 4 ram prg (by decide) 0x400 (by decide)
  have hhit : headHit prg ram y = false := by simp [headHit, hb]
  have htile := fun k => headPart_tile y sp 4 ram prg (by decide) k
  have hkce := headPart_keeps y sp 4 ram prg (by decide) 0xCE (by decide)
  have hk433 := headPart_keeps y sp 4 ram prg (by decide) 0x433 (by decide)
  have hk1d := headPart_keeps y sp 4 ram prg (by decide) 0x1D (by decide)
  have hk57 := headPart_keeps y sp 4 ram prg (by decide) 0x57 (by decide)
  have hk705 := headPart_keeps y sp 4 ram prg (by decide) 0x705 (by decide)
  have hk700 := headPart_keeps y sp 4 ram prg (by decide) 0x700 (by decide)
  have hk33 := headPart_keeps y sp 4 ram prg (by decide) 0x33 (by decide)
  have hk45 := headPart_keeps y sp 4 ram prg (by decide) 0x45 (by decide)
  have hk783 := headPart_keeps y sp 4 ram prg (by decide) 0x783 (by decide)
  have hk703 := headPart_keeps y sp 4 ram prg (by decide) 0x703 (by decide)
  have hk416 := headPart_keeps y sp 4 ram prg (by decide) 0x416 (by decide)
  have hk70a := headPart_keeps y sp 4 ram prg (by decide) 0x70A (by decide)
  have hk708 := headPart_keeps y sp 4 ram prg (by decide) 0x708 (by decide)
  have hk706 := headPart_keeps y sp 4 ram prg (by decide) 0x706 (by decide)
  have hk709 := headPart_keeps y sp 4 ram prg (by decide) 0x709 (by decide)
  have hk70e := headPart_keeps y sp 4 ram prg (by decide) 0x70E (by decide)
  have hk490 := headPart_keeps y sp 4 ram prg (by decide) 0x490 (by decide)
  have hkb := headPart_keeps y sp 4 ram prg (by decide) 0xB (by decide)
  obtain ⟨h0, h1, h2, h3⟩ := htbl
  simp only [headBlocked, footCoin, footAxeAt, pipeEntryAt, impeded, lands, footSolid, footProbed, footTile, footTileL, footTileR, headSpeed, headBumps,
    headProbed, headTile, coinTile, solidTile, climbable, climbExt, bbOffset, bne] at hb hc ha hp hn hs
  rcases hi with rfl | rfl <;>
  · simp only [footCheck_ram, footCheck_c0, footCheck_c1, footCheck_c2, footCheck_c3, footCheck_c4, footCheck_c5, footCheck_c6, footCheck_c7, footCheck_c8, footCheck_c9, footCheck_c10, footCheck_c11, footCheck_c12, footCheck_c13, footCheck_c14, chkFoot_ram, chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, chkFoot_c5, chkFoot_c6, chkFoot_c7, chkFoot_c8, chkFoot_c9, chkFoot_c10, chkFoot_c11, chkFoot_c12, chkFoot_c13, chkFoot_c14, chkFoot_c15, chkFoot_c16, chkFoot_c17, chkFoot_c18, chkFoot_c19, chkFoot_c20, chkFoot_c21, chkFoot_c22, chkFoot_c23, afterFoot, footGround, lands, footSolid, footProbed, footTile, footTileL, footTileR, headSpeed, headBumps, headBlocked, headProbed, headTile, coinTile, solidTile, bbOffset]
    sym_exec [hkd, hkp1, hkp2, hkp3, footAxe, hhit, hhc, footGround, climbable, climbExt, pipeDown, bne, hsp, htile, hkce, hk433, hk1d, hk57, hk705, hk700, hk33, hk45, hk783, hk703, hk416, hk70a, hk708, hk706, hk709, hk70e, hk490, hkb] at *
    all_goals
      fun_congr
      bv_decide (config := { enums := false })

theorem bgPre_490 (R : UInt16 → UInt8) (hgo : bgPre_pc R = 0xDC98) : bgPre_ram R 0x490 = 0xFF := by
  simp only [bgPre_pc, bgPre_ram, bgPre_c0, bgPre_c1, bgPre_c2, bgPre_c3, bgPre_c4, bgPre_c5, bgPre_c6, bgPre_c7, bgPre_c8, bgPre_c9, bgPre_c10, bgPre_c11, bgPre_c12, bgPre_c13] at hgo ⊢
  sym_exec [bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

/-- `PlayerBGCollision` with a clear frame leaves `$490` at `$FF` and `$70E` alone. -/
theorem bgSide_490 (w : UInt16 → UInt8) (sp : UInt8) (R prg : UInt16 → UInt8) (hb : BgClear w sp R prg)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6) :
    bgSide_ram w sp R prg 0x490 = 0xFF ∧ bgSide_ram w sp R prg 0x70E = R 0x70E := by
  have he : bgRam R 0x70E = 0 := by rw [bgRam_cell R hb.go 0x70E (by decide) (by decide)]; exact hb.js
  have h1 := foot_kept (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) prg 0x490 (Or.inl rfl) htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp he hb.spring
  have h2 := foot_kept (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) prg 0x70E (Or.inr rfl) htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp he hb.spring
  have hs (q : UInt8) (i : UInt16) (hi : i = 0x490 ∨ i = 0x70E) : sideScratch q i = false := by
    simp only [sideScratch, stackAt]
    bv_decide (config := { enums := false })
  have hp : bgRam R 0x490 = 0xFF := by
    show bgSize_ram (bgPre_ram R) 0x490 = _
    rw [bgSize_ram_frame _ _ (by simp only [bgSize_writes])]
    exact bgPre_490 R hb.go
  constructor
  · simp only [bgSide_ram]
    refine (side_cell w _ prg (bgFootRam sp prg R) 0x490 hb.side (hs _ _ (Or.inl rfl))).trans ?_
    show footCheck_ram (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) prg 0x490 = _
    rw [h1, hp]
  · simp only [bgSide_ram]
    refine (side_cell w _ prg (bgFootRam sp prg R) 0x70E hb.side (hs _ _ (Or.inr rfl))).trans ?_
    show footCheck_ram (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) prg 0x70E = _
    rw [h2, he]
    exact hb.js.symm

/-! ### The routine's exit -/

/-- What the routine does to the cells that have bounds. -/
structure Exit (ram F : UInt16 → UInt8) : Prop where
  keep : ∀ i, written i = false → F i = ram i
  crouch : F 0x714 = 0
  high : F 0xB5 = 1
  plat : F 0x3A1 = 0
  left1 : F 0x71A = ram 0x71A
  right1 : F 0x71B = ram 0x71B
  left2 : F 0x71C = ram 0x71C
  right2 : F 0x71D = ram 0x71D
  scroll : F 0x73D = ram 0x73D
  mirror : F 0x778 = ram 0x778
  coll : F 0x490 = 0xFF
  spring : F 0x70E = 0
  rel : F 0x3AD = F 0x86 - ram 0x71C
  ab : F 0x0A = ram 0x6FC &&& 0xC0

/-- What the frame's hypotheses have to say of the routine's entry, other than a clear collision. -/
structure Entry (ram : UInt16 → UInt8) : Prop where
  small : ram 0x754 ≠ 0
  high : ram 0xB5 = 1
  y : 0x20 ≤ ram 0xCE ∧ ram 0xCE < 0xE0
  speed : ram 0x9F + 8 < 0x10
  scroll : ram 0x755 < 0x50

theorem a_of_input (r : UInt16 → UInt8) (h : Smb.Routine.ModelBridge.InputCells r) : r 0x0A = r 0x6FC &&& 0xC0 := h.1

theorem attr_other (r : UInt16 → UInt8) (i : UInt16) (hi : i ≠ 0x3C4) : ctrlAttr_ram r i = r i := by
  sym_exec [ctrlAttr_ram]
  revert hi
  bv_decide (config := { enums := false })

theorem j_other (r : UInt16 → UInt8) (i : UInt16) (hi : i < 0x100 ∨ 0x200 ≤ i) : ctrlJ_ram 0xF7 r i = r i := by
  sym_exec [ctrlJ_ram]
  revert hi
  bv_decide (config := { enums := false })

theorem pre_other (ram : UInt16 → UInt8) (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778 ∨ i = 0x755 ∨ i = 0x754 ∨ i = 0xB5 ∨ i = 0xCE ∨ i = 0x9F ∨ i = 0x1D ∨ i = 0x704 ∨ i = 0x70B ∨ i = 0x70E) :
    moveIn 0xF7 ram i = ram i := by
  have hp : ctrlPre_ram ram i = ram i := by
    apply ctrlPre_ram_frame
    simp only [ctrlPre_writes]
    revert hi
    bv_decide (config := { enums := false })
  simp only [moveIn, hp]
  revert hi
  bv_decide (config := { enums := false })

/-! ### State 0 -/

theorem ctrlA0_post_keep (ram prg : UInt16 → UInt8) (i : UInt16) (hi : writtenPost i = false) :
    ctrlA0_ram 0xF7 ram prg i = ms0_ram 0xF5 (moveIn 0xF7 ram) i := by
  rw [Smb.Routine.ModelFrame.ctrlA0_composition]
  exact aux_keep _ _ _ hi

theorem side0_tail (w ram prg : UInt16 → UInt8) (i : UInt16) (hi : writtenTail i = false) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (h : footCheck_pc (bgY (frameR0 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR0 0xF7 ram prg)) prg = 0xDD5E) :
    frame0_side_ram w 0xF7 ram prg i = ctrlA0_ram 0xF7 ram prg i := by
  have e : ctrlJ_s (ctrlA0_s 0xF7) = 0xF5 := by delta ctrlJ_s ctrlA0_s ctrlAux_s ctrlMid_s; rfl
  have e2 : ctrlA0_s 0xF7 = 0xF7 := ctrlA0_s_eq' _
  unfold frame0_side_ram
  rw [ctrlAttr_keep _ _ hi, e, bg_keep _ _ _ _ hi (stack_foot _ _ hc h)]
  show ctrlJ_ram (ctrlA0_s 0xF7) _ i = _
  rw [e2, ctrlJ_keep _ _ hi]

theorem side0_keep (w ram prg : UInt16 → UInt8) (i : UInt16) (hi : written i = false) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (h : footCheck_pc (bgY (frameR0 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR0 0xF7 ram prg)) prg = 0xDD5E) :
    frame0_side_ram w 0xF7 ram prg i = ram i := by
  have hp := post_of_written i hi
  rw [side0_tail w ram prg i (tail_of_post i hp) hc h, ctrlA0_post_keep _ _ _ hp,
    ms0_ram_frame _ _ _ (by simp only [written] at hi; simp only [ms0_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
  exact moveIn_keep ram i hi

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem ms0_714 (sp : UInt8) (ram : UInt16 → UInt8) (h754 : ram 0x754 ≠ 0) (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms0_ram sp ram 0x714 = 0 := by
  simp only [ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem ms0_b5 (sp : UInt8) (ram : UInt16 → UInt8) (hb : ram 0xB5 = 1) (hy : 0x20 ≤ ram 0xCE ∧ ram 0xCE < 0xE0) (hspd : ram 0x9F + 8 < 0x10) (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms0_ram sp ram 0xB5 = 1 := by
  simp only [ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

/-! ### State 1 -/

theorem ctrlA1_post_keep (ram prg : UInt16 → UInt8) (i : UInt16) (hi : writtenPost i = false) :
    ctrlA1_ram 0xF7 ram prg i = ms1_ram 0xF5 (moveIn 0xF7 ram) i := by
  rw [Smb.Routine.ModelFrame.ctrlA1_composition]
  exact aux_keep _ _ _ hi

theorem side1_tail (w ram prg : UInt16 → UInt8) (i : UInt16) (hi : writtenTail i = false) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (h : footCheck_pc (bgY (frameR1 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR1 0xF7 ram prg)) prg = 0xDD5E) :
    frame1_side_ram w 0xF7 ram prg i = ctrlA1_ram 0xF7 ram prg i := by
  have e : ctrlJ_s (ctrlA1_s 0xF7) = 0xF5 := by delta ctrlJ_s ctrlA1_s ctrlAux_s ctrlMid_s; rfl
  have e2 : ctrlA1_s 0xF7 = 0xF7 := ctrlA1_s_eq' _
  unfold frame1_side_ram
  rw [ctrlAttr_keep _ _ hi, e, bg_keep _ _ _ _ hi (stack_foot _ _ hc h)]
  show ctrlJ_ram (ctrlA1_s 0xF7) _ i = _
  rw [e2, ctrlJ_keep _ _ hi]

theorem side1_keep (w ram prg : UInt16 → UInt8) (i : UInt16) (hi : written i = false) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (h : footCheck_pc (bgY (frameR1 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR1 0xF7 ram prg)) prg = 0xDD5E) :
    frame1_side_ram w 0xF7 ram prg i = ram i := by
  have hp := post_of_written i hi
  rw [side1_tail w ram prg i (tail_of_post i hp) hc h, ctrlA1_post_keep _ _ _ hp,
    ms1_ram_frame _ _ _ (by simp only [written] at hi; simp only [ms1_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
  exact moveIn_keep ram i hi

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem ms1_714 (sp : UInt8) (ram : UInt16 → UInt8) (h754 : ram 0x754 ≠ 0) (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms1_ram sp ram 0x714 = 0 := by
  simp only [ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem ms1_b5 (sp : UInt8) (ram : UInt16 → UInt8) (hb : ram 0xB5 = 1) (hy : 0x20 ≤ ram 0xCE ∧ ram 0xCE < 0xE0) (hspd : ram 0x9F + 8 < 0x10) (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms1_ram sp ram 0xB5 = 1 := by
  simp only [ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

/-! ### State 2 -/

theorem ctrlA2_post_keep (ram prg : UInt16 → UInt8) (i : UInt16) (hi : writtenPost i = false) :
    ctrlA2_ram 0xF7 ram prg i = ms2_ram 0xF5 (moveIn 0xF7 ram) i := by
  rw [Smb.Routine.ModelFrame.ctrlA2_composition]
  exact aux_keep _ _ _ hi

theorem side2_tail (w ram prg : UInt16 → UInt8) (i : UInt16) (hi : writtenTail i = false) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (h : footCheck_pc (bgY (frameR2 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR2 0xF7 ram prg)) prg = 0xDD5E) :
    frame2_side_ram w 0xF7 ram prg i = ctrlA2_ram 0xF7 ram prg i := by
  have e : ctrlJ_s (ctrlA2_s 0xF7) = 0xF5 := by delta ctrlJ_s ctrlA2_s ctrlAux_s ctrlMid_s; rfl
  have e2 : ctrlA2_s 0xF7 = 0xF7 := ctrlA2_s_eq' _
  unfold frame2_side_ram
  rw [ctrlAttr_keep _ _ hi, e, bg_keep _ _ _ _ hi (stack_foot _ _ hc h)]
  show ctrlJ_ram (ctrlA2_s 0xF7) _ i = _
  rw [e2, ctrlJ_keep _ _ hi]

theorem side2_keep (w ram prg : UInt16 → UInt8) (i : UInt16) (hi : written i = false) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (h : footCheck_pc (bgY (frameR2 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR2 0xF7 ram prg)) prg = 0xDD5E) :
    frame2_side_ram w 0xF7 ram prg i = ram i := by
  have hp := post_of_written i hi
  rw [side2_tail w ram prg i (tail_of_post i hp) hc h, ctrlA2_post_keep _ _ _ hp,
    ms2_ram_frame _ _ _ (by simp only [written] at hi; simp only [ms2_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
  exact moveIn_keep ram i hi

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem ms2_714 (sp : UInt8) (ram : UInt16 → UInt8) (h754 : ram 0x754 ≠ 0) (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms2_ram sp ram 0x714 = 0 := by
  simp only [ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem ms2_b5 (sp : UInt8) (ram : UInt16 → UInt8) (hb : ram 0xB5 = 1) (hy : 0x20 ≤ ram 0xCE ∧ ram 0xCE < 0xE0) (hspd : ram 0x9F + 8 < 0x10) (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms2_ram sp ram 0xB5 = 1 := by
  simp only [ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

theorem side0_exit (w ram prg : UInt16 → UInt8) (h : Move0Hyps ram) (he : Entry ram)
    (hb : BgClear w (frameS0 0xF7) (frameR0 0xF7 ram prg) prg) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (hf : footCheck_pc (bgY (frameR0 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR0 0xF7 ram prg)) prg = 0xDD5E) :
    Exit ram (frame0_side_ram w 0xF7 ram prg) := by
  have htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6 := by
    simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
  have ht (i : UInt16) (hi : writtenTail i = false) := side0_tail w ram prg i hi hc hf
  generalize hM : ms0_ram 0xF5 (moveIn 0xF7 ram) = M at *
  have hms (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778 ∨ i = 0x755) : M i = ram i := by
    rw [← hM, ms0_ram_frame _ _ _ (by simp only [ms0_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
    exact pre_other ram i (by rcases hi with h | h | h | h | h | h | h <;> simp [h])
  have hmid (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778 ∨ i = 0x755) : ctrlMid_ram M i = ram i := by
    rw [ctrlMid_ram_frame _ _ (by simp only [ctrlMid_writes]; revert hi; bv_decide (config := { enums := false }))]
    exact hms i hi
  have hA : ctrlA0_ram 0xF7 ram prg = ctrlAux_ram (ctrlMid_s 0xF7) (ctrlMid_ram M) prg := by
    rw [← hM]; exact Smb.Routine.ModelFrame.ctrlA0_composition 0xF7 ram prg
  have hedge (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778) : frame0_side_ram w 0xF7 ram prg i = ram i := by
    rw [ht i (by simp only [writtenTail]; revert hi; bv_decide (config := { enums := false })), hA,
      aux_edge _ _ _ i hi (by rw [hmid 0x755 (by simp)]; exact he.scroll)]
    exact hmid i (by rcases hi with h | h | h | h | h | h <;> simp [h])
  have hbg := bgSide_490 w (frameS0 0xF7) (frameR0 0xF7 ram prg) prg hb htbl
  have h86 : frame0_side_ram w 0xF7 ram prg 0x86 = scrollRam (ctrlMid_s 0xF7) (auxIn (ctrlMid_s 0xF7) (ctrlMid_ram M)) 0x86 := by
    have hF : frame0_side_ram w 0xF7 ram prg 0x86 = afterFoot (lands prg (bgRam (frameR0 0xF7 ram prg)) (bgY (frameR0 0xF7 ram prg))) (bgRam (frameR0 0xF7 ram prg)) 0x86 := by
      unfold frame0_side_ram
      rw [attr_other _ _ (by decide)]
      exact bgSide_cell w (frameS0 0xF7) _ prg 0x86 (by simp [cellOf]) htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
        (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
    have hR : bgRam (frameR0 0xF7 ram prg) 0x86 = ctrlA0_ram 0xF7 ram prg 0x86 := by
      rw [bgRam_cell _ hb.go 0x86 (by decide) (by decide)]
      show ctrlJ_ram (ctrlA0_s 0xF7) (ctrlA0_ram 0xF7 ram prg) 0x86 = _
      exact ctrlJ_cell _ _ 0x86 (by simp [cellOf])
    have hL : afterFoot (lands prg (bgRam (frameR0 0xF7 ram prg)) (bgY (frameR0 0xF7 ram prg))) (bgRam (frameR0 0xF7 ram prg)) 0x86 = bgRam (frameR0 0xF7 ram prg) 0x86 := by
      simp [afterFoot]
    rw [hF, hL, hR, hA]
    exact Smb.Routine.HorizontalLimit.ctrlAux_x _ _ _ _ (by decide)
  have hmove := h.moveIn 0xF7
  refine ⟨?_, ?_, ?_, ?_, hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), ?_, ?_, ?_, ?_⟩
  · intro i hi
    subst hM
    exact side0_keep w ram prg i hi hc hf
  · rw [ht _ (by decide), ctrlA0_post_keep _ _ _ (by decide)]
    exact ms0_714 _ _ (by rw [pre_other ram _ (by simp)]; exact he.small) hmove.ht hmove.hs hmove.hz hmove.hjs
  · rw [ht _ (by decide), ctrlA0_post_keep _ _ _ (by decide)]
    refine ms0_b5 _ _ (by rw [pre_other ram _ (by simp)]; exact he.high) (by rw [pre_other ram _ (by simp)]; exact he.y) (by rw [pre_other ram _ (by simp)]; exact he.speed) hmove.ht hmove.hs hmove.hz hmove.hjs
  · rw [ht _ (by decide), hA, Smb.Routine.HorizontalLimit.ctrlAux_x _ _ _ _ (by decide)]
    simp [scrollRam]
  · unfold frame0_side_ram
    rw [attr_other _ _ (by decide)]
    exact hbg.1
  · unfold frame0_side_ram
    rw [attr_other _ _ (by decide)]
    refine hbg.2.trans ?_
    exact hb.js
  · rw [ht _ (by decide), hA, aux_rel, h86, scroll_cell _ _ 0x71C (by simp)
      (by rw [auxIn_at _ _ 0x755 (by decide)]; rw [hmid 0x755 (by simp)]; exact he.scroll), auxIn_at _ _ 0x71C (by decide), hmid 0x71C (by simp)]
  · have hI := moveIn_input 0xF7 ram h.ha h.he
    rw [ht _ (by decide), ctrlA0_post_keep _ _ _ (by decide), ms0_ram_frame _ _ _ (by simp only [ms0_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; decide),
      a_of_input _ hI.2, hI.1]

theorem side1_exit (w ram prg : UInt16 → UInt8) (h : Move1Hyps ram) (he : Entry ram)
    (hb : BgClear w (frameS1 0xF7) (frameR1 0xF7 ram prg) prg) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (hf : footCheck_pc (bgY (frameR1 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR1 0xF7 ram prg)) prg = 0xDD5E) :
    Exit ram (frame1_side_ram w 0xF7 ram prg) := by
  have htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6 := by
    simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
  have ht (i : UInt16) (hi : writtenTail i = false) := side1_tail w ram prg i hi hc hf
  generalize hM : ms1_ram 0xF5 (moveIn 0xF7 ram) = M at *
  have hms (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778 ∨ i = 0x755) : M i = ram i := by
    rw [← hM, ms1_ram_frame _ _ _ (by simp only [ms1_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
    exact pre_other ram i (by rcases hi with h | h | h | h | h | h | h <;> simp [h])
  have hmid (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778 ∨ i = 0x755) : ctrlMid_ram M i = ram i := by
    rw [ctrlMid_ram_frame _ _ (by simp only [ctrlMid_writes]; revert hi; bv_decide (config := { enums := false }))]
    exact hms i hi
  have hA : ctrlA1_ram 0xF7 ram prg = ctrlAux_ram (ctrlMid_s 0xF7) (ctrlMid_ram M) prg := by
    rw [← hM]; exact Smb.Routine.ModelFrame.ctrlA1_composition 0xF7 ram prg
  have hedge (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778) : frame1_side_ram w 0xF7 ram prg i = ram i := by
    rw [ht i (by simp only [writtenTail]; revert hi; bv_decide (config := { enums := false })), hA,
      aux_edge _ _ _ i hi (by rw [hmid 0x755 (by simp)]; exact he.scroll)]
    exact hmid i (by rcases hi with h | h | h | h | h | h <;> simp [h])
  have hbg := bgSide_490 w (frameS1 0xF7) (frameR1 0xF7 ram prg) prg hb htbl
  have h86 : frame1_side_ram w 0xF7 ram prg 0x86 = scrollRam (ctrlMid_s 0xF7) (auxIn (ctrlMid_s 0xF7) (ctrlMid_ram M)) 0x86 := by
    have hF : frame1_side_ram w 0xF7 ram prg 0x86 = afterFoot (lands prg (bgRam (frameR1 0xF7 ram prg)) (bgY (frameR1 0xF7 ram prg))) (bgRam (frameR1 0xF7 ram prg)) 0x86 := by
      unfold frame1_side_ram
      rw [attr_other _ _ (by decide)]
      exact bgSide_cell w (frameS1 0xF7) _ prg 0x86 (by simp [cellOf]) htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
        (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
    have hR : bgRam (frameR1 0xF7 ram prg) 0x86 = ctrlA1_ram 0xF7 ram prg 0x86 := by
      rw [bgRam_cell _ hb.go 0x86 (by decide) (by decide)]
      show ctrlJ_ram (ctrlA1_s 0xF7) (ctrlA1_ram 0xF7 ram prg) 0x86 = _
      exact ctrlJ_cell _ _ 0x86 (by simp [cellOf])
    have hL : afterFoot (lands prg (bgRam (frameR1 0xF7 ram prg)) (bgY (frameR1 0xF7 ram prg))) (bgRam (frameR1 0xF7 ram prg)) 0x86 = bgRam (frameR1 0xF7 ram prg) 0x86 := by
      simp [afterFoot]
    rw [hF, hL, hR, hA]
    exact Smb.Routine.HorizontalLimit.ctrlAux_x _ _ _ _ (by decide)
  have hmove := h.moveIn 0xF7
  refine ⟨?_, ?_, ?_, ?_, hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), ?_, ?_, ?_, ?_⟩
  · intro i hi
    subst hM
    exact side1_keep w ram prg i hi hc hf
  · rw [ht _ (by decide), ctrlA1_post_keep _ _ _ (by decide)]
    exact ms1_714 _ _ (by rw [pre_other ram _ (by simp)]; exact he.small) hmove.ht hmove.hs hmove.hz hmove.hjs
  · rw [ht _ (by decide), ctrlA1_post_keep _ _ _ (by decide)]
    refine ms1_b5 _ _ (by rw [pre_other ram _ (by simp)]; exact he.high) (by rw [pre_other ram _ (by simp)]; exact he.y) (by rw [pre_other ram _ (by simp)]; exact he.speed) hmove.ht hmove.hs hmove.hz hmove.hjs
  · rw [ht _ (by decide), hA, Smb.Routine.HorizontalLimit.ctrlAux_x _ _ _ _ (by decide)]
    simp [scrollRam]
  · unfold frame1_side_ram
    rw [attr_other _ _ (by decide)]
    exact hbg.1
  · unfold frame1_side_ram
    rw [attr_other _ _ (by decide)]
    refine hbg.2.trans ?_
    exact hb.js
  · rw [ht _ (by decide), hA, aux_rel, h86, scroll_cell _ _ 0x71C (by simp)
      (by rw [auxIn_at _ _ 0x755 (by decide)]; rw [hmid 0x755 (by simp)]; exact he.scroll), auxIn_at _ _ 0x71C (by decide), hmid 0x71C (by simp)]
  · have hI := moveIn_input 0xF7 ram h.ha h.he
    rw [ht _ (by decide), ctrlA1_post_keep _ _ _ (by decide), ms1_ram_frame _ _ _ (by simp only [ms1_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; decide),
      a_of_input _ hI.2, hI.1]

theorem side2_exit (w ram prg : UInt16 → UInt8) (h : Move2Hyps ram) (he : Entry ram)
    (hb : BgClear w (frameS2 0xF7) (frameR2 0xF7 ram prg) prg) (hc : CodeAt prg 0x5F96 climbTilesCode)
    (hf : footCheck_pc (bgY (frameR2 0xF7 ram prg)) (bgSize_s (bgPre_s 0xF5)) (bgRam (frameR2 0xF7 ram prg)) prg = 0xDD5E) :
    Exit ram (frame2_side_ram w 0xF7 ram prg) := by
  have htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6 := by
    simp only [CodeAt, climbTilesCode, UInt16.reduceAdd] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
  have ht (i : UInt16) (hi : writtenTail i = false) := side2_tail w ram prg i hi hc hf
  generalize hM : ms2_ram 0xF5 (moveIn 0xF7 ram) = M at *
  have hms (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778 ∨ i = 0x755) : M i = ram i := by
    rw [← hM, ms2_ram_frame _ _ _ (by simp only [ms2_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
    exact pre_other ram i (by rcases hi with h | h | h | h | h | h | h <;> simp [h])
  have hmid (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778 ∨ i = 0x755) : ctrlMid_ram M i = ram i := by
    rw [ctrlMid_ram_frame _ _ (by simp only [ctrlMid_writes]; revert hi; bv_decide (config := { enums := false }))]
    exact hms i hi
  have hA : ctrlA2_ram 0xF7 ram prg = ctrlAux_ram (ctrlMid_s 0xF7) (ctrlMid_ram M) prg := by
    rw [← hM]; exact Smb.Routine.ModelFrame.ctrlA2_composition 0xF7 ram prg
  have hedge (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x73D ∨ i = 0x778) : frame2_side_ram w 0xF7 ram prg i = ram i := by
    rw [ht i (by simp only [writtenTail]; revert hi; bv_decide (config := { enums := false })), hA,
      aux_edge _ _ _ i hi (by rw [hmid 0x755 (by simp)]; exact he.scroll)]
    exact hmid i (by rcases hi with h | h | h | h | h | h <;> simp [h])
  have hbg := bgSide_490 w (frameS2 0xF7) (frameR2 0xF7 ram prg) prg hb htbl
  have h86 : frame2_side_ram w 0xF7 ram prg 0x86 = scrollRam (ctrlMid_s 0xF7) (auxIn (ctrlMid_s 0xF7) (ctrlMid_ram M)) 0x86 := by
    have hF : frame2_side_ram w 0xF7 ram prg 0x86 = afterFoot (lands prg (bgRam (frameR2 0xF7 ram prg)) (bgY (frameR2 0xF7 ram prg))) (bgRam (frameR2 0xF7 ram prg)) 0x86 := by
      unfold frame2_side_ram
      rw [attr_other _ _ (by decide)]
      exact bgSide_cell w (frameS2 0xF7) _ prg 0x86 (by simp [cellOf]) htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
        (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
    have hR : bgRam (frameR2 0xF7 ram prg) 0x86 = ctrlA2_ram 0xF7 ram prg 0x86 := by
      rw [bgRam_cell _ hb.go 0x86 (by decide) (by decide)]
      show ctrlJ_ram (ctrlA2_s 0xF7) (ctrlA2_ram 0xF7 ram prg) 0x86 = _
      exact ctrlJ_cell _ _ 0x86 (by simp [cellOf])
    have hL : afterFoot (lands prg (bgRam (frameR2 0xF7 ram prg)) (bgY (frameR2 0xF7 ram prg))) (bgRam (frameR2 0xF7 ram prg)) 0x86 = bgRam (frameR2 0xF7 ram prg) 0x86 := by
      simp [afterFoot]
    rw [hF, hL, hR, hA]
    exact Smb.Routine.HorizontalLimit.ctrlAux_x _ _ _ _ (by decide)
  have hmove := h.moveIn 0xF7
  refine ⟨?_, ?_, ?_, ?_, hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), hedge _ (by simp), ?_, ?_, ?_, ?_⟩
  · intro i hi
    subst hM
    exact side2_keep w ram prg i hi hc hf
  · rw [ht _ (by decide), ctrlA2_post_keep _ _ _ (by decide)]
    exact ms2_714 _ _ (by rw [pre_other ram _ (by simp)]; exact he.small) hmove.ht hmove.hs hmove.hz hmove.hjs
  · rw [ht _ (by decide), ctrlA2_post_keep _ _ _ (by decide)]
    refine ms2_b5 _ _ (by rw [pre_other ram _ (by simp)]; exact he.high) (by rw [pre_other ram _ (by simp)]; exact he.y) (by rw [pre_other ram _ (by simp)]; exact he.speed) hmove.ht hmove.hs hmove.hz hmove.hjs
  · rw [ht _ (by decide), hA, Smb.Routine.HorizontalLimit.ctrlAux_x _ _ _ _ (by decide)]
    simp [scrollRam]
  · unfold frame2_side_ram
    rw [attr_other _ _ (by decide)]
    exact hbg.1
  · unfold frame2_side_ram
    rw [attr_other _ _ (by decide)]
    refine hbg.2.trans ?_
    exact hb.js
  · rw [ht _ (by decide), hA, aux_rel, h86, scroll_cell _ _ 0x71C (by simp)
      (by rw [auxIn_at _ _ 0x755 (by decide)]; rw [hmid 0x755 (by simp)]; exact he.scroll), auxIn_at _ _ 0x71C (by decide), hmid 0x71C (by simp)]
  · have hI := moveIn_input 0xF7 ram h.ha h.he
    rw [ht _ (by decide), ctrlA2_post_keep _ _ _ (by decide), ms2_ram_frame _ _ _ (by simp only [ms2_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; decide),
      a_of_input _ hI.2, hI.1]

/-- State 0: with a clear collision, the position's as `ctrlAux` left it. -/
theorem side0_xpos (w ram prg : UInt16 → UInt8) (hb : BgClear w (frameS0 0xF7) (frameR0 0xF7 ram prg) prg)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6) (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D) :
    frame0_side_ram w 0xF7 ram prg i = ctrlA0_ram 0xF7 ram prg i := by
  have hc : cellOf i := by rcases hi with rfl | rfl <;> simp [cellOf]
  unfold frame0_side_ram
  rw [attr_other _ _ (by rcases hi with rfl | rfl <;> decide)]
  have := bgSide_cell w (frameS0 0xF7) (frameR0 0xF7 ram prg) prg i hc htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
    (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
  refine this.trans ?_
  have ha : afterFoot (lands prg (bgRam (frameR0 0xF7 ram prg)) (bgY (frameR0 0xF7 ram prg))) (bgRam (frameR0 0xF7 ram prg)) i = bgRam (frameR0 0xF7 ram prg) i := by
    rcases hi with rfl | rfl
    · exact aF_86 _ _
    · exact aF_6d _ _
  rw [ha, bgRam_cell _ hb.go i (by rcases hi with rfl | rfl <;> decide) (by rcases hi with rfl | rfl <;> decide)]
  show ctrlJ_ram (ctrlA0_s 0xF7) (ctrlA0_ram 0xF7 ram prg) i = _
  exact ctrlJ_cell _ _ i hc

/-- State 1: with a clear collision, the position's as `ctrlAux` left it. -/
theorem side1_xpos (w ram prg : UInt16 → UInt8) (hb : BgClear w (frameS1 0xF7) (frameR1 0xF7 ram prg) prg)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6) (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D) :
    frame1_side_ram w 0xF7 ram prg i = ctrlA1_ram 0xF7 ram prg i := by
  have hc : cellOf i := by rcases hi with rfl | rfl <;> simp [cellOf]
  unfold frame1_side_ram
  rw [attr_other _ _ (by rcases hi with rfl | rfl <;> decide)]
  have := bgSide_cell w (frameS1 0xF7) (frameR1 0xF7 ram prg) prg i hc htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
    (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
  refine this.trans ?_
  have ha : afterFoot (lands prg (bgRam (frameR1 0xF7 ram prg)) (bgY (frameR1 0xF7 ram prg))) (bgRam (frameR1 0xF7 ram prg)) i = bgRam (frameR1 0xF7 ram prg) i := by
    rcases hi with rfl | rfl
    · exact aF_86 _ _
    · exact aF_6d _ _
  rw [ha, bgRam_cell _ hb.go i (by rcases hi with rfl | rfl <;> decide) (by rcases hi with rfl | rfl <;> decide)]
  show ctrlJ_ram (ctrlA1_s 0xF7) (ctrlA1_ram 0xF7 ram prg) i = _
  exact ctrlJ_cell _ _ i hc

/-- State 2: with a clear collision, the position's as `ctrlAux` left it. -/
theorem side2_xpos (w ram prg : UInt16 → UInt8) (hb : BgClear w (frameS2 0xF7) (frameR2 0xF7 ram prg) prg)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6) (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D) :
    frame2_side_ram w 0xF7 ram prg i = ctrlA2_ram 0xF7 ram prg i := by
  have hc : cellOf i := by rcases hi with rfl | rfl <;> simp [cellOf]
  unfold frame2_side_ram
  rw [attr_other _ _ (by rcases hi with rfl | rfl <;> decide)]
  have := bgSide_cell w (frameS2 0xF7) (frameR2 0xF7 ram prg) prg i hc htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
    (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
  refine this.trans ?_
  have ha : afterFoot (lands prg (bgRam (frameR2 0xF7 ram prg)) (bgY (frameR2 0xF7 ram prg))) (bgRam (frameR2 0xF7 ram prg)) i = bgRam (frameR2 0xF7 ram prg) i := by
    rcases hi with rfl | rfl
    · exact aF_86 _ _
    · exact aF_6d _ _
  rw [ha, bgRam_cell _ hb.go i (by rcases hi with rfl | rfl <;> decide) (by rcases hi with rfl | rfl <;> decide)]
  show ctrlJ_ram (ctrlA2_s 0xF7) (ctrlA2_ram 0xF7 ram prg) i = _
  exact ctrlJ_cell _ _ i hc

end Smb.Routine.LaunchExit
