import Smb.Routine.ModelBridge

/-!
# The movement model across `PlayerCtrlRoutine`, up to `PlayerBGCollision`

`ModelBridge` is about `PlayerMovementSubs` from its own entry. Here the input cells come from `$6FC` by the code before it, and the code after it sets the moving direction and otherwise leaves the model's cells alone. `$0D` is written later still, at `SaveAB`.
-/
namespace Smb.Routine.ModelFrame
open Smb.Routine.PlayerFramePosition Smb.Routine.ModelBridge Smb.Routine.HorizontalLimit
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The bytes the model reads that `PlayerCtrlRoutine` doesn't set before `PlayerMovementSubs`. -/
def preByte (i : UInt16) : Bool :=
  i == 0x57 || i == 0x705 || i == 0x700 || i == 0x33 || i == 0x45 || i == 0x1D || i == 0x783 || i == 0x703 || i == 0xCE || i == 0x416 ||
  i == 0x9F || i == 0x433 || i == 0x709 || i == 0x70A || i == 0x708 || i == 0x706 || i == 0x0D ||
  i == 0x704 || i == 0x70B || i == 0x70E || i == 0x74E || i == 0x490 || i == 0x0E || i == 0x754 || i == 0x47D

theorem moveIn_pre (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) (hi : preByte i = true) : moveIn sp ram i = ram i := by
  have hp : ctrlPre_ram ram i = ram i := by
    apply ctrlPre_ram_frame
    simp only [preByte] at hi
    simp only [ctrlPre_writes]
    bv_decide
  simp only [moveIn, hp]
  simp only [preByte] at hi
  bv_decide

/-- In normal control outside water, `$6FC` isn't touched, and the two input cells are what the model reads. -/
theorem moveIn_input (sp : UInt8) (ram : UInt16 → UInt8) (ha : ram 0x74E ≠ 0) (he : ram 0x0E = 8) :
    moveIn sp ram 0x6FC = ram 0x6FC ∧ InputCells (moveIn sp ram) := by
  have h1 : moveIn sp ram 0x1D = ram 0x1D := moveIn_pre sp ram 0x1D (by decide)
  simp only [InputCells, h1]
  simp only [moveIn, ctrlPre_ram, ctrlPre_c0, ctrlPre_c1, ctrlPre_c2, ctrlPre_c3, ctrlPre_c4, ctrlPre_c5, ctrlPre_c6, ctrlPre_c7, ctrlPre_c8, ctrlPre_c9]
  sym_exec [bne] at *
  fun_congr
  bv_decide (config := { enums := false })

theorem cellsOf_moveIn (sp : UInt8) (ram : UInt16 → UInt8) : cellsOf (moveIn sp ram) = cellsOf ram := by
  simp only [cellsOf, moveIn_pre sp ram 0x57 (by decide), moveIn_pre sp ram 0x705 (by decide), moveIn_pre sp ram 0x700 (by decide), moveIn_pre sp ram 0x33 (by decide), moveIn_pre sp ram 0x45 (by decide), moveIn_pre sp ram 0x1D (by decide), moveIn_pre sp ram 0x783 (by decide), moveIn_pre sp ram 0x703 (by decide), moveIn_pre sp ram 0xCE (by decide), moveIn_pre sp ram 0x416 (by decide), moveIn_pre sp ram 0x9F (by decide), moveIn_pre sp ram 0x433 (by decide), moveIn_pre sp ram 0x709 (by decide), moveIn_pre sp ram 0x70A (by decide), moveIn_pre sp ram 0x708 (by decide), moveIn_pre sp ram 0x706 (by decide), moveIn_pre sp ram 0xD (by decide)]

theorem inOfRam_moveIn (sp : UInt8) (ram : UInt16 → UInt8) (h : moveIn sp ram 0x6FC = ram 0x6FC) : inOfRam (moveIn sp ram) = inOfRam ram := by
  simp only [inOfRam, h, moveIn_pre sp ram 0x783 (by decide)]

/-- What the code after `PlayerMovementSubs` leaves alone. -/
def postByte (i : UInt16) : Bool :=
  i == 0x705 || i == 0x700 || i == 0x33 || i == 0x1D || i == 0x783 || i == 0x703 || i == 0xCE || i == 0x416 ||
  i == 0x9F || i == 0x433 || i == 0x709 || i == 0x70A || i == 0x708 || i == 0x706 || i == 0x0D

theorem ctrlA0_composition (sp : UInt8) (ram prg : UInt16 → UInt8) :
    ctrlA0_ram sp ram prg = ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms0_ram (sp + 254) (moveIn sp ram))) prg := by
  unfold ctrlA0_ram moveIn
  simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]

theorem ctrlA0_post (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hi : postByte i = true) :
    ctrlA0_ram sp ram prg i = ms0_ram (sp + 254) (moveIn sp ram) i := by
  rw [ctrlA0_composition]
  have ha : ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms0_ram (sp + 254) (moveIn sp ram))) prg i =
      ctrlMid_ram (ms0_ram (sp + 254) (moveIn sp ram)) i := by
    apply ctrlAux_ram_frame
    sym_exec [postByte] at hi
    sym_exec [ctrlAux_writes, absIdx]
    bv_decide
  rw [ha]
  apply ctrlMid_ram_frame
  simp only [postByte] at hi
  simp only [ctrlMid_writes]
  bv_decide

theorem ctrlA1_composition (sp : UInt8) (ram prg : UInt16 → UInt8) :
    ctrlA1_ram sp ram prg = ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms1_ram (sp + 254) (moveIn sp ram))) prg := by
  unfold ctrlA1_ram moveIn
  simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]

theorem ctrlA1_post (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hi : postByte i = true) :
    ctrlA1_ram sp ram prg i = ms1_ram (sp + 254) (moveIn sp ram) i := by
  rw [ctrlA1_composition]
  have ha : ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms1_ram (sp + 254) (moveIn sp ram))) prg i =
      ctrlMid_ram (ms1_ram (sp + 254) (moveIn sp ram)) i := by
    apply ctrlAux_ram_frame
    sym_exec [postByte] at hi
    sym_exec [ctrlAux_writes, absIdx]
    bv_decide
  rw [ha]
  apply ctrlMid_ram_frame
  simp only [postByte] at hi
  simp only [ctrlMid_writes]
  bv_decide

theorem ctrlA2_composition (sp : UInt8) (ram prg : UInt16 → UInt8) :
    ctrlA2_ram sp ram prg = ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms2_ram (sp + 254) (moveIn sp ram))) prg := by
  unfold ctrlA2_ram moveIn
  simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]

theorem ctrlA2_post (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hi : postByte i = true) :
    ctrlA2_ram sp ram prg i = ms2_ram (sp + 254) (moveIn sp ram) i := by
  rw [ctrlA2_composition]
  have ha : ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms2_ram (sp + 254) (moveIn sp ram))) prg i =
      ctrlMid_ram (ms2_ram (sp + 254) (moveIn sp ram)) i := by
    apply ctrlAux_ram_frame
    sym_exec [postByte] at hi
    sym_exec [ctrlAux_writes, absIdx]
    bv_decide
  rw [ha]
  apply ctrlMid_ram_frame
  simp only [postByte] at hi
  simp only [ctrlMid_writes]
  bv_decide

/-- Away from the screen's edges, `ScrollHandler` leaves Mario's speed and position alone. -/
theorem scroll_keep (sp : UInt8) (r : UInt16 → UInt8) (i : UInt16)
    (hi : i = 0x57 ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400)
    (he : edgeR r = leftL r + 255) (hn : 8 ≤ pixelP r - leftL r) (hf : pixelP r - leftL r ≤ 0xD0)
    (hp : r 0x6FF ≤ 3 ∨ 0xFC ≤ r 0x6FF) (hq : r 0x3A1 = 0) : scrollRam sp r i = r i := by
  simp only [edgeR, leftL, pixelP, pos16] at he hn hf
  rcases hi with rfl | rfl | rfl | rfl <;>
  · sym_exec [scrollRam, gxoRam, scrMid, clampLeft, clampRight, stopsSpeed, scrBits, gxoBits, gxoR, gxoL, offBits, edgePageDiff,
      objX, objPage, scrLeftX, scrLeftPage, scrRightX, scrRightPage, scrolls, scrAmt, scrPxs, clampX, clampPage, bne, dummyIdx, forceIdx, pageIdx, posIdx, speedIdx] at *
    all_goals
      fun_congr
      bv_decide (config := { enums := false })

/-! ## The foot check -/

/-- What the foot check does to the model's cells, when it lands or doesn't. -/
def afterFoot (L : Bool) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif L && i == 0xCE then ram 0xCE &&& 0xF0
  else bif L && (i == 0x9F || i == 0x433 || i == 0x1D) then 0
  else ram i

/-- The climb table's entry for a tile's group, as `chkFoot_ram` reads it. -/
abbrev climbAt (prg : UInt16 → UInt8) (a : UInt8) : UInt8 :=
  prg ((57238 : UInt16) + (((a &&& 192) <<< 1 <<< 1 ||| (a &&& 192) >>> 7 &&& 1) <<< 1 ||| (a &&& 192) <<< 1 >>> 7 &&& 1).toUInt16 &&& 32767)

set_option maxHeartbeats 8000000 in
theorem chkFoot_cell (a sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (hi : i = 0xCE ∨ i = 0x9F ∨ i = 0x433 ∨ i = 0x1D ∨ i = 0x57 ∨ i = 0x705 ∨ i = 0x700 ∨ i = 0x33 ∨ i = 0x45 ∨ i = 0x783 ∨ i = 0x703 ∨
      i = 0x416 ∨ i = 0x70A ∨ i = 0x708 ∨ i = 0x706 ∨ i = 0x709 ∨ i = 0x0D ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400)
    (hp : climbAt prg a = climbExt a)
    (hs : (a != 0x67 && a != 0x68) = true)
    (hn : (footGround a ram && 5 ≤ ram 4) = false) (he : ram 0x70E = 0) (hd : (footGround a ram && ram 4 < 5 && pipeDown ram) = false) :
    chkFoot_ram a sp ram prg i = afterFoot (footGround a ram && ram 4 < 5) ram i := by
  simp only [footGround, climbable, climbExt, pipeDown, bne, climbAt] at hn hs hd hp
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [chkFoot_ram, chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, chkFoot_c5, chkFoot_c6, chkFoot_c7, chkFoot_c8, chkFoot_c9, chkFoot_c10, chkFoot_c11, chkFoot_c12, chkFoot_c13, chkFoot_c14, chkFoot_c15, chkFoot_c16, chkFoot_c17, chkFoot_c18, chkFoot_c19, chkFoot_c20, chkFoot_c21, chkFoot_c22, chkFoot_c23, chkFoot_c24, afterFoot, footGround]
    sym_exec [climbable, climbExt, pipeDown, bne] at *
    all_goals
      fun_congr
      bv_decide (config := { enums := false })

set_option maxHeartbeats 8000000 in
/-- With nothing above the head, the head check leaves the vertical speed alone. -/
theorem headPart_speed (y sp : UInt8) (ram prg : UInt16 → UInt8) (hb : headBlocked prg ram y = false) :
    headPart_ram y sp ram prg 0x9F = ram 0x9F := by
  simp only [headBlocked, headProbed, headTile, coinTile, solidTile, bbOffset, bne] at hb
  simp only [headPart_ram, headPart_c0, headPart_c1, headPart_c2, headPart_c3, headPart_c4, headPart_c5, headPart_c6, headPart_c7, headPart_c8, headPart_c9, headPart_c10, headPart_c11, headPart_c12, headPart_c13, headPart_c14, headPart_c15, headPart_c16, headPart_c17, headPart_c18, headPart_c19, headPart_c20]
  sym_exec [bbFlags, bbRam, bbYPos, bbYAdd, bbNybble, bbXPos, bbPage, bbTile_wr, bbRow_wr, bbLo_wr, bbXSum_wr, bbColumn_wr, bbTile_wrs, bbRow_wrs, bbLo_wrs, bbXSum_wrs, bbColumn_wrs, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

set_option maxHeartbeats 8000000 in
/-- The foot check as a whole, when it doesn't impede: nothing overhead, and no coin, axe, spring or pipe underfoot. -/
theorem foot_cell (y sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16)
    (hi : i = 0xCE ∨ i = 0x9F ∨ i = 0x433 ∨ i = 0x1D ∨ i = 0x57 ∨ i = 0x705 ∨ i = 0x700 ∨ i = 0x33 ∨ i = 0x45 ∨ i = 0x783 ∨ i = 0x703 ∨
      i = 0x416 ∨ i = 0x70A ∨ i = 0x708 ∨ i = 0x706 ∨ i = 0x709 ∨ i = 0x0D ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : headBlocked prg ram y = false) (hhc : headCoin prg ram y = false) (hc : footCoin prg ram y = false) (ha : footAxeAt prg ram y = false)
    (hp : pipeEntryAt prg ram y = false) (hn : impeded prg ram y = false) (he : ram 0x70E = 0)
    (hs : (footTile prg ram y != 0x67 && footTile prg ram y != 0x68) = true) :
    footCheck_ram y sp ram prg i = afterFoot (lands prg ram y) ram i := by
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
  have hkb := headPart_keeps y sp 4 ram prg (by decide) 0xB (by decide)
  obtain ⟨h0, h1, h2, h3⟩ := htbl
  simp only [headBlocked, footCoin, footAxeAt, pipeEntryAt, impeded, lands, footSolid, footProbed, footTile, footTileL, footTileR, headSpeed, headBumps,
    headProbed, headTile, coinTile, solidTile, climbable, climbExt, bbOffset, bne] at hb hc ha hp hn hs
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [footCheck_ram, footCheck_c0, footCheck_c1, footCheck_c2, footCheck_c3, footCheck_c4, footCheck_c5, footCheck_c6, footCheck_c7, footCheck_c8, footCheck_c9, footCheck_c10, footCheck_c11, footCheck_c12, footCheck_c13, footCheck_c14, chkFoot_ram, chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, chkFoot_c5, chkFoot_c6, chkFoot_c7, chkFoot_c8, chkFoot_c9, chkFoot_c10, chkFoot_c11, chkFoot_c12, chkFoot_c13, chkFoot_c14, chkFoot_c15, chkFoot_c16, chkFoot_c17, chkFoot_c18, chkFoot_c19, chkFoot_c20, chkFoot_c21, chkFoot_c22, chkFoot_c23, afterFoot, footGround, lands, footSolid, footProbed, footTile, footTileL, footTileR, headSpeed, headBumps, headBlocked, headProbed, headTile, coinTile, solidTile, bbOffset]
    sym_exec [hkd, hkp1, hkp2, hkp3, footAxe, hhit, hhc, footGround, climbable, climbExt, pipeDown, bne, hsp, htile, hkce, hk433, hk1d, hk57, hk705, hk700, hk33, hk45, hk783, hk703, hk416, hk70a, hk708, hk706, hk709, hk70e, hkb] at *
    all_goals
      fun_congr
      bv_decide (config := { enums := false })

set_option maxHeartbeats 8000000 in
/-- The foot check goes on to the side check. -/
theorem foot_pc (y sp : UInt8) (ram prg : UInt16 → UInt8)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : headBlocked prg ram y = false) (hhc : headCoin prg ram y = false) (hc : footCoin prg ram y = false) (ha : footAxeAt prg ram y = false)
    (hp : pipeEntryAt prg ram y = false) (hn : impeded prg ram y = false) (he : ram 0x70E = 0)
    (hs : (footTile prg ram y != 0x67 && footTile prg ram y != 0x68) = true) :
    footCheck_pc y sp ram prg = 0xDD5E := by
  have hsp := headPart_speed y sp ram prg hb
  have htile := fun k => headPart_tile y sp 4 ram prg (by decide) k
  have hhit : headHit prg ram y = false := by simp [headHit, hb]
  have hk1 := headPart_keeps y sp 4 ram prg (by decide) 0xCE (by decide)
  have hk2 := headPart_keeps y sp 4 ram prg (by decide) 0x70E (by decide)
  have hk3 := headPart_keeps y sp 4 ram prg (by decide) 0x0B (by decide)
  obtain ⟨h0, h1, h2, h3⟩ := htbl
  simp only [headBlocked, footCoin, footAxeAt, pipeEntryAt, impeded, lands, footSolid, footProbed, footTile, footTileL, footTileR, headSpeed, headBumps,
    headProbed, headTile, coinTile, solidTile, climbable, climbExt, bbOffset, bne] at hb hc ha hp hn hs
  simp only [footCheck_pc, footCheck_c0, footCheck_c1, footCheck_c2, footCheck_c3, footCheck_c4, footCheck_c5, footCheck_c6, footCheck_c7, footCheck_c8, footCheck_c9, footCheck_c10, footCheck_c11, footCheck_c12, footCheck_c13, footCheck_c14, chkFoot_pc, chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, chkFoot_c5, chkFoot_c6, chkFoot_c7, chkFoot_c8, chkFoot_c9, chkFoot_c10, chkFoot_c11, chkFoot_c12, chkFoot_c13, chkFoot_c14, chkFoot_c15, chkFoot_c16, chkFoot_c17, chkFoot_c18, chkFoot_c19, chkFoot_c20, chkFoot_c21, chkFoot_c22, chkFoot_c23, footGround]
  sym_exec [hk1, hk2, hk3, footAxe, hhit, hhc, footGround, climbable, climbExt, pipeDown, bne, hsp, htile] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

set_option maxHeartbeats 8000000 in
/-- `$EB` after the foot check is the adder offset for Mario's size. -/
theorem foot_eb (y sp : UInt8) (ram prg : UInt16 → UInt8)
    (hpc : footCheck_pc y sp ram prg = 0xDD5E) : footCheck_ram y sp ram prg 0xEB = prg ((0xE3AD + y.toUInt16) &&& 0x7FFF) := by
  have hb := headPart_eb y sp ram prg
  simp only [footCheck_pc, footCheck_ram, footCheck_c0, footCheck_c1, footCheck_c2, footCheck_c3, footCheck_c4, footCheck_c5, footCheck_c6, footCheck_c7, footCheck_c8, footCheck_c9, footCheck_c10, footCheck_c11, footCheck_c12, footCheck_c13, footCheck_c14, chkFoot_pc, chkFoot_ram, chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, chkFoot_c5, chkFoot_c6, chkFoot_c7, chkFoot_c8, chkFoot_c9, chkFoot_c10, chkFoot_c11, chkFoot_c12, chkFoot_c13, chkFoot_c14, chkFoot_c15, chkFoot_c16, chkFoot_c17, chkFoot_c18, chkFoot_c19, chkFoot_c20, chkFoot_c21, chkFoot_c22, chkFoot_c23] at hpc ⊢
  sym_exec [hb, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

/-! ## The rest of `PlayerBGCollision` -/

/-- The prologue, on the way to the foot check: a state of 0 or 3 becomes 2, and `$490` is set. Nothing else the model reads changes. -/
theorem bgPre_cell (ram : UInt16 → UInt8) (i : UInt16) (hgo : bgPre_pc ram = 0xDC98) (hne : i ≠ 0x1D) (hne2 : i ≠ 0x490) :
    bgPre_ram ram i = ram i := by
  apply bgPre_ram_frame
  simp only [bgPre_writes]
  bv_decide (config := { enums := false })

theorem bgPre_st (ram : UInt16 → UInt8) (hgo : bgPre_pc ram = 0xDC98) (hs : ram 0x704 = 0) (ht : ram 0x1D ≤ 2) :
    bgPre_ram ram 0x1D = bif ram 0x1D == 0 then 2 else ram 0x1D := by
  simp only [bgPre_pc, bgPre_ram, bgPre_c0, bgPre_c1, bgPre_c2, bgPre_c3, bgPre_c4, bgPre_c5, bgPre_c6, bgPre_c7, bgPre_c8, bgPre_c9, bgPre_c10, bgPre_c11, bgPre_c12, bgPre_c13] at hgo ⊢
  sym_exec [bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

/-- A side check that finds no wall keeps every byte but its scratch. -/
theorem side_cell (w : UInt16 → UInt8) (sp : UInt8) (prg ram : UInt16 → UInt8) (i : UInt16)
    (hb : sideBlocks prg ram = false) (hs : sideScratch sp i = false) : sideRam w sp prg ram i = ram i := by
  simp [sideRam, hb, hs]

/-! ## A frame with nothing touched but the floor -/

/-- The bytes of `cellsOf`. -/
def cellOf (i : UInt16) : Prop :=
  i = 0xCE ∨ i = 0x9F ∨ i = 0x433 ∨ i = 0x1D ∨ i = 0x57 ∨ i = 0x705 ∨ i = 0x700 ∨ i = 0x33 ∨ i = 0x45 ∨ i = 0x783 ∨ i = 0x703 ∨
    i = 0x416 ∨ i = 0x70A ∨ i = 0x708 ∨ i = 0x706 ∨ i = 0x709 ∨ i = 0x0D ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400

theorem cell_scratch (sp : UInt8) (i : UInt16) (hi : cellOf i) : sideScratch sp i = false := by
  simp only [cellOf] at hi
  simp only [sideScratch, stackAt]
  bv_decide (config := { enums := false })

theorem ctrlAttr_cell (r : UInt16 → UInt8) (i : UInt16) (hi : cellOf i) : ctrlAttr_ram r i = r i := by
  simp only [cellOf] at hi
  sym_exec [ctrlAttr_ram]
  bv_decide (config := { enums := false })

theorem ctrlJ_cell (sp : UInt8) (r : UInt16 → UInt8) (i : UInt16) (hi : cellOf i) : ctrlJ_ram sp r i = r i := by
  simp only [cellOf] at hi
  sym_exec [ctrlJ_ram]
  bv_decide (config := { enums := false })

/-- `PlayerBGCollision`'s end, on the model's cells: what the foot check leaves, with the side check finding no wall. -/
theorem bgSide_cell (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hi : cellOf i)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : headBlocked prg (bgRam ram) (bgY ram) = false) (hhc : headCoin prg (bgRam ram) (bgY ram) = false)
    (hc : footCoin prg (bgRam ram) (bgY ram) = false) (ha : footAxeAt prg (bgRam ram) (bgY ram) = false)
    (hp : pipeEntryAt prg (bgRam ram) (bgY ram) = false) (hn : impeded prg (bgRam ram) (bgY ram) = false)
    (he : bgRam ram 0x70E = 0)
    (hs : (footTile prg (bgRam ram) (bgY ram) != 0x67 && footTile prg (bgRam ram) (bgY ram) != 0x68) = true)
    (hw : sideBlocks prg (bgFootRam sp prg ram) = false) :
    bgSide_ram w sp ram prg i = afterFoot (lands prg (bgRam ram) (bgY ram)) (bgRam ram) i := by
  have h := foot_cell (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg i hi htbl hb hhc hc ha hp hn he hs
  simp only [bgSide_ram]
  exact (side_cell w _ prg (bgFootRam sp prg ram) i hw (cell_scratch _ i hi)).trans h

/-! ## The speed and position through `ScrollHandler` -/

/-- What `ScrollHandler` needs of the state it starts from: `XInv`'s facts, away from both edges. -/
structure Away (ram : UInt16 → UInt8) : Prop where
  edge : edgeR ram = leftL ram + 255
  plat : ram 0x3A1 = 0
  near : 12 ≤ pixelP ram - leftL ram
  far : pixelP ram - leftL ram ≤ 0xCD

theorem rel_bounds (P L : UInt16) (x : UInt8) (hn : 12 ≤ P - L) (hf : P - L ≤ 0xCD) (hp : x ≤ 3 ∨ 0xFC ≤ x) :
    8 ≤ P + sext16b x - L ∧ P + sext16b x - L ≤ 0xD0 := by
  simp only [sext16b]
  by_cases h : x < 0x80 <;> simp only [h, decide_true, decide_false, cond_true, cond_false] <;> bv_decide (config := { enums := false })

/-- A move that leaves the edges alone and changes the pixel by at most 3 stays where `scroll_keep` applies. -/
theorem scroll_away (sp : UInt8) (ram M : UInt16 → UInt8) (hA : Away ram) (hm : pixelP M = pixelP ram + sext16b (M 0x6FF))
    (hp : M 0x6FF ≤ 3 ∨ 0xFC ≤ M 0x6FF) (h1 : M 0x71A = ram 0x71A) (h2 : M 0x71B = ram 0x71B) (h3 : M 0x71C = ram 0x71C) (h4 : M 0x71D = ram 0x71D)
    (hq : M 0x3A1 = 0) (i : UInt16) (hi : i = 0x57 ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400) :
    scrollRam sp M i = M i := by
  obtain ⟨he, _, hn, hf⟩ := hA
  have hL : leftL M = leftL ram := by simp only [leftL, h1, h3]
  have hR : edgeR M = edgeR ram := by simp only [edgeR, h2, h4]
  have hb := rel_bounds (pixelP ram) (leftL ram) (M 0x6FF) hn hf hp
  rw [← hm, ← hL] at hb
  exact scroll_keep sp M i hi (by rw [hL, hR]; exact he) hb.1 hb.2 hp hq

/-! ## The frame

From `PlayerCtrlRoutine`'s entry to `PlayerHole`, with nothing overhead, no wall, and a floor or nothing underfoot, the model's cells are where the model says. -/

/-- What the foot check and the prologue do to `M`, when it lands or doesn't. -/
def afterBg (L : Bool) (M : Smb.Movement.S) : Smb.Movement.S :=
  if L then { M with y := M.y &&& 0xF0, vy := 0, vf := 0, st := 0 }
  else if M.st == 0 then { M with st := 2 } else M

theorem modelMove_moveIn (sp : UInt8) (ram : UInt16 → UInt8) (ha : ram 0x74E ≠ 0) (he : ram 0x0E = 8) :
    modelMove (moveIn sp ram) = modelMove ram := by
  simp only [modelMove, cellsOf_moveIn, inOfRam_moveIn sp ram (moveIn_input sp ram ha he).1]

theorem bgRam_cell (R : UInt16 → UInt8) (hgo : bgPre_pc R = 0xDC98) (i : UInt16) (hne : i ≠ 0x1D) (hne2 : i ≠ 0x490) : bgRam R i = R i := by
  show bgSize_ram (bgPre_ram R) i = R i
  rw [show bgSize_ram (bgPre_ram R) i = bgPre_ram R i by delta bgSize_ram; rfl]
  exact bgPre_cell R i hgo hne hne2

theorem ctrlMid_move (M : UInt16 → UInt8) :
    ctrlMid_ram M 0x45 = bif M 0x57 == 0 then M 0x45 else bif M 0x57 < 0x80 then 1 else 2 := by
  simp only [ctrlMid_ram, ctrlMid_c0, ctrlMid_c1, ctrlMid_c2, ctrlMid_c3, ctrlMid_c4, ctrlMid_c5, ctrlMid_c6, ctrlMid_c7]
  sym_exec [bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

theorem ctrlAux_move (sp : UInt8) (ram prg : UInt16 → UInt8) : ctrlAux_ram sp ram prg 0x45 = ram 0x45 := by
  apply ctrlAux_ram_frame
  sym_exec [ctrlAux_writes, absIdx]

set_option maxHeartbeats 8000000 in
theorem ms0_px (sp : UInt8) (ram : UInt16 → UInt8) (hv : speedOk (ram 0x57) = true)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms0_ram sp ram 0x6FF ≤ 3 ∨ 0xFC ≤ ms0_ram sp ram 0x6FF := by
  simp only [ms0_ram, ms0_c0, ms0_c1, ms0_c2, ms0_c3, ms0_c4, ms0_c5, ms0_c6, ms0_c7, ms0_c8, ms0_c9, ms0_c10, ms0_c11, ms0_c12, ms0_c13, ms0_c14, ms0_c15, ms0_c16, ms0_c17, ms0_c18, ms0_c19, ms0_c20, ms0_c21, ms0_c22, ms0_c23, ms0_c24, ms0_c25, ms0_c26, ms0_c27, ms0_c28, ms0_c29, ms0_c30]
  simp only [speedOk] at hv
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

set_option maxHeartbeats 8000000 in
theorem ms1_px (sp : UInt8) (ram : UInt16 → UInt8) (hv : speedOk (ram 0x57) = true)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms1_ram sp ram 0x6FF ≤ 3 ∨ 0xFC ≤ ms1_ram sp ram 0x6FF := by
  simp only [ms1_ram, ms1_c0, ms1_c1, ms1_c2, ms1_c3, ms1_c4, ms1_c5, ms1_c6, ms1_c7, ms1_c8, ms1_c9, ms1_c10, ms1_c11, ms1_c12, ms1_c13, ms1_c14, ms1_c15, ms1_c16, ms1_c17, ms1_c18, ms1_c19, ms1_c20, ms1_c21, ms1_c22, ms1_c23, ms1_c24, ms1_c25, ms1_c26, ms1_c27, ms1_c28, ms1_c29, ms1_c30]
  simp only [speedOk] at hv
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

set_option maxHeartbeats 8000000 in
theorem ms2_px (sp : UInt8) (ram : UInt16 → UInt8) (hv : speedOk (ram 0x57) = true)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ms2_ram sp ram 0x6FF ≤ 3 ∨ 0xFC ≤ ms2_ram sp ram 0x6FF := by
  simp only [ms2_ram, ms2_c0, ms2_c1, ms2_c2, ms2_c3, ms2_c4, ms2_c5, ms2_c6]
  simp only [speedOk] at hv
  sym_exec [startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam, gravityVel, gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, frictionAbs, frictionForce, skidStops, tbl3, xSpeedClass, xFrictionClass, xRunning, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx, pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx, jumpYSpeed, jumpClass, tbl7, jumpMForce, fallMForce, initMForce, bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

/-- State 0: the model's cells before collision, at `PlayerBGCollision`. -/
structure Move0Hyps (ram : UInt16 → UInt8) : Prop where
  ht : ram 0x1D = 0
  hs : ram 0x704 = 0
  hz : ram 0x70B = 0
  hjs : ram 0x70E = 0
  hspd : ram 0x9F + 0x40 < 0x80
  he : ram 0x0E = 8
  ha : ram 0x74E ≠ 0
  hc : ram 0x490 = 0xFF

theorem Move0Hyps.moveIn {ram : UInt16 → UInt8} (h : Move0Hyps ram) (sp : UInt8) : Move0Hyps (PlayerFramePosition.moveIn sp ram) where
  ht := by rw [moveIn_pre sp ram 0x1D (by decide)]; exact h.ht
  hs := by rw [moveIn_pre sp ram 0x704 (by decide)]; exact h.hs
  hz := by rw [moveIn_pre sp ram 0x70B (by decide)]; exact h.hz
  hjs := by rw [moveIn_pre sp ram 0x70E (by decide)]; exact h.hjs
  hspd := by rw [moveIn_pre sp ram 0x9F (by decide)]; exact h.hspd
  he := by rw [moveIn_pre sp ram 0x0E (by decide)]; exact h.he
  ha := by rw [moveIn_pre sp ram 0x74E (by decide)]; exact h.ha
  hc := by rw [moveIn_pre sp ram 0x490 (by decide)]; exact h.hc

theorem ctrlA0_f (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x705 = (modelMove ram).f := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x705 (by decide), Smb.Routine.ModelBridge.ms0_f (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_abs (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x700 = (modelMove ram).abs := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x700 (by decide), Smb.Routine.ModelBridge.ms0_abs (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_face (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x33 = (modelMove ram).face := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x33 (by decide), Smb.Routine.ModelBridge.ms0_face (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_t783 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x783 = (modelMove ram).t783 := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x783 (by decide), Smb.Routine.ModelBridge.ms0_t783 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_r703 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x703 = (modelMove ram).r703 := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x703 (by decide), Smb.Routine.ModelBridge.ms0_r703 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_y (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0xCE = (modelMove ram).y := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0xCE (by decide), Smb.Routine.ModelBridge.ms0_y (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_ysub (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x416 = (modelMove ram).ysub := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x416 (by decide), Smb.Routine.ModelBridge.ms0_ysub (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_vy (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x9F = (modelMove ram).vy := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x9F (by decide), Smb.Routine.ModelBridge.ms0_vy (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_vf (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x433 = (modelMove ram).vf := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x433 (by decide), Smb.Routine.ModelBridge.ms0_vf (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_g (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x709 = (modelMove ram).g := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x709 (by decide), Smb.Routine.ModelBridge.ms0_g (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_gfall (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x70A = (modelMove ram).gfall := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x70A (by decide), Smb.Routine.ModelBridge.ms0_gfall (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_y0 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x708 = (modelMove ram).y0 := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x708 (by decide), Smb.Routine.ModelBridge.ms0_y0 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_rise (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x706 = (modelMove ram).rise := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x706 (by decide), Smb.Routine.ModelBridge.ms0_rise (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_st (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x1D = (modelMove ram).st := by
  have hm := h.moveIn sp
  rw [ctrlA0_post sp ram prg 0x1D (by decide), Smb.Routine.ModelBridge.ms0_st (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

/-- State 1: the model's cells before collision, at `PlayerBGCollision`. -/
structure Move1Hyps (ram : UInt16 → UInt8) : Prop where
  ht : ram 0x1D = 1
  hs : ram 0x704 = 0
  hz : ram 0x70B = 0
  hjs : ram 0x70E = 0
  hspd : ram 0x9F + 0x40 < 0x80
  he : ram 0x0E = 8
  ha : ram 0x74E ≠ 0
  hc : ram 0x490 = 0xFF

theorem Move1Hyps.moveIn {ram : UInt16 → UInt8} (h : Move1Hyps ram) (sp : UInt8) : Move1Hyps (PlayerFramePosition.moveIn sp ram) where
  ht := by rw [moveIn_pre sp ram 0x1D (by decide)]; exact h.ht
  hs := by rw [moveIn_pre sp ram 0x704 (by decide)]; exact h.hs
  hz := by rw [moveIn_pre sp ram 0x70B (by decide)]; exact h.hz
  hjs := by rw [moveIn_pre sp ram 0x70E (by decide)]; exact h.hjs
  hspd := by rw [moveIn_pre sp ram 0x9F (by decide)]; exact h.hspd
  he := by rw [moveIn_pre sp ram 0x0E (by decide)]; exact h.he
  ha := by rw [moveIn_pre sp ram 0x74E (by decide)]; exact h.ha
  hc := by rw [moveIn_pre sp ram 0x490 (by decide)]; exact h.hc

theorem ctrlA1_f (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x705 = (modelMove ram).f := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x705 (by decide), Smb.Routine.ModelBridge.ms1_f (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_abs (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x700 = (modelMove ram).abs := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x700 (by decide), Smb.Routine.ModelBridge.ms1_abs (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_face (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x33 = (modelMove ram).face := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x33 (by decide), Smb.Routine.ModelBridge.ms1_face (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_t783 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x783 = (modelMove ram).t783 := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x783 (by decide), Smb.Routine.ModelBridge.ms1_t783 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_r703 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x703 = (modelMove ram).r703 := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x703 (by decide), Smb.Routine.ModelBridge.ms1_r703 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_y (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0xCE = (modelMove ram).y := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0xCE (by decide), Smb.Routine.ModelBridge.ms1_y (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_ysub (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x416 = (modelMove ram).ysub := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x416 (by decide), Smb.Routine.ModelBridge.ms1_ysub (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_vy (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x9F = (modelMove ram).vy := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x9F (by decide), Smb.Routine.ModelBridge.ms1_vy (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_vf (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x433 = (modelMove ram).vf := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x433 (by decide), Smb.Routine.ModelBridge.ms1_vf (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_g (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x709 = (modelMove ram).g := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x709 (by decide), Smb.Routine.ModelBridge.ms1_g (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_gfall (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x70A = (modelMove ram).gfall := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x70A (by decide), Smb.Routine.ModelBridge.ms1_gfall (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_y0 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x708 = (modelMove ram).y0 := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x708 (by decide), Smb.Routine.ModelBridge.ms1_y0 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_rise (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x706 = (modelMove ram).rise := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x706 (by decide), Smb.Routine.ModelBridge.ms1_rise (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_st (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x1D = (modelMove ram).st := by
  have hm := h.moveIn sp
  rw [ctrlA1_post sp ram prg 0x1D (by decide), Smb.Routine.ModelBridge.ms1_st (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

/-- State 2: the model's cells before collision, at `PlayerBGCollision`. -/
structure Move2Hyps (ram : UInt16 → UInt8) : Prop where
  ht : ram 0x1D = 2
  hs : ram 0x704 = 0
  hz : ram 0x70B = 0
  hjs : ram 0x70E = 0
  hspd : ram 0x9F + 0x40 < 0x80
  he : ram 0x0E = 8
  ha : ram 0x74E ≠ 0
  hc : ram 0x490 = 0xFF

theorem Move2Hyps.moveIn {ram : UInt16 → UInt8} (h : Move2Hyps ram) (sp : UInt8) : Move2Hyps (PlayerFramePosition.moveIn sp ram) where
  ht := by rw [moveIn_pre sp ram 0x1D (by decide)]; exact h.ht
  hs := by rw [moveIn_pre sp ram 0x704 (by decide)]; exact h.hs
  hz := by rw [moveIn_pre sp ram 0x70B (by decide)]; exact h.hz
  hjs := by rw [moveIn_pre sp ram 0x70E (by decide)]; exact h.hjs
  hspd := by rw [moveIn_pre sp ram 0x9F (by decide)]; exact h.hspd
  he := by rw [moveIn_pre sp ram 0x0E (by decide)]; exact h.he
  ha := by rw [moveIn_pre sp ram 0x74E (by decide)]; exact h.ha
  hc := by rw [moveIn_pre sp ram 0x490 (by decide)]; exact h.hc

theorem ctrlA2_f (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x705 = (modelMove ram).f := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x705 (by decide), Smb.Routine.ModelBridge.ms2_f (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_abs (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x700 = (modelMove ram).abs := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x700 (by decide), Smb.Routine.ModelBridge.ms2_abs (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_face (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x33 = (modelMove ram).face := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x33 (by decide), Smb.Routine.ModelBridge.ms2_face (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_t783 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x783 = (modelMove ram).t783 := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x783 (by decide), Smb.Routine.ModelBridge.ms2_t783 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_r703 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x703 = (modelMove ram).r703 := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x703 (by decide), Smb.Routine.ModelBridge.ms2_r703 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_y (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0xCE = (modelMove ram).y := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0xCE (by decide), Smb.Routine.ModelBridge.ms2_y (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_ysub (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x416 = (modelMove ram).ysub := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x416 (by decide), Smb.Routine.ModelBridge.ms2_ysub (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_vy (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x9F = (modelMove ram).vy := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x9F (by decide), Smb.Routine.ModelBridge.ms2_vy (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_vf (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x433 = (modelMove ram).vf := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x433 (by decide), Smb.Routine.ModelBridge.ms2_vf (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_g (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x709 = (modelMove ram).g := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x709 (by decide), Smb.Routine.ModelBridge.ms2_g (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_gfall (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x70A = (modelMove ram).gfall := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x70A (by decide), Smb.Routine.ModelBridge.ms2_gfall (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_y0 (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x708 = (modelMove ram).y0 := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x708 (by decide), Smb.Routine.ModelBridge.ms2_y0 (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_rise (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x706 = (modelMove ram).rise := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x706 (by decide), Smb.Routine.ModelBridge.ms2_rise (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_st (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x1D = (modelMove ram).st := by
  have hm := h.moveIn sp
  rw [ctrlA2_post sp ram prg 0x1D (by decide), Smb.Routine.ModelBridge.ms2_st (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

/-- State 0: speed through `ScrollHandler`, and the moving direction. -/
theorem ctrlA0_v (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    ctrlA0_ram sp ram prg 0x57 = (modelMove ram).v := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms0_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms0_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  generalize hM : ms0_ram (sp + 254) (moveIn sp ram) = M at hx hpx
  have hk (i : UInt16) (hi : carried i = true) : M i = ram i := by
    rw [← hM, Smb.Routine.HorizontalLimit.ms0_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hmid (i : UInt16) (hi : (i != 1177 && i != 69) = true) : ctrlMid_ram M i = M i := by
    apply ctrlMid_ram_frame; simp only [ctrlMid_writes]; simp only [bne] at hi; bv_decide (config := { enums := false })
  let r := auxIn (ctrlMid_s sp) (ctrlMid_ram M)
  have hr (i : UInt16) (hi : ((i < 0x100 || 0x200 ≤ i) && i != 1177 && i != 69) = true) : r i = M i := by
    have h1 : (i < 0x100 || 0x200 ≤ i) = true := by simp only [bne] at hi; bv_decide (config := { enums := false })
    have h2 : (i != 1177 && i != 69) = true := by simp only [bne] at hi ⊢; bv_decide (config := { enums := false })
    show auxIn _ (ctrlMid_ram M) i = M i
    rw [auxIn_at _ _ _ h1, hmid i h2]
  have hs57 := scroll_away (ctrlMid_s sp) ram r hA
    (by simp only [pixelP, hr 0x6D (by decide), hr 0x86 (by decide), hr 0x6FF (by decide)]; simpa only [pixelP] using hx.2.2)
    (by rw [hr 0x6FF (by decide)]; exact hpx)
    (by rw [hr 0x71A (by decide)]; exact hk 0x71A (by decide)) (by rw [hr 0x71B (by decide)]; exact hk 0x71B (by decide))
    (by rw [hr 0x71C (by decide)]; exact hk 0x71C (by decide)) (by rw [hr 0x71D (by decide)]; exact hk 0x71D (by decide))
    (by rw [hr 0x3A1 (by decide), hk 0x3A1 (by decide)]; exact hA.plat) 0x57 (Or.inl rfl)
  rw [ctrlA0_composition, hM, HorizontalLimit.ctrlAux_x _ _ prg 0x57 (by decide)]
  rw [hs57, hr 0x57 (by decide), ← hM, Smb.Routine.ModelBridge.ms0_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA0_move (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) :
    ctrlA0_ram sp ram prg 0x45 = (Smb.Movement.setMove (modelMove ram)).move := by
  have hm := h.moveIn sp
  have hi := (moveIn_input sp ram h.ha h.he).2
  have e1 := Smb.Routine.ModelBridge.ms0_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc hi
  have e2 := Smb.Routine.ModelBridge.ms0_move (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc hi
  rw [modelMove_moveIn sp ram h.ha h.he] at e1 e2
  rw [ctrlA0_composition, ctrlAux_move, ctrlMid_move, e1, e2]
  simp only [Smb.Movement.setMove]
  generalize modelMove ram = M
  by_cases h1 : M.v = 0 <;> by_cases h2 : M.v < 0x80 <;> simp [h1, h2]

/-- State 1: speed through `ScrollHandler`, and the moving direction. -/
theorem ctrlA1_v (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    ctrlA1_ram sp ram prg 0x57 = (modelMove ram).v := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms1_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms1_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  generalize hM : ms1_ram (sp + 254) (moveIn sp ram) = M at hx hpx
  have hk (i : UInt16) (hi : carried i = true) : M i = ram i := by
    rw [← hM, Smb.Routine.HorizontalLimit.ms1_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hmid (i : UInt16) (hi : (i != 1177 && i != 69) = true) : ctrlMid_ram M i = M i := by
    apply ctrlMid_ram_frame; simp only [ctrlMid_writes]; simp only [bne] at hi; bv_decide (config := { enums := false })
  let r := auxIn (ctrlMid_s sp) (ctrlMid_ram M)
  have hr (i : UInt16) (hi : ((i < 0x100 || 0x200 ≤ i) && i != 1177 && i != 69) = true) : r i = M i := by
    have h1 : (i < 0x100 || 0x200 ≤ i) = true := by simp only [bne] at hi; bv_decide (config := { enums := false })
    have h2 : (i != 1177 && i != 69) = true := by simp only [bne] at hi ⊢; bv_decide (config := { enums := false })
    show auxIn _ (ctrlMid_ram M) i = M i
    rw [auxIn_at _ _ _ h1, hmid i h2]
  have hs57 := scroll_away (ctrlMid_s sp) ram r hA
    (by simp only [pixelP, hr 0x6D (by decide), hr 0x86 (by decide), hr 0x6FF (by decide)]; simpa only [pixelP] using hx.2.2)
    (by rw [hr 0x6FF (by decide)]; exact hpx)
    (by rw [hr 0x71A (by decide)]; exact hk 0x71A (by decide)) (by rw [hr 0x71B (by decide)]; exact hk 0x71B (by decide))
    (by rw [hr 0x71C (by decide)]; exact hk 0x71C (by decide)) (by rw [hr 0x71D (by decide)]; exact hk 0x71D (by decide))
    (by rw [hr 0x3A1 (by decide), hk 0x3A1 (by decide)]; exact hA.plat) 0x57 (Or.inl rfl)
  rw [ctrlA1_composition, hM, HorizontalLimit.ctrlAux_x _ _ prg 0x57 (by decide)]
  rw [hs57, hr 0x57 (by decide), ← hM, Smb.Routine.ModelBridge.ms1_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA1_move (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) :
    ctrlA1_ram sp ram prg 0x45 = (Smb.Movement.setMove (modelMove ram)).move := by
  have hm := h.moveIn sp
  have hi := (moveIn_input sp ram h.ha h.he).2
  have e1 := Smb.Routine.ModelBridge.ms1_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc hi
  have e2 := Smb.Routine.ModelBridge.ms1_move (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc hi
  rw [modelMove_moveIn sp ram h.ha h.he] at e1 e2
  rw [ctrlA1_composition, ctrlAux_move, ctrlMid_move, e1, e2]
  simp only [Smb.Movement.setMove]
  generalize modelMove ram = M
  by_cases h1 : M.v = 0 <;> by_cases h2 : M.v < 0x80 <;> simp [h1, h2]

/-- State 2: speed through `ScrollHandler`, and the moving direction. -/
theorem ctrlA2_v (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    ctrlA2_ram sp ram prg 0x57 = (modelMove ram).v := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms2_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms2_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  generalize hM : ms2_ram (sp + 254) (moveIn sp ram) = M at hx hpx
  have hk (i : UInt16) (hi : carried i = true) : M i = ram i := by
    rw [← hM, Smb.Routine.HorizontalLimit.ms2_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hmid (i : UInt16) (hi : (i != 1177 && i != 69) = true) : ctrlMid_ram M i = M i := by
    apply ctrlMid_ram_frame; simp only [ctrlMid_writes]; simp only [bne] at hi; bv_decide (config := { enums := false })
  let r := auxIn (ctrlMid_s sp) (ctrlMid_ram M)
  have hr (i : UInt16) (hi : ((i < 0x100 || 0x200 ≤ i) && i != 1177 && i != 69) = true) : r i = M i := by
    have h1 : (i < 0x100 || 0x200 ≤ i) = true := by simp only [bne] at hi; bv_decide (config := { enums := false })
    have h2 : (i != 1177 && i != 69) = true := by simp only [bne] at hi ⊢; bv_decide (config := { enums := false })
    show auxIn _ (ctrlMid_ram M) i = M i
    rw [auxIn_at _ _ _ h1, hmid i h2]
  have hs57 := scroll_away (ctrlMid_s sp) ram r hA
    (by simp only [pixelP, hr 0x6D (by decide), hr 0x86 (by decide), hr 0x6FF (by decide)]; simpa only [pixelP] using hx.2.2)
    (by rw [hr 0x6FF (by decide)]; exact hpx)
    (by rw [hr 0x71A (by decide)]; exact hk 0x71A (by decide)) (by rw [hr 0x71B (by decide)]; exact hk 0x71B (by decide))
    (by rw [hr 0x71C (by decide)]; exact hk 0x71C (by decide)) (by rw [hr 0x71D (by decide)]; exact hk 0x71D (by decide))
    (by rw [hr 0x3A1 (by decide), hk 0x3A1 (by decide)]; exact hA.plat) 0x57 (Or.inl rfl)
  rw [ctrlA2_composition, hM, HorizontalLimit.ctrlAux_x _ _ prg 0x57 (by decide)]
  rw [hs57, hr 0x57 (by decide), ← hM, Smb.Routine.ModelBridge.ms2_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2,
    modelMove_moveIn sp ram h.ha h.he]

theorem ctrlA2_move (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) :
    ctrlA2_ram sp ram prg 0x45 = (Smb.Movement.setMove (modelMove ram)).move := by
  have hm := h.moveIn sp
  have hi := (moveIn_input sp ram h.ha h.he).2
  have e1 := Smb.Routine.ModelBridge.ms2_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc hi
  have e2 := Smb.Routine.ModelBridge.ms2_move (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc hi
  rw [modelMove_moveIn sp ram h.ha h.he] at e1 e2
  rw [ctrlA2_composition, ctrlAux_move, ctrlMid_move, e1, e2]
  simp only [Smb.Movement.setMove]
  generalize modelMove ram = M
  by_cases h1 : M.v = 0 <;> by_cases h2 : M.v < 0x80 <;> simp [h1, h2]

/-! ## The whole routine -/

theorem setMove_f (M : Smb.Movement.S) : (Smb.Movement.setMove M).f = M.f := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_abs (M : Smb.Movement.S) : (Smb.Movement.setMove M).abs = M.abs := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_face (M : Smb.Movement.S) : (Smb.Movement.setMove M).face = M.face := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_t783 (M : Smb.Movement.S) : (Smb.Movement.setMove M).t783 = M.t783 := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_r703 (M : Smb.Movement.S) : (Smb.Movement.setMove M).r703 = M.r703 := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_y (M : Smb.Movement.S) : (Smb.Movement.setMove M).y = M.y := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_ysub (M : Smb.Movement.S) : (Smb.Movement.setMove M).ysub = M.ysub := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_vy (M : Smb.Movement.S) : (Smb.Movement.setMove M).vy = M.vy := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_vf (M : Smb.Movement.S) : (Smb.Movement.setMove M).vf = M.vf := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_g (M : Smb.Movement.S) : (Smb.Movement.setMove M).g = M.g := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_gfall (M : Smb.Movement.S) : (Smb.Movement.setMove M).gfall = M.gfall := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_y0 (M : Smb.Movement.S) : (Smb.Movement.setMove M).y0 = M.y0 := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_rise (M : Smb.Movement.S) : (Smb.Movement.setMove M).rise = M.rise := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_v (M : Smb.Movement.S) : (Smb.Movement.setMove M).v = M.v := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_st (M : Smb.Movement.S) : (Smb.Movement.setMove M).st = M.st := by
  unfold Smb.Movement.setMove; split <;> rfl
theorem setMove_prevA (M : Smb.Movement.S) : (Smb.Movement.setMove M).prevA = M.prevA := by
  unfold Smb.Movement.setMove; split <;> rfl

theorem modelMove_prevA (ram : UInt16 → UInt8) : (modelMove ram).prevA = ram 0x0D &&& 0x80 := by
  have h1 : ∀ s, (Smb.Movement.fallS s).prevA = s.prevA := by intro s; unfold Smb.Movement.fallS; split <;> rfl
  have h2 : ∀ a b c d s, (Smb.Movement.friction a b c d s).prevA = s.prevA := by
    intro a b c d s; unfold Smb.Movement.friction; repeat' split
    all_goals rfl
  have h3 : ∀ a b c i s, (Smb.Movement.routine a b c i s).prevA = s.prevA := by
    intro a b c i s; unfold Smb.Movement.routine Smb.Movement.skid; repeat' split
    all_goals rfl
  have h4 : ∀ a b s, (Smb.Movement.timerSet a b s).prevA = s.prevA := by intro a b s; unfold Smb.Movement.timerSet; split <;> rfl
  have h5 : ∀ a s, (Smb.Movement.jumpStart a s).prevA = s.prevA := by intro a s; unfold Smb.Movement.jumpStart; split <;> rfl
  simp only [modelMove, h1, Smb.Movement.moved, h2, h3, h4, h5, cellsOf]

theorem aF_57 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x57 = r 0x57 := by
  have h1 : ((0x57 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x57 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x57 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x57 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_705 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x705 = r 0x705 := by
  have h1 : ((0x705 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x705 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x705 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x705 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_700 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x700 = r 0x700 := by
  have h1 : ((0x700 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x700 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x700 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x700 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_33 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x33 = r 0x33 := by
  have h1 : ((0x33 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x33 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x33 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x33 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_45 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x45 = r 0x45 := by
  have h1 : ((0x45 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x45 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x45 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x45 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_783 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x783 = r 0x783 := by
  have h1 : ((0x783 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x783 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x783 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x783 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_703 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x703 = r 0x703 := by
  have h1 : ((0x703 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x703 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x703 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x703 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_416 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x416 = r 0x416 := by
  have h1 : ((0x416 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x416 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x416 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x416 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_709 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x709 = r 0x709 := by
  have h1 : ((0x709 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x709 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x709 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x709 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_70a (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x70A = r 0x70A := by
  have h1 : ((0x70A : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x70A : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x70A : UInt16) == 0x433) = false := by decide
  have h4 : ((0x70A : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_708 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x708 = r 0x708 := by
  have h1 : ((0x708 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x708 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x708 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x708 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_706 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x706 = r 0x706 := by
  have h1 : ((0x706 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x706 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x706 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x706 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_d (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0xD = r 0xD := by
  have h1 : ((0xD : UInt16) == 0xCE) = false := by decide
  have h2 : ((0xD : UInt16) == 0x9F) = false := by decide
  have h3 : ((0xD : UInt16) == 0x433) = false := by decide
  have h4 : ((0xD : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_ce (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0xCE = bif L then r 0xCE &&& 0xF0 else r 0xCE := by
  cases L <;> rfl
theorem aF_9f (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x9F = bif L then 0 else r 0x9F := by
  cases L <;> rfl
theorem aF_433 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x433 = bif L then 0 else r 0x433 := by
  cases L <;> rfl
theorem aF_1d (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x1D = bif L then 0 else r 0x1D := by
  cases L <;> rfl

theorem aF_86 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x86 = r 0x86 := by
  have h1 : ((0x86 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x86 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x86 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x86 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_6d (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x6D = r 0x6D := by
  have h1 : ((0x6D : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x6D : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x6D : UInt16) == 0x433) = false := by decide
  have h4 : ((0x6D : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
theorem aF_400 (L : Bool) (r : UInt16 → UInt8) : afterFoot L r 0x400 = r 0x400 := by
  have h1 : ((0x400 : UInt16) == 0xCE) = false := by decide
  have h2 : ((0x400 : UInt16) == 0x9F) = false := by decide
  have h3 : ((0x400 : UInt16) == 0x433) = false := by decide
  have h4 : ((0x400 : UInt16) == 0x1D) = false := by decide
  simp only [afterFoot, h1, h2, h3, h4, Bool.and_false, Bool.or_false, cond_false]
/-- What a frame needs of its collision: nothing overhead, no coin, axe, spring or pipe underfoot, and no wall. -/
structure BgClear (w : UInt16 → UInt8) (sp : UInt8) (R prg : UInt16 → UInt8) : Prop where
  go : bgPre_pc R = 0xDC98
  head : headBlocked prg (bgRam R) (bgY R) = false
  headc : headCoin prg (bgRam R) (bgY R) = false
  coin : footCoin prg (bgRam R) (bgY R) = false
  axe : footAxeAt prg (bgRam R) (bgY R) = false
  pipe : pipeEntryAt prg (bgRam R) (bgY R) = false
  imp : impeded prg (bgRam R) (bgY R) = false
  spring : (footTile prg (bgRam R) (bgY R) != 0x67 && footTile prg (bgRam R) (bgY R) != 0x68) = true
  side : sideBlocks prg (bgFootRam sp prg R) = false
  js : R 0x70E = 0
  swim : R 0x704 = 0
  st : R 0x1D ≤ 2

/-- State 0: from `$B0E9` to `$B179`, the model's cells end where the model says. -/
theorem frame0_model (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : BgClear w (frameS0 sp) (frameR0 sp ram prg) prg) :
    cellsOf (frame0_side_ram w sp ram prg) =
      afterBg (lands prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg))) (Smb.Movement.setMove (modelMove ram)) := by
  generalize hRdef : frameR0 sp ram prg = R at hb ⊢
  have hF (i : UInt16) (hi : cellOf i) : frame0_side_ram w sp ram prg i = afterFoot (lands prg (bgRam R) (bgY R)) (bgRam R) i := by
    unfold frame0_side_ram
    rw [ctrlAttr_cell _ i hi, show ctrlJ_ram (ctrlA0_s sp) (ctrlA0_ram sp ram prg) = R from hRdef]
    exact bgSide_cell w (frameS0 sp) R prg i hi htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
      (by rw [bgRam_cell R hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
  have hR (i : UInt16) (hi : cellOf i) (hne : i ≠ 0x1D) : bgRam R i = ctrlA0_ram sp ram prg i := by
    rw [bgRam_cell R hb.go i hne (by simp only [cellOf] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ← hRdef]
    exact ctrlJ_cell _ _ i hi
  have hset_f := setMove_f (modelMove ram)
  have hset_abs := setMove_abs (modelMove ram)
  have hset_face := setMove_face (modelMove ram)
  have hset_t783 := setMove_t783 (modelMove ram)
  have hset_r703 := setMove_r703 (modelMove ram)
  have hset_y := setMove_y (modelMove ram)
  have hset_ysub := setMove_ysub (modelMove ram)
  have hset_vy := setMove_vy (modelMove ram)
  have hset_vf := setMove_vf (modelMove ram)
  have hset_g := setMove_g (modelMove ram)
  have hset_gfall := setMove_gfall (modelMove ram)
  have hset_y0 := setMove_y0 (modelMove ram)
  have hset_rise := setMove_rise (modelMove ram)
  have e_f : bgRam R 0x705 = (Smb.Movement.setMove (modelMove ram)).f := by
    rw [hR 0x705 (by simp [cellOf]) (by decide), ctrlA0_f sp ram prg h, hset_f]
  have e_abs : bgRam R 0x700 = (Smb.Movement.setMove (modelMove ram)).abs := by
    rw [hR 0x700 (by simp [cellOf]) (by decide), ctrlA0_abs sp ram prg h, hset_abs]
  have e_face : bgRam R 0x33 = (Smb.Movement.setMove (modelMove ram)).face := by
    rw [hR 0x33 (by simp [cellOf]) (by decide), ctrlA0_face sp ram prg h, hset_face]
  have e_t783 : bgRam R 0x783 = (Smb.Movement.setMove (modelMove ram)).t783 := by
    rw [hR 0x783 (by simp [cellOf]) (by decide), ctrlA0_t783 sp ram prg h, hset_t783]
  have e_r703 : bgRam R 0x703 = (Smb.Movement.setMove (modelMove ram)).r703 := by
    rw [hR 0x703 (by simp [cellOf]) (by decide), ctrlA0_r703 sp ram prg h, hset_r703]
  have e_y : bgRam R 0xCE = (Smb.Movement.setMove (modelMove ram)).y := by
    rw [hR 0xCE (by simp [cellOf]) (by decide), ctrlA0_y sp ram prg h, hset_y]
  have e_ysub : bgRam R 0x416 = (Smb.Movement.setMove (modelMove ram)).ysub := by
    rw [hR 0x416 (by simp [cellOf]) (by decide), ctrlA0_ysub sp ram prg h, hset_ysub]
  have e_vy : bgRam R 0x9F = (Smb.Movement.setMove (modelMove ram)).vy := by
    rw [hR 0x9F (by simp [cellOf]) (by decide), ctrlA0_vy sp ram prg h, hset_vy]
  have e_vf : bgRam R 0x433 = (Smb.Movement.setMove (modelMove ram)).vf := by
    rw [hR 0x433 (by simp [cellOf]) (by decide), ctrlA0_vf sp ram prg h, hset_vf]
  have e_g : bgRam R 0x709 = (Smb.Movement.setMove (modelMove ram)).g := by
    rw [hR 0x709 (by simp [cellOf]) (by decide), ctrlA0_g sp ram prg h, hset_g]
  have e_gfall : bgRam R 0x70A = (Smb.Movement.setMove (modelMove ram)).gfall := by
    rw [hR 0x70A (by simp [cellOf]) (by decide), ctrlA0_gfall sp ram prg h, hset_gfall]
  have e_y0 : bgRam R 0x708 = (Smb.Movement.setMove (modelMove ram)).y0 := by
    rw [hR 0x708 (by simp [cellOf]) (by decide), ctrlA0_y0 sp ram prg h, hset_y0]
  have e_rise : bgRam R 0x706 = (Smb.Movement.setMove (modelMove ram)).rise := by
    rw [hR 0x706 (by simp [cellOf]) (by decide), ctrlA0_rise sp ram prg h, hset_rise]
  have hset_v := setMove_v (modelMove ram)
  have e_v : bgRam R 0x57 = (Smb.Movement.setMove (modelMove ram)).v := by
    rw [hR 0x57 (by simp [cellOf]) (by decide), ctrlA0_v sp ram prg h hA hv, hset_v]
  have e_move : bgRam R 0x45 = (Smb.Movement.setMove (modelMove ram)).move := by
    rw [hR 0x45 (by simp [cellOf]) (by decide), ctrlA0_move sp ram prg h]
  have hRst : R 0x1D = (modelMove ram).st := by
    rw [← hRdef]
    exact (ctrlJ_cell _ _ 0x1D (by simp [cellOf])).trans (ctrlA0_st sp ram prg h)
  have e_st : bgRam R 0x1D = bif (modelMove ram).st == 0 then 2 else (modelMove ram).st := by
    show bgSize_ram (bgPre_ram R) 0x1D = _
    rw [show bgSize_ram (bgPre_ram R) 0x1D = bgPre_ram R 0x1D by delta bgSize_ram; rfl, bgPre_st R hb.go hb.swim hb.st, hRst]
  have e_d : bgRam R 0x0D = ram 0x0D := by
    rw [hR 0x0D (by simp [cellOf]) (by decide), ctrlA0_post sp ram prg 0x0D (by decide), ms0_ram_frame _ _ _ (by simp only [ms0_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; bv_decide (config := { enums := false })), moveIn_pre sp ram 0x0D (by decide)]
  have hset_st := setMove_st (modelMove ram)
  have hset_p := setMove_prevA (modelMove ram)
  have hprev := modelMove_prevA ram
  simp only [cellsOf, hF 0x57 (by simp [cellOf]), hF 0x705 (by simp [cellOf]), hF 0x700 (by simp [cellOf]), hF 0x33 (by simp [cellOf]), hF 0x45 (by simp [cellOf]), hF 0x1D (by simp [cellOf]),
    hF 0x783 (by simp [cellOf]), hF 0x703 (by simp [cellOf]), hF 0xCE (by simp [cellOf]), hF 0x416 (by simp [cellOf]), hF 0x9F (by simp [cellOf]), hF 0x433 (by simp [cellOf]), hF 0x709 (by simp [cellOf]),
    hF 0x70A (by simp [cellOf]), hF 0x708 (by simp [cellOf]), hF 0x706 (by simp [cellOf]), hF 0x0D (by simp [cellOf])]
  generalize lands prg (bgRam R) (bgY R) = L
  generalize hM : Smb.Movement.setMove (modelMove ram) = M at *
  have hst' : (modelMove ram).st = M.st := hset_st.symm
  rw [hst'] at e_st
  have hp' : ram 0x0D &&& 0x80 = M.prevA := by rw [hset_p, hprev]
  cases L <;> cases hz : (M.st == 0) <;> simp only [aF_57, aF_705, aF_700, aF_33, aF_45, aF_783, aF_703, aF_416, aF_709, aF_70a, aF_708, aF_706, aF_d, aF_ce, aF_9f, aF_433, aF_1d, afterBg, cond_true, cond_false, Bool.false_eq_true, if_false, if_true, hz, e_v, e_f, e_abs, e_face, e_move, e_t783, e_r703, e_y, e_ysub, e_vy, e_vf, e_g, e_gfall, e_y0, e_rise, e_d, e_st, hp'] <;> rfl

/-- State 1: from `$B0E9` to `$B179`, the model's cells end where the model says. -/
theorem frame1_model (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : BgClear w (frameS1 sp) (frameR1 sp ram prg) prg) :
    cellsOf (frame1_side_ram w sp ram prg) =
      afterBg (lands prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg))) (Smb.Movement.setMove (modelMove ram)) := by
  generalize hRdef : frameR1 sp ram prg = R at hb ⊢
  have hF (i : UInt16) (hi : cellOf i) : frame1_side_ram w sp ram prg i = afterFoot (lands prg (bgRam R) (bgY R)) (bgRam R) i := by
    unfold frame1_side_ram
    rw [ctrlAttr_cell _ i hi, show ctrlJ_ram (ctrlA1_s sp) (ctrlA1_ram sp ram prg) = R from hRdef]
    exact bgSide_cell w (frameS1 sp) R prg i hi htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
      (by rw [bgRam_cell R hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
  have hR (i : UInt16) (hi : cellOf i) (hne : i ≠ 0x1D) : bgRam R i = ctrlA1_ram sp ram prg i := by
    rw [bgRam_cell R hb.go i hne (by simp only [cellOf] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ← hRdef]
    exact ctrlJ_cell _ _ i hi
  have hset_f := setMove_f (modelMove ram)
  have hset_abs := setMove_abs (modelMove ram)
  have hset_face := setMove_face (modelMove ram)
  have hset_t783 := setMove_t783 (modelMove ram)
  have hset_r703 := setMove_r703 (modelMove ram)
  have hset_y := setMove_y (modelMove ram)
  have hset_ysub := setMove_ysub (modelMove ram)
  have hset_vy := setMove_vy (modelMove ram)
  have hset_vf := setMove_vf (modelMove ram)
  have hset_g := setMove_g (modelMove ram)
  have hset_gfall := setMove_gfall (modelMove ram)
  have hset_y0 := setMove_y0 (modelMove ram)
  have hset_rise := setMove_rise (modelMove ram)
  have e_f : bgRam R 0x705 = (Smb.Movement.setMove (modelMove ram)).f := by
    rw [hR 0x705 (by simp [cellOf]) (by decide), ctrlA1_f sp ram prg h, hset_f]
  have e_abs : bgRam R 0x700 = (Smb.Movement.setMove (modelMove ram)).abs := by
    rw [hR 0x700 (by simp [cellOf]) (by decide), ctrlA1_abs sp ram prg h, hset_abs]
  have e_face : bgRam R 0x33 = (Smb.Movement.setMove (modelMove ram)).face := by
    rw [hR 0x33 (by simp [cellOf]) (by decide), ctrlA1_face sp ram prg h, hset_face]
  have e_t783 : bgRam R 0x783 = (Smb.Movement.setMove (modelMove ram)).t783 := by
    rw [hR 0x783 (by simp [cellOf]) (by decide), ctrlA1_t783 sp ram prg h, hset_t783]
  have e_r703 : bgRam R 0x703 = (Smb.Movement.setMove (modelMove ram)).r703 := by
    rw [hR 0x703 (by simp [cellOf]) (by decide), ctrlA1_r703 sp ram prg h, hset_r703]
  have e_y : bgRam R 0xCE = (Smb.Movement.setMove (modelMove ram)).y := by
    rw [hR 0xCE (by simp [cellOf]) (by decide), ctrlA1_y sp ram prg h, hset_y]
  have e_ysub : bgRam R 0x416 = (Smb.Movement.setMove (modelMove ram)).ysub := by
    rw [hR 0x416 (by simp [cellOf]) (by decide), ctrlA1_ysub sp ram prg h, hset_ysub]
  have e_vy : bgRam R 0x9F = (Smb.Movement.setMove (modelMove ram)).vy := by
    rw [hR 0x9F (by simp [cellOf]) (by decide), ctrlA1_vy sp ram prg h, hset_vy]
  have e_vf : bgRam R 0x433 = (Smb.Movement.setMove (modelMove ram)).vf := by
    rw [hR 0x433 (by simp [cellOf]) (by decide), ctrlA1_vf sp ram prg h, hset_vf]
  have e_g : bgRam R 0x709 = (Smb.Movement.setMove (modelMove ram)).g := by
    rw [hR 0x709 (by simp [cellOf]) (by decide), ctrlA1_g sp ram prg h, hset_g]
  have e_gfall : bgRam R 0x70A = (Smb.Movement.setMove (modelMove ram)).gfall := by
    rw [hR 0x70A (by simp [cellOf]) (by decide), ctrlA1_gfall sp ram prg h, hset_gfall]
  have e_y0 : bgRam R 0x708 = (Smb.Movement.setMove (modelMove ram)).y0 := by
    rw [hR 0x708 (by simp [cellOf]) (by decide), ctrlA1_y0 sp ram prg h, hset_y0]
  have e_rise : bgRam R 0x706 = (Smb.Movement.setMove (modelMove ram)).rise := by
    rw [hR 0x706 (by simp [cellOf]) (by decide), ctrlA1_rise sp ram prg h, hset_rise]
  have hset_v := setMove_v (modelMove ram)
  have e_v : bgRam R 0x57 = (Smb.Movement.setMove (modelMove ram)).v := by
    rw [hR 0x57 (by simp [cellOf]) (by decide), ctrlA1_v sp ram prg h hA hv, hset_v]
  have e_move : bgRam R 0x45 = (Smb.Movement.setMove (modelMove ram)).move := by
    rw [hR 0x45 (by simp [cellOf]) (by decide), ctrlA1_move sp ram prg h]
  have hRst : R 0x1D = (modelMove ram).st := by
    rw [← hRdef]
    exact (ctrlJ_cell _ _ 0x1D (by simp [cellOf])).trans (ctrlA1_st sp ram prg h)
  have e_st : bgRam R 0x1D = bif (modelMove ram).st == 0 then 2 else (modelMove ram).st := by
    show bgSize_ram (bgPre_ram R) 0x1D = _
    rw [show bgSize_ram (bgPre_ram R) 0x1D = bgPre_ram R 0x1D by delta bgSize_ram; rfl, bgPre_st R hb.go hb.swim hb.st, hRst]
  have e_d : bgRam R 0x0D = ram 0x0D := by
    rw [hR 0x0D (by simp [cellOf]) (by decide), ctrlA1_post sp ram prg 0x0D (by decide), ms1_ram_frame _ _ _ (by simp only [ms1_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; bv_decide (config := { enums := false })), moveIn_pre sp ram 0x0D (by decide)]
  have hset_st := setMove_st (modelMove ram)
  have hset_p := setMove_prevA (modelMove ram)
  have hprev := modelMove_prevA ram
  simp only [cellsOf, hF 0x57 (by simp [cellOf]), hF 0x705 (by simp [cellOf]), hF 0x700 (by simp [cellOf]), hF 0x33 (by simp [cellOf]), hF 0x45 (by simp [cellOf]), hF 0x1D (by simp [cellOf]),
    hF 0x783 (by simp [cellOf]), hF 0x703 (by simp [cellOf]), hF 0xCE (by simp [cellOf]), hF 0x416 (by simp [cellOf]), hF 0x9F (by simp [cellOf]), hF 0x433 (by simp [cellOf]), hF 0x709 (by simp [cellOf]),
    hF 0x70A (by simp [cellOf]), hF 0x708 (by simp [cellOf]), hF 0x706 (by simp [cellOf]), hF 0x0D (by simp [cellOf])]
  generalize lands prg (bgRam R) (bgY R) = L
  generalize hM : Smb.Movement.setMove (modelMove ram) = M at *
  have hst' : (modelMove ram).st = M.st := hset_st.symm
  rw [hst'] at e_st
  have hp' : ram 0x0D &&& 0x80 = M.prevA := by rw [hset_p, hprev]
  cases L <;> cases hz : (M.st == 0) <;> simp only [aF_57, aF_705, aF_700, aF_33, aF_45, aF_783, aF_703, aF_416, aF_709, aF_70a, aF_708, aF_706, aF_d, aF_ce, aF_9f, aF_433, aF_1d, afterBg, cond_true, cond_false, Bool.false_eq_true, if_false, if_true, hz, e_v, e_f, e_abs, e_face, e_move, e_t783, e_r703, e_y, e_ysub, e_vy, e_vf, e_g, e_gfall, e_y0, e_rise, e_d, e_st, hp'] <;> rfl

/-- State 2: from `$B0E9` to `$B179`, the model's cells end where the model says. -/
theorem frame2_model (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : BgClear w (frameS2 sp) (frameR2 sp ram prg) prg) :
    cellsOf (frame2_side_ram w sp ram prg) =
      afterBg (lands prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg))) (Smb.Movement.setMove (modelMove ram)) := by
  generalize hRdef : frameR2 sp ram prg = R at hb ⊢
  have hF (i : UInt16) (hi : cellOf i) : frame2_side_ram w sp ram prg i = afterFoot (lands prg (bgRam R) (bgY R)) (bgRam R) i := by
    unfold frame2_side_ram
    rw [ctrlAttr_cell _ i hi, show ctrlJ_ram (ctrlA2_s sp) (ctrlA2_ram sp ram prg) = R from hRdef]
    exact bgSide_cell w (frameS2 sp) R prg i hi htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
      (by rw [bgRam_cell R hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
  have hR (i : UInt16) (hi : cellOf i) (hne : i ≠ 0x1D) : bgRam R i = ctrlA2_ram sp ram prg i := by
    rw [bgRam_cell R hb.go i hne (by simp only [cellOf] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ← hRdef]
    exact ctrlJ_cell _ _ i hi
  have hset_f := setMove_f (modelMove ram)
  have hset_abs := setMove_abs (modelMove ram)
  have hset_face := setMove_face (modelMove ram)
  have hset_t783 := setMove_t783 (modelMove ram)
  have hset_r703 := setMove_r703 (modelMove ram)
  have hset_y := setMove_y (modelMove ram)
  have hset_ysub := setMove_ysub (modelMove ram)
  have hset_vy := setMove_vy (modelMove ram)
  have hset_vf := setMove_vf (modelMove ram)
  have hset_g := setMove_g (modelMove ram)
  have hset_gfall := setMove_gfall (modelMove ram)
  have hset_y0 := setMove_y0 (modelMove ram)
  have hset_rise := setMove_rise (modelMove ram)
  have e_f : bgRam R 0x705 = (Smb.Movement.setMove (modelMove ram)).f := by
    rw [hR 0x705 (by simp [cellOf]) (by decide), ctrlA2_f sp ram prg h, hset_f]
  have e_abs : bgRam R 0x700 = (Smb.Movement.setMove (modelMove ram)).abs := by
    rw [hR 0x700 (by simp [cellOf]) (by decide), ctrlA2_abs sp ram prg h, hset_abs]
  have e_face : bgRam R 0x33 = (Smb.Movement.setMove (modelMove ram)).face := by
    rw [hR 0x33 (by simp [cellOf]) (by decide), ctrlA2_face sp ram prg h, hset_face]
  have e_t783 : bgRam R 0x783 = (Smb.Movement.setMove (modelMove ram)).t783 := by
    rw [hR 0x783 (by simp [cellOf]) (by decide), ctrlA2_t783 sp ram prg h, hset_t783]
  have e_r703 : bgRam R 0x703 = (Smb.Movement.setMove (modelMove ram)).r703 := by
    rw [hR 0x703 (by simp [cellOf]) (by decide), ctrlA2_r703 sp ram prg h, hset_r703]
  have e_y : bgRam R 0xCE = (Smb.Movement.setMove (modelMove ram)).y := by
    rw [hR 0xCE (by simp [cellOf]) (by decide), ctrlA2_y sp ram prg h, hset_y]
  have e_ysub : bgRam R 0x416 = (Smb.Movement.setMove (modelMove ram)).ysub := by
    rw [hR 0x416 (by simp [cellOf]) (by decide), ctrlA2_ysub sp ram prg h, hset_ysub]
  have e_vy : bgRam R 0x9F = (Smb.Movement.setMove (modelMove ram)).vy := by
    rw [hR 0x9F (by simp [cellOf]) (by decide), ctrlA2_vy sp ram prg h, hset_vy]
  have e_vf : bgRam R 0x433 = (Smb.Movement.setMove (modelMove ram)).vf := by
    rw [hR 0x433 (by simp [cellOf]) (by decide), ctrlA2_vf sp ram prg h, hset_vf]
  have e_g : bgRam R 0x709 = (Smb.Movement.setMove (modelMove ram)).g := by
    rw [hR 0x709 (by simp [cellOf]) (by decide), ctrlA2_g sp ram prg h, hset_g]
  have e_gfall : bgRam R 0x70A = (Smb.Movement.setMove (modelMove ram)).gfall := by
    rw [hR 0x70A (by simp [cellOf]) (by decide), ctrlA2_gfall sp ram prg h, hset_gfall]
  have e_y0 : bgRam R 0x708 = (Smb.Movement.setMove (modelMove ram)).y0 := by
    rw [hR 0x708 (by simp [cellOf]) (by decide), ctrlA2_y0 sp ram prg h, hset_y0]
  have e_rise : bgRam R 0x706 = (Smb.Movement.setMove (modelMove ram)).rise := by
    rw [hR 0x706 (by simp [cellOf]) (by decide), ctrlA2_rise sp ram prg h, hset_rise]
  have hset_v := setMove_v (modelMove ram)
  have e_v : bgRam R 0x57 = (Smb.Movement.setMove (modelMove ram)).v := by
    rw [hR 0x57 (by simp [cellOf]) (by decide), ctrlA2_v sp ram prg h hA hv, hset_v]
  have e_move : bgRam R 0x45 = (Smb.Movement.setMove (modelMove ram)).move := by
    rw [hR 0x45 (by simp [cellOf]) (by decide), ctrlA2_move sp ram prg h]
  have hRst : R 0x1D = (modelMove ram).st := by
    rw [← hRdef]
    exact (ctrlJ_cell _ _ 0x1D (by simp [cellOf])).trans (ctrlA2_st sp ram prg h)
  have e_st : bgRam R 0x1D = bif (modelMove ram).st == 0 then 2 else (modelMove ram).st := by
    show bgSize_ram (bgPre_ram R) 0x1D = _
    rw [show bgSize_ram (bgPre_ram R) 0x1D = bgPre_ram R 0x1D by delta bgSize_ram; rfl, bgPre_st R hb.go hb.swim hb.st, hRst]
  have e_d : bgRam R 0x0D = ram 0x0D := by
    rw [hR 0x0D (by simp [cellOf]) (by decide), ctrlA2_post sp ram prg 0x0D (by decide), ms2_ram_frame _ _ _ (by simp only [ms2_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; bv_decide (config := { enums := false })), moveIn_pre sp ram 0x0D (by decide)]
  have hset_st := setMove_st (modelMove ram)
  have hset_p := setMove_prevA (modelMove ram)
  have hprev := modelMove_prevA ram
  simp only [cellsOf, hF 0x57 (by simp [cellOf]), hF 0x705 (by simp [cellOf]), hF 0x700 (by simp [cellOf]), hF 0x33 (by simp [cellOf]), hF 0x45 (by simp [cellOf]), hF 0x1D (by simp [cellOf]),
    hF 0x783 (by simp [cellOf]), hF 0x703 (by simp [cellOf]), hF 0xCE (by simp [cellOf]), hF 0x416 (by simp [cellOf]), hF 0x9F (by simp [cellOf]), hF 0x433 (by simp [cellOf]), hF 0x709 (by simp [cellOf]),
    hF 0x70A (by simp [cellOf]), hF 0x708 (by simp [cellOf]), hF 0x706 (by simp [cellOf]), hF 0x0D (by simp [cellOf])]
  generalize lands prg (bgRam R) (bgY R) = L
  generalize hM : Smb.Movement.setMove (modelMove ram) = M at *
  have hst' : (modelMove ram).st = M.st := hset_st.symm
  rw [hst'] at e_st
  have hp' : ram 0x0D &&& 0x80 = M.prevA := by rw [hset_p, hprev]
  cases L <;> cases hz : (M.st == 0) <;> simp only [aF_57, aF_705, aF_700, aF_33, aF_45, aF_783, aF_703, aF_416, aF_709, aF_70a, aF_708, aF_706, aF_d, aF_ce, aF_9f, aF_433, aF_1d, afterBg, cond_true, cond_false, Bool.false_eq_true, if_false, if_true, hz, e_v, e_f, e_abs, e_face, e_move, e_t783, e_r703, e_y, e_ysub, e_vy, e_vf, e_g, e_gfall, e_y0, e_rise, e_d, e_st, hp'] <;> rfl

/-- State 0: Mario's position, as `ScrollHandler` leaves it away from the screen's edges. -/
theorem ctrlA0_x (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D ∨ i = 0x400) :
    ctrlA0_ram sp ram prg i = ms0_ram (sp + 254) (moveIn sp ram) i := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms0_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms0_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms0_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  generalize hM : ms0_ram (sp + 254) (moveIn sp ram) = M at hx hpx
  have hk (i : UInt16) (hi : carried i = true) : M i = ram i := by
    rw [← hM, Smb.Routine.HorizontalLimit.ms0_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hmid (i : UInt16) (hi : (i != 1177 && i != 69) = true) : ctrlMid_ram M i = M i := by
    apply ctrlMid_ram_frame; simp only [ctrlMid_writes]; simp only [bne] at hi; bv_decide (config := { enums := false })
  let r := auxIn (ctrlMid_s sp) (ctrlMid_ram M)
  have hr (i : UInt16) (hi : ((i < 0x100 || 0x200 ≤ i) && i != 1177 && i != 69) = true) : r i = M i := by
    have h1 : (i < 0x100 || 0x200 ≤ i) = true := by simp only [bne] at hi; bv_decide (config := { enums := false })
    have h2 : (i != 1177 && i != 69) = true := by simp only [bne] at hi ⊢; bv_decide (config := { enums := false })
    show auxIn _ (ctrlMid_ram M) i = M i
    rw [auxIn_at _ _ _ h1, hmid i h2]
  have hs := scroll_away (ctrlMid_s sp) ram r hA
    (by simp only [pixelP, hr 0x6D (by decide), hr 0x86 (by decide), hr 0x6FF (by decide)]; simpa only [pixelP] using hx.2.2)
    (by rw [hr 0x6FF (by decide)]; exact hpx)
    (by rw [hr 0x71A (by decide)]; exact hk 0x71A (by decide)) (by rw [hr 0x71B (by decide)]; exact hk 0x71B (by decide))
    (by rw [hr 0x71C (by decide)]; exact hk 0x71C (by decide)) (by rw [hr 0x71D (by decide)]; exact hk 0x71D (by decide))
    (by rw [hr 0x3A1 (by decide), hk 0x3A1 (by decide)]; exact hA.plat) i (by rcases hi with rfl | rfl | rfl <;> simp)
  rw [ctrlA0_composition, hM, HorizontalLimit.ctrlAux_x _ _ prg i (by rcases hi with rfl | rfl | rfl <;> decide), hs]
  rcases hi with rfl | rfl | rfl
  · exact hr 0x86 (by decide)
  · exact hr 0x6D (by decide)
  · exact hr 0x400 (by decide)

/-- State 0: the pixel moves by at most 4 before the collision code. -/
theorem ctrlA0_near (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    pixelP (ctrlA0_ram sp ram prg) = pixelP ram + sext16b (ms0_ram (sp + 254) (moveIn sp ram) 0x6FF) ∧
      (ms0_ram (sp + 254) (moveIn sp ram) 0x6FF ≤ 3 ∨ 0xFC ≤ ms0_ram (sp + 254) (moveIn sp ram) 0x6FF) := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms0_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms0_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms0_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA0_x sp ram prg h hA hv
  refine ⟨?_, hpx⟩
  simp only [pixelP, hctrl 0x86 (by simp), hctrl 0x6D (by simp)]
  simpa only [pixelP] using hx.2.2

/-- State 0: Mario's position moves by the new speed, before the collision code. -/
theorem ctrlA0_pos (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    pack (pixelP (ctrlA0_ram sp ram prg)) (ctrlA0_ram sp ram prg 0x400) =
      (pack (pixelP ram) (ram 0x400) + sext (modelMove ram).v * 16) &&& 0xFFFFFF := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms0_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms0_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms0_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA0_x sp ram prg h hA hv
  have hpos := hx.2.1
  rw [pos24_pack, pos24_pack, hvM] at hpos
  simp only [pixelP, pos16, hctrl 0x86 (by simp), hctrl 0x6D (by simp), hctrl 0x400 (by simp)]
  simpa only [pixelP, pos16] using hpos

/-- State 0: Mario's position moves by the new speed. -/
theorem frame0_pos (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move0Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : BgClear w (frameS0 sp) (frameR0 sp ram prg) prg) :
    pack (pixelP (frame0_side_ram w sp ram prg)) (frame0_side_ram w sp ram prg 0x400) =
      (pack (pixelP ram) (ram 0x400) + sext (modelMove ram).v * 16) &&& 0xFFFFFF := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms0_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms0_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms0_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA0_x sp ram prg h hA hv
  have hF (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D ∨ i = 0x400) : frame0_side_ram w sp ram prg i = ms0_ram (sp + 254) (moveIn sp ram) i := by
    have hc : cellOf i := by rcases hi with rfl | rfl | rfl <;> simp [cellOf]
    rw [← hctrl i hi]
    unfold frame0_side_ram
    rw [ctrlAttr_cell _ i hc]
    have := bgSide_cell w (frameS0 sp) (frameR0 sp ram prg) prg i hc htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
      (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
    rw [show ctrlJ_ram (ctrlA0_s sp) (ctrlA0_ram sp ram prg) = frameR0 sp ram prg from rfl, this]
    have hne : i ≠ 0x1D ∧ i ≠ 0x490 := by rcases hi with rfl | rfl | rfl <;> decide
    have ha : afterFoot (lands prg (bgRam (frameR0 sp ram prg)) (bgY (frameR0 sp ram prg))) (bgRam (frameR0 sp ram prg)) i = bgRam (frameR0 sp ram prg) i := by
      rcases hi with rfl | rfl | rfl
      · exact aF_86 _ _
      · exact aF_6d _ _
      · exact aF_400 _ _
    rw [ha, bgRam_cell _ hb.go i hne.1 hne.2]
    exact ctrlJ_cell _ _ i hc
  have hpos := hx.2.1
  rw [pos24_pack, pos24_pack, hvM] at hpos
  simp only [pixelP, pos16, hF 0x86 (by simp), hF 0x6D (by simp), hF 0x400 (by simp)]
  simpa only [pixelP, pos16] using hpos

/-- State 1: Mario's position, as `ScrollHandler` leaves it away from the screen's edges. -/
theorem ctrlA1_x (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D ∨ i = 0x400) :
    ctrlA1_ram sp ram prg i = ms1_ram (sp + 254) (moveIn sp ram) i := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms1_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms1_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms1_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  generalize hM : ms1_ram (sp + 254) (moveIn sp ram) = M at hx hpx
  have hk (i : UInt16) (hi : carried i = true) : M i = ram i := by
    rw [← hM, Smb.Routine.HorizontalLimit.ms1_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hmid (i : UInt16) (hi : (i != 1177 && i != 69) = true) : ctrlMid_ram M i = M i := by
    apply ctrlMid_ram_frame; simp only [ctrlMid_writes]; simp only [bne] at hi; bv_decide (config := { enums := false })
  let r := auxIn (ctrlMid_s sp) (ctrlMid_ram M)
  have hr (i : UInt16) (hi : ((i < 0x100 || 0x200 ≤ i) && i != 1177 && i != 69) = true) : r i = M i := by
    have h1 : (i < 0x100 || 0x200 ≤ i) = true := by simp only [bne] at hi; bv_decide (config := { enums := false })
    have h2 : (i != 1177 && i != 69) = true := by simp only [bne] at hi ⊢; bv_decide (config := { enums := false })
    show auxIn _ (ctrlMid_ram M) i = M i
    rw [auxIn_at _ _ _ h1, hmid i h2]
  have hs := scroll_away (ctrlMid_s sp) ram r hA
    (by simp only [pixelP, hr 0x6D (by decide), hr 0x86 (by decide), hr 0x6FF (by decide)]; simpa only [pixelP] using hx.2.2)
    (by rw [hr 0x6FF (by decide)]; exact hpx)
    (by rw [hr 0x71A (by decide)]; exact hk 0x71A (by decide)) (by rw [hr 0x71B (by decide)]; exact hk 0x71B (by decide))
    (by rw [hr 0x71C (by decide)]; exact hk 0x71C (by decide)) (by rw [hr 0x71D (by decide)]; exact hk 0x71D (by decide))
    (by rw [hr 0x3A1 (by decide), hk 0x3A1 (by decide)]; exact hA.plat) i (by rcases hi with rfl | rfl | rfl <;> simp)
  rw [ctrlA1_composition, hM, HorizontalLimit.ctrlAux_x _ _ prg i (by rcases hi with rfl | rfl | rfl <;> decide), hs]
  rcases hi with rfl | rfl | rfl
  · exact hr 0x86 (by decide)
  · exact hr 0x6D (by decide)
  · exact hr 0x400 (by decide)

/-- State 1: the pixel moves by at most 4 before the collision code. -/
theorem ctrlA1_near (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    pixelP (ctrlA1_ram sp ram prg) = pixelP ram + sext16b (ms1_ram (sp + 254) (moveIn sp ram) 0x6FF) ∧
      (ms1_ram (sp + 254) (moveIn sp ram) 0x6FF ≤ 3 ∨ 0xFC ≤ ms1_ram (sp + 254) (moveIn sp ram) 0x6FF) := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms1_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms1_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms1_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA1_x sp ram prg h hA hv
  refine ⟨?_, hpx⟩
  simp only [pixelP, hctrl 0x86 (by simp), hctrl 0x6D (by simp)]
  simpa only [pixelP] using hx.2.2

/-- State 1: Mario's position moves by the new speed, before the collision code. -/
theorem ctrlA1_pos (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    pack (pixelP (ctrlA1_ram sp ram prg)) (ctrlA1_ram sp ram prg 0x400) =
      (pack (pixelP ram) (ram 0x400) + sext (modelMove ram).v * 16) &&& 0xFFFFFF := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms1_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms1_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms1_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA1_x sp ram prg h hA hv
  have hpos := hx.2.1
  rw [pos24_pack, pos24_pack, hvM] at hpos
  simp only [pixelP, pos16, hctrl 0x86 (by simp), hctrl 0x6D (by simp), hctrl 0x400 (by simp)]
  simpa only [pixelP, pos16] using hpos

/-- State 1: Mario's position moves by the new speed. -/
theorem frame1_pos (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move1Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : BgClear w (frameS1 sp) (frameR1 sp ram prg) prg) :
    pack (pixelP (frame1_side_ram w sp ram prg)) (frame1_side_ram w sp ram prg 0x400) =
      (pack (pixelP ram) (ram 0x400) + sext (modelMove ram).v * 16) &&& 0xFFFFFF := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms1_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms1_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms1_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA1_x sp ram prg h hA hv
  have hF (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D ∨ i = 0x400) : frame1_side_ram w sp ram prg i = ms1_ram (sp + 254) (moveIn sp ram) i := by
    have hc : cellOf i := by rcases hi with rfl | rfl | rfl <;> simp [cellOf]
    rw [← hctrl i hi]
    unfold frame1_side_ram
    rw [ctrlAttr_cell _ i hc]
    have := bgSide_cell w (frameS1 sp) (frameR1 sp ram prg) prg i hc htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
      (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
    rw [show ctrlJ_ram (ctrlA1_s sp) (ctrlA1_ram sp ram prg) = frameR1 sp ram prg from rfl, this]
    have hne : i ≠ 0x1D ∧ i ≠ 0x490 := by rcases hi with rfl | rfl | rfl <;> decide
    have ha : afterFoot (lands prg (bgRam (frameR1 sp ram prg)) (bgY (frameR1 sp ram prg))) (bgRam (frameR1 sp ram prg)) i = bgRam (frameR1 sp ram prg) i := by
      rcases hi with rfl | rfl | rfl
      · exact aF_86 _ _
      · exact aF_6d _ _
      · exact aF_400 _ _
    rw [ha, bgRam_cell _ hb.go i hne.1 hne.2]
    exact ctrlJ_cell _ _ i hc
  have hpos := hx.2.1
  rw [pos24_pack, pos24_pack, hvM] at hpos
  simp only [pixelP, pos16, hF 0x86 (by simp), hF 0x6D (by simp), hF 0x400 (by simp)]
  simpa only [pixelP, pos16] using hpos

/-- State 2: Mario's position, as `ScrollHandler` leaves it away from the screen's edges. -/
theorem ctrlA2_x (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D ∨ i = 0x400) :
    ctrlA2_ram sp ram prg i = ms2_ram (sp + 254) (moveIn sp ram) i := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms2_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms2_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms2_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  generalize hM : ms2_ram (sp + 254) (moveIn sp ram) = M at hx hpx
  have hk (i : UInt16) (hi : carried i = true) : M i = ram i := by
    rw [← hM, Smb.Routine.HorizontalLimit.ms2_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hmid (i : UInt16) (hi : (i != 1177 && i != 69) = true) : ctrlMid_ram M i = M i := by
    apply ctrlMid_ram_frame; simp only [ctrlMid_writes]; simp only [bne] at hi; bv_decide (config := { enums := false })
  let r := auxIn (ctrlMid_s sp) (ctrlMid_ram M)
  have hr (i : UInt16) (hi : ((i < 0x100 || 0x200 ≤ i) && i != 1177 && i != 69) = true) : r i = M i := by
    have h1 : (i < 0x100 || 0x200 ≤ i) = true := by simp only [bne] at hi; bv_decide (config := { enums := false })
    have h2 : (i != 1177 && i != 69) = true := by simp only [bne] at hi ⊢; bv_decide (config := { enums := false })
    show auxIn _ (ctrlMid_ram M) i = M i
    rw [auxIn_at _ _ _ h1, hmid i h2]
  have hs := scroll_away (ctrlMid_s sp) ram r hA
    (by simp only [pixelP, hr 0x6D (by decide), hr 0x86 (by decide), hr 0x6FF (by decide)]; simpa only [pixelP] using hx.2.2)
    (by rw [hr 0x6FF (by decide)]; exact hpx)
    (by rw [hr 0x71A (by decide)]; exact hk 0x71A (by decide)) (by rw [hr 0x71B (by decide)]; exact hk 0x71B (by decide))
    (by rw [hr 0x71C (by decide)]; exact hk 0x71C (by decide)) (by rw [hr 0x71D (by decide)]; exact hk 0x71D (by decide))
    (by rw [hr 0x3A1 (by decide), hk 0x3A1 (by decide)]; exact hA.plat) i (by rcases hi with rfl | rfl | rfl <;> simp)
  rw [ctrlA2_composition, hM, HorizontalLimit.ctrlAux_x _ _ prg i (by rcases hi with rfl | rfl | rfl <;> decide), hs]
  rcases hi with rfl | rfl | rfl
  · exact hr 0x86 (by decide)
  · exact hr 0x6D (by decide)
  · exact hr 0x400 (by decide)

/-- State 2: the pixel moves by at most 4 before the collision code. -/
theorem ctrlA2_near (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    pixelP (ctrlA2_ram sp ram prg) = pixelP ram + sext16b (ms2_ram (sp + 254) (moveIn sp ram) 0x6FF) ∧
      (ms2_ram (sp + 254) (moveIn sp ram) 0x6FF ≤ 3 ∨ 0xFC ≤ ms2_ram (sp + 254) (moveIn sp ram) 0x6FF) := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms2_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms2_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms2_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA2_x sp ram prg h hA hv
  refine ⟨?_, hpx⟩
  simp only [pixelP, hctrl 0x86 (by simp), hctrl 0x6D (by simp)]
  simpa only [pixelP] using hx.2.2

/-- State 2: Mario's position moves by the new speed, before the collision code. -/
theorem ctrlA2_pos (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true) :
    pack (pixelP (ctrlA2_ram sp ram prg)) (ctrlA2_ram sp ram prg 0x400) =
      (pack (pixelP ram) (ram 0x400) + sext (modelMove ram).v * 16) &&& 0xFFFFFF := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms2_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms2_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms2_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA2_x sp ram prg h hA hv
  have hpos := hx.2.1
  rw [pos24_pack, pos24_pack, hvM] at hpos
  simp only [pixelP, pos16, hctrl 0x86 (by simp), hctrl 0x6D (by simp), hctrl 0x400 (by simp)]
  simpa only [pixelP, pos16] using hpos

/-- State 2: Mario's position moves by the new speed. -/
theorem frame2_pos (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (h : Move2Hyps ram) (hA : Away ram) (hv : speedOk (ram 0x57) = true)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hb : BgClear w (frameS2 sp) (frameR2 sp ram prg) prg) :
    pack (pixelP (frame2_side_ram w sp ram prg)) (frame2_side_ram w sp ram prg 0x400) =
      (pack (pixelP ram) (ram 0x400) + sext (modelMove ram).v * 16) &&& 0xFFFFFF := by
  have hm := h.moveIn sp
  have hmv : speedOk (moveIn sp ram 0x57) = true := by rw [moveIn_pre sp ram 0x57 (by decide)]; exact hv
  have hx := moveX_transport sp ram _ (Smb.Routine.HorizontalLimit.ms2_x (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hmv)
  have hpx := ms2_px (sp + 254) (moveIn sp ram) hmv hm.ht hm.hs hm.hz hm.hjs
  have hvM := Smb.Routine.ModelBridge.ms2_v (sp + 254) (moveIn sp ram) hm.ht hm.hs hm.hz hm.hjs hm.hspd hm.he hm.ha hm.hc (moveIn_input sp ram h.ha h.he).2
  rw [modelMove_moveIn sp ram h.ha h.he] at hvM
  have hctrl := ctrlA2_x sp ram prg h hA hv
  have hF (i : UInt16) (hi : i = 0x86 ∨ i = 0x6D ∨ i = 0x400) : frame2_side_ram w sp ram prg i = ms2_ram (sp + 254) (moveIn sp ram) i := by
    have hc : cellOf i := by rcases hi with rfl | rfl | rfl <;> simp [cellOf]
    rw [← hctrl i hi]
    unfold frame2_side_ram
    rw [ctrlAttr_cell _ i hc]
    have := bgSide_cell w (frameS2 sp) (frameR2 sp ram prg) prg i hc htbl hb.head hb.headc hb.coin hb.axe hb.pipe hb.imp
      (by rw [bgRam_cell _ hb.go 0x70E (by decide) (by decide)]; exact hb.js) hb.spring hb.side
    rw [show ctrlJ_ram (ctrlA2_s sp) (ctrlA2_ram sp ram prg) = frameR2 sp ram prg from rfl, this]
    have hne : i ≠ 0x1D ∧ i ≠ 0x490 := by rcases hi with rfl | rfl | rfl <;> decide
    have ha : afterFoot (lands prg (bgRam (frameR2 sp ram prg)) (bgY (frameR2 sp ram prg))) (bgRam (frameR2 sp ram prg)) i = bgRam (frameR2 sp ram prg) i := by
      rcases hi with rfl | rfl | rfl
      · exact aF_86 _ _
      · exact aF_6d _ _
      · exact aF_400 _ _
    rw [ha, bgRam_cell _ hb.go i hne.1 hne.2]
    exact ctrlJ_cell _ _ i hc
  have hpos := hx.2.1
  rw [pos24_pack, pos24_pack, hvM] at hpos
  simp only [pixelP, pos16, hF 0x86 (by simp), hF 0x6D (by simp), hF 0x400 (by simp)]
  simpa only [pixelP, pos16] using hpos

end Smb.Routine.ModelFrame
