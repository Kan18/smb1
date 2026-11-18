import Smb.Goal.OpenFloor
import Smb.Routine.LaunchVert
import Smb.Routine.LaunchJoin

/-!
# What Mario's sensors read, from the launch's bounds

The regions' bounds fix the block buffer near Mario: air, and the floor's two rows. `tile_eq` reads a tile off that from his position, so what `PlayerBGCollision` finds depends only on where he is, which `VFacts` and the position bound limit.
-/
namespace Smb.Goal.OneOne

open Smb.Abs Smb.Abs.LaunchPhase
open Smb.Routine
open Smb.Routine.HorizontalLimit (pixelP leftL edgeR)
open Smb.Routine.LaunchPhase (forall_u8 forall_u16)

/-- The block buffer's cells near Mario. -/
def inBuf (a : UInt16) : Bool := 0x500 ≤ a && a < 0x5D0 && a &&& 0xF < 7

/-- What the buffer holds there. -/
def bufTile (a : UInt16) : UInt8 := bif 0x5B0 ≤ a then 0x54 else 0

/-- Nothing but `v` is in bounds at `a`. -/
def onlyAt (a : UInt16) (v : UInt8) (x : UInt8) : Bool := !((gAt G a).mem x) || x == v

def onlyAll (a : UInt16) (v : UInt8) : Bool := (List.range 256).all fun n => onlyAt a v (UInt8.ofNat n)

theorem only_sound {a : UInt16} {v x : UInt8} (h : onlyAll a v = true) (hm : (gAt G a).mem x = true) : x = v := by
  have h2 := forall_u8 (onlyAt a v) h x
  simpa [onlyAt, hm] using h2

def bufOk (a : UInt16) : Bool := !inBuf a || onlyAll a (bufTile a)

theorem g_buf : (List.range 0x10000).all (fun n => bufOk (UInt16.ofNat n)) = true := by native_decide

theorem buf_of_glob {R : UInt16 → UInt8} (hG : ∀ i, (gAt G i).mem (R i) = true) (a : UInt16) (ha : inBuf a = true) : R a = bufTile a := by
  have h := forall_u16 bufOk g_buf a
  simp only [bufOk, ha, Bool.not_true, Bool.false_or] at h
  exact only_sound h (hG a)

/-- A probe's address, in its parts. -/
def addrOf (X Y xa ya : UInt8) : UInt16 :=
  let c : UInt8 := bif xa.toUInt16 + X.toUInt16 > 0xFF then 1 else 0
  let col : UInt8 := ((((0 : UInt8) + c) &&& 1) <<< 4) ||| ((xa + X) >>> 4)
  ((0x05 : UInt16) <<< 8 ||| ((col &&& 0x0F) + (bif col >>> 4 == 0 then 0x00 else 0xD0)).toUInt16) + (((Y + ya) &&& 0xF0) - 0x20).toUInt16

theorem addr_mask (X Y xa ya : UInt8) (hxa : xa ≤ 0x10) (hya : ya ≤ 0x20) (hX : X < 0x60) (hY1 : 0x40 ≤ Y) (hY2 : Y < 0xC0) :
    addrOf X Y xa ya &&& 0x7FF = addrOf X Y xa ya ∧ inBuf (addrOf X Y xa ya) = true ∧
      bufTile (addrOf X Y xa ya) = bif 0xD0 ≤ (Y + ya) &&& 0xF0 then 0x54 else 0 := by
  simp only [addrOf, inBuf, bufTile]
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide (config := { enums := false })

/-- A tile from the buffer, for a probe that stays where it's bounded. -/
theorem tile_eq (R : UInt16 → UInt8) (k xa ya : UInt8) (hx : bbXAdd romFn k = xa) (hy : bbYAdd romFn k = ya) (hxa : xa ≤ 0x10) (hya : ya ≤ 0x20)
    (hpage : R 0x6D = 0) (hX : R 0x86 < 0x60) (hY1 : 0x40 ≤ R 0xCE) (hY2 : R 0xCE < 0xC0) (hb : ∀ a, inBuf a = true → R a = bufTile a) :
    bbTile romFn R 0 k = bif 0xD0 ≤ (R 0xCE + ya) &&& 0xF0 then 0x54 else 0 := by
  have e86 : ((0x86 : UInt8) + 0).toUInt16 &&& 0x7FF = 0x86 := by decide
  have eCE : ((0xCE : UInt8) + 0).toUInt16 &&& 0x7FF = 0xCE := by decide
  have e6D : ((0x6D : UInt8) + 0).toUInt16 &&& 0x7FF = 0x6D := by decide
  have hA : bbAddr romFn R 0 k = addrOf (R 0x86) (R 0xCE) xa ya := by
    simp only [bbAddr, bbLo, bbColumn, bbXSum, bbRow, bbXPos, bbYPos, bbPage, e86, eCE, e6D, hpage, hx, hy, addrOf]
  obtain ⟨h1, h2, h3⟩ := addr_mask (R 0x86) (R 0xCE) xa ya hxa hya hX hY1 hY2
  simp only [bbTile, hA, h1]
  rw [hb _ h2, h3]

/-- The ROM's adders for small Mario's sensors. -/
theorem rom_adds : bbXAdd romFn 0x0E = 0x08 ∧ bbYAdd romFn 0x0E = 0x12 ∧ bbXAdd romFn 0x0F = 0x03 ∧ bbYAdd romFn 0x0F = 0x20 ∧ bbXAdd romFn 0x10 = 0x0C ∧ bbYAdd romFn 0x10 = 0x20 ∧
    bbXAdd romFn 0x11 = 0x02 ∧ bbYAdd romFn 0x11 = 0x18 ∧ bbXAdd romFn 0x12 = 0x02 ∧ bbYAdd romFn 0x12 = 0x18 ∧ bbXAdd romFn 0x13 = 0x0D ∧ bbYAdd romFn 0x13 = 0x18 ∧
    bbXAdd romFn 0x14 = 0x0D ∧ bbYAdd romFn 0x14 = 0x18 := by native_decide

theorem head_row (y : UInt8) (h : y < 176 ∨ (y &&& 15 < 5 ∧ y < 192)) : ¬ (0xD0 ≤ (y + 0x12) &&& 0xF0) ∧ ¬ (0xD0 ≤ (y + 0x18) &&& 0xF0) := by
  constructor <;> (revert h; bv_decide (config := { enums := false }))

theorem y_cf (y : UInt8) (h : y < 0xC0) : y < 0xCF := by
  revert h; bv_decide (config := { enums := false })

theorem foot_row (y : UInt8) (hl : 0x40 ≤ y) (h : y < 176 ∨ (y &&& 15 < 5 ∧ y < 192)) (hf : 0xD0 ≤ (y + 0x20) &&& 0xF0) : y &&& 15 < 5 := by
  revert hl h hf; bv_decide (config := { enums := false })

/-- What the sensors need of the state at the start of the collision code. -/
structure AtBg (R : UInt16 → UInt8) : Prop where
  noExit : R 0x716 = 0
  engine : R 0x0E = 8
  high : R 0xB5 = 1
  st : R 0x1D ≤ 2
  swim : R 0x704 = 0
  js : R 0x70E = 0
  small : R 0x754 ≠ 0
  page : R 0x6D = 0
  x : R 0x86 < 0x60
  ylo : 0x40 ≤ R 0xCE
  yhi : R 0xCE < 176 ∨ (R 0xCE &&& 15 < 5 ∧ R 0xCE < 192)
  buf : ∀ a, inBuf a = true → R a = bufTile a

theorem AtBg.yc {R : UInt16 → UInt8} (h : AtBg R) : R 0xCE < 0xC0 := by
  have := h.yhi
  revert this; generalize R 0xCE = y; bv_decide (config := { enums := false })

theorem sensors0_of {R : UInt16 → UInt8} (h : AtBg R) : Sensors0 R := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := rom_adds
  have t (k xa ya : UInt8) (hx : bbXAdd romFn k = xa) (hy : bbYAdd romFn k = ya) (hxa : xa ≤ 0x10) (hya : ya ≤ 0x20) :=
    tile_eq R k xa ya hx hy hxa hya h.page h.x h.ylo h.yc h.buf
  have hr := head_row _ h.yhi
  have fl := t 0x0F 3 0x20 a3 a4 (by decide) (by decide)
  have fr := t 0x10 0xC 0x20 a5 a6 (by decide) (by decide)
  have row (hc : 0xD0 ≤ (R 0xCE + 0x20) &&& 0xF0) := foot_row _ h.ylo h.yhi hc
  have hlow : R 0xCE < 0xCF := y_cf _ h.yc
  refine ⟨h.noExit, h.engine, h.high, hlow, h.st, h.swim, h.js, h.small, ?_, ?_, ?_, ?_⟩
  · rw [t 0x0E 8 0x12 a1 a2 (by decide) (by decide)]
    simp [hr.1]
  · rw [fl]
    by_cases hc : 0xD0 ≤ (R 0xCE + 0x20) &&& 0xF0 <;> simp [hc, floorTile]
  · rw [fr]
    by_cases hc : 0xD0 ≤ (R 0xCE + 0x20) &&& 0xF0 <;> simp [hc, floorTile]
  · rw [fl, fr]
    by_cases hc : 0xD0 ≤ (R 0xCE + 0x20) &&& 0xF0
    · intro _; exact row hc
    · simp [hc, floorTile]

theorem aF_ce (L : Bool) (r : UInt16 → UInt8) : ModelFrame.afterFoot L r 0xCE = r 0xCE ∨ ModelFrame.afterFoot L r 0xCE = r 0xCE &&& 0xF0 := by
  cases L <;> simp [ModelFrame.afterFoot]

theorem foot_buf (y sp : UInt8) (r prg : UInt16 → UInt8) (a : UInt16) (ha : inBuf a = true) : footCheck_ram y sp r prg a = r a := by
  apply footCheck_ram_frame
  simp only [inBuf] at ha
  simp only [footCheck_writes]
  revert ha
  bv_decide (config := { enums := false })

theorem side_row (y y' : UInt8) (hl : 0x40 ≤ y) (h : y < 176 ∨ (y &&& 15 < 5 ∧ y < 192)) (he : y' = y ∨ y' = y &&& 0xF0) :
    0x40 ≤ y' ∧ y' < 0xC0 ∧ ¬ (0xD0 ≤ (y' + 0x18) &&& 0xF0) := by
  rcases he with rfl | rfl <;> (revert hl h; bv_decide (config := { enums := false }))

theorem sensors_of {sp : UInt8} {R : UInt16 → UInt8} (h : AtBg R) : Sensors sp R := by
  have h0 := sensors0_of h
  obtain ⟨f1, f2, _, f4, f5, f6, f7, f8, hpc, heb⟩ := foot_of_sensors (sp := sp) h0
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := rom_adds
  have hg := sensors_go h0
  have hje : bgRam R 0x70E = 0 := by rw [ModelFrame.bgRam_cell R hg 0x70E (by decide) (by decide)]; exact h.js
  have hfoot (i : UInt16) (hi : i = 0xCE ∨ i = 0x86 ∨ i = 0x6D) := ModelFrame.foot_cell (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) romFn i
    (by rcases hi with rfl | rfl | rfl <;> simp) HorizontalLimitNes.rom_climbTable f1 f2 f4 f5 f6 f7 hje f8
  have hF : ∀ i, bgFootRam sp romFn R i = footCheck_ram (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) romFn i := fun _ => rfl
  have hR (i : UInt16) (h1 : i ≠ 0x1D) (h2 : i ≠ 0x490) := ModelFrame.bgRam_cell R hg i h1 h2
  have h86 : bgFootRam sp romFn R 0x86 = R 0x86 := by
    rw [hF, hfoot _ (by simp), ModelFrame.aF_86, hR _ (by decide) (by decide)]
  have h6d : bgFootRam sp romFn R 0x6D = R 0x6D := by
    rw [hF, hfoot _ (by simp), ModelFrame.aF_6d, hR _ (by decide) (by decide)]
  have hce : bgFootRam sp romFn R 0xCE = R 0xCE ∨ bgFootRam sp romFn R 0xCE = R 0xCE &&& 0xF0 := by
    rw [hF, hfoot _ (by simp), ← hR 0xCE (by decide) (by decide)]
    exact aF_ce _ _
  obtain ⟨y1, y2, y3⟩ := side_row _ _ h.ylo h.yhi hce
  have hb : ∀ a, inBuf a = true → bgFootRam sp romFn R a = bufTile a := fun a ha => by
    have hne : a ≠ 0x1D ∧ a ≠ 0x490 := by
      simp only [inBuf] at ha
      constructor <;> (intro e; subst e; revert ha; decide)
    rw [hF, foot_buf _ _ _ _ _ ha, hR a hne.1 hne.2]
    exact h.buf a ha
  have t (k xa ya : UInt8) (hx : bbXAdd romFn k = xa) (hy : bbYAdd romFn k = ya) (hxa : xa ≤ 0x10) (hya : ya ≤ 0x20) :=
    tile_eq (bgFootRam sp romFn R) k xa ya hx hy hxa hya (by rw [h6d]; exact h.page) (by rw [h86]; exact h.x) y1 y2 hb
  have side (k k' xa : UInt8) (he : (0x0E : UInt8) + k = k') (hx : bbXAdd romFn k' = xa) (hy : bbYAdd romFn k' = 0x18) (hxa : xa ≤ 0x10) : sideTile romFn (bgFootRam sp romFn R) k = 0 := by
    simp only [sideTile, heb, he]
    rw [t k' xa 0x18 hx hy hxa (by decide)]
    simp [y3]
  exact { h0 with
    side3 := side 3 0x11 2 rfl a7 a8 (by decide)
    side4 := side 4 0x12 2 rfl a9 a10 (by decide)
    side5 := side 5 0x13 0xD rfl a11 a12 (by decide)
    side6 := side 6 0x14 0xD rfl a13 a14 (by decide) }

theorem foot_split (y : UInt8) (hl : 0x40 ≤ y) (h : y < 176 ∨ (y &&& 15 < 5 ∧ y < 192)) :
    (0xD0 ≤ (y + 0x20) &&& 0xF0 → 176 ≤ y ∧ y &&& 15 < 5 ∧ y < 192) ∧ (¬ 0xD0 ≤ (y + 0x20) &&& 0xF0 → y < 176) := by
  constructor <;> (revert hl h; bv_decide (config := { enums := false }))

/-- Whether Mario lands comes down to where he is and how fast he's falling. -/
theorem lands_of {R : UInt16 → UInt8} (h : AtBg R) (hv : R 0xCE < 176 ∨ R 0x9F < 0x80) (hg : R 0x1D = 0 → R 0xCE = 176 ∧ R 0x9F = 0) :
    lands romFn (bgRam R) (bgY R) = (R 0x1D == 0 || (R 0x1D != 0 && R 0x9F < 0x80 && 176 ≤ R 0xCE && R 0xCE &&& 15 < 5 && R 0xCE < 192)) := by
  have h0 := sensors0_of h
  obtain ⟨f1, _, _, _, _, _, _, _, _, _⟩ := foot_of_sensors (sp := 0) h0
  obtain ⟨_, _, a3, a4, a5, a6, _, _, _, _, _, _, _, _⟩ := rom_adds
  have hg0 := sensors_go h0
  have hy := sensors_y h0
  have ht := sensors_tile h0
  have e0 : bbOffset romFn 2 = 0x0E := rom_offset
  have hR (i : UInt16) (h1 : i ≠ 0x1D) (h2 : i ≠ 0x490) := ModelFrame.bgRam_cell R hg0 i h1 h2
  have fl := tile_eq R 0x0F 3 0x20 a3 a4 (by decide) (by decide) h.page h.x h.ylo h.yc h.buf
  have fr := tile_eq R 0x10 0xC 0x20 a5 a6 (by decide) (by decide) h.page h.x h.ylo h.yc h.buf
  obtain ⟨s1, s2⟩ := foot_split _ h.ylo h.yhi
  have hsp : headSpeed romFn (bgRam R) (bgY R) = R 0x9F := by
    simp [headSpeed, headBumps, f1, hR 0x9F (by decide) (by decide)]
  have hTL : footTileL romFn (bgRam R) (bgY R) = bbTile romFn R 0 0x0F := by
    simp only [footTileL, hy, e0]; exact ht _
  have hTR : footTileR romFn (bgRam R) (bgY R) = bbTile romFn R 0 0x10 := by
    simp only [footTileR, hy, e0]; exact ht _
  simp only [lands, footSolid, footProbed, footTile, hTL, hTR, hsp, hR 0xCE (by decide) (by decide), hR 0x70E (by decide) (by decide), h.js, fl, fr]
  by_cases hc : 0xD0 ≤ (R 0xCE + 0x20) &&& 0xF0
  · obtain ⟨c1, c2, c3⟩ := s1 hc
    have hvy : R 0x9F < 0x80 := by
      rcases hv with hv | hv
      · exact absurd c1 (by simpa [UInt8.not_le] using hv)
      · exact hv
    have hlt : R 0xCE < 0xCF := y_cf _ h.yc
    by_cases hst : R 0x1D = 0 <;> simp [hc, hvy, c1, c2, c3, hlt, hst, climbable, climbExt]
  · have c1 := s2 hc
    have hst : R 0x1D ≠ 0 := fun e => by
      have := (hg e).1
      rw [this] at c1
      exact absurd c1 (by decide)
    have hn : ¬ (176 ≤ R 0xCE) := by simpa [UInt8.not_le] using c1
    simp [hc, hn, hst]

end Smb.Goal.OneOne
