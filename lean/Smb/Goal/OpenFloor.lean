import Smb.Goal.FrameContract
import Smb.Routine.MemoryContracts

/-!
# Collision on open ground, from what the sensors read

`OpenBg` lists what `PlayerBGCollision` has to find. For small Mario over a floor, with nothing else near, all of it comes from the tiles at his sensors. Which tiles those are comes from the block buffer, which is a separate question.
-/
namespace Smb.Goal.OneOne

open Smb.Routine

/-- The floor's tile in 1-1. -/
def floorTile : UInt8 := 0x54

/-- The head and foot sensors for small Mario read nothing but, under his feet, the floor. -/
structure Sensors0 (R : UInt16 → UInt8) : Prop where
  noExit : R 0x716 = 0
  engine : R 0x0E = 8
  high : R 0xB5 = 1
  low : R 0xCE < 0xCF
  st : R 0x1D ≤ 2
  swim : R 0x704 = 0
  js : R 0x70E = 0
  small : R 0x754 ≠ 0
  head : bbTile romFn R 0 0x0E = 0
  footL : bbTile romFn R 0 0x0F = 0 ∨ bbTile romFn R 0 0x0F = floorTile
  footR : bbTile romFn R 0 0x10 = 0 ∨ bbTile romFn R 0 0x10 = floorTile
  row : (bbTile romFn R 0 0x0F = floorTile ∨ bbTile romFn R 0 0x10 = floorTile) → R 0xCE &&& 15 < 5

/-- And the side sensors read nothing. -/
structure Sensors (sp : UInt8) (R : UInt16 → UInt8) : Prop extends Sensors0 R where
  side3 : sideTile romFn (bgFootRam sp romFn R) 3 = 0
  side4 : sideTile romFn (bgFootRam sp romFn R) 4 = 0
  side5 : sideTile romFn (bgFootRam sp romFn R) 5 = 0
  side6 : sideTile romFn (bgFootRam sp romFn R) 6 = 0

theorem rom_offset : romFn ((58285 : UInt16) + (2 : UInt8).toUInt16 &&& 32767) = 0x0E := by native_decide

theorem rom_offsetAt : romFn ((0xE3AD : UInt16) + (2 : UInt8).toUInt16 &&& 0x7FFF) = 0x0E := by native_decide

theorem sensors_go {R : UInt16 → UInt8} (h : Sensors0 R) : bgPre_pc R = 0xDC98 := by
  have h1 := h.noExit; have h2 := h.engine; have h3 := h.high; have h4 := h.low; have h5 := h.st; have h6 := h.swim
  clear h
  simp only [bgPre_pc, bgPre_c0, bgPre_c1, bgPre_c2, bgPre_c3, bgPre_c4, bgPre_c5, bgPre_c6, bgPre_c7, bgPre_c8, bgPre_c9, bgPre_c10, bgPre_c11, bgPre_c12, bgPre_c13]
  sym_exec [bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

theorem sensors_y {R : UInt16 → UInt8} (h : Sensors0 R) : bgY R = 2 := by
  have hg := sensors_go h
  have e : bgPre_ram R 0x754 = R 0x754 := ModelFrame.bgPre_cell R 0x754 hg (by decide) (by decide)
  have hs := h.small
  rw [← e] at hs
  clear h e hg
  simp only [bgY, bgSize_y, bgSize_c0, bgSize_c1]
  sym_exec [bne] at *
  all_goals
    fun_congr
    bv_decide (config := { enums := false })

theorem sensors_tile {R : UInt16 → UInt8} (h : Sensors0 R) (k : UInt8) : bbTile romFn (bgRam R) 0 k = bbTile romFn R 0 k := by
  have hg := sensors_go h
  apply MemoryContracts.bbTile_congr
  · exact ModelFrame.bgRam_cell R hg 0x86 (by decide) (by decide)
  · exact ModelFrame.bgRam_cell R hg 0xCE (by decide) (by decide)
  · exact ModelFrame.bgRam_cell R hg 0x6D (by decide) (by decide)
  · intro i h1 h2
    refine ModelFrame.bgRam_cell R hg i ?_ ?_
    · intro e; subst e; revert h1; decide
    · intro e; subst e; revert h1; decide

/-- The head and foot predicates, given what the sensors read. -/
theorem open_foot (prg r : UInt16 → UInt8) (y : UInt8)
    (hH : bbTile prg r 0 (bbOffset prg y) = 0)
    (hL : bbTile prg r 0 (bbOffset prg y + 1) = 0 ∨ bbTile prg r 0 (bbOffset prg y + 1) = floorTile)
    (hR : bbTile prg r 0 (bbOffset prg y + 2) = 0 ∨ bbTile prg r 0 (bbOffset prg y + 2) = floorTile)
    (hrow : (bbTile prg r 0 (bbOffset prg y + 1) = floorTile ∨ bbTile prg r 0 (bbOffset prg y + 2) = floorTile) → r 0xCE &&& 15 < 5) :
    headBlocked prg r y = false ∧ headCoin prg r y = false ∧ headHit prg r y = false ∧ footCoin prg r y = false ∧ footAxeAt prg r y = false ∧
      pipeEntryAt prg r y = false ∧ impeded prg r y = false ∧ (footTile prg r y != 0x67 && footTile prg r y != 0x68) = true := by
  have h5 : r 0xCE &&& 15 < 5 ∨ (bbTile prg r 0 (bbOffset prg y + 1) = 0 ∧ bbTile prg r 0 (bbOffset prg y + 2) = 0) := by
    by_cases h : bbTile prg r 0 (bbOffset prg y + 1) = floorTile ∨ bbTile prg r 0 (bbOffset prg y + 2) = floorTile
    · exact Or.inl (hrow h)
    · right
      simp only [not_or] at h
      exact ⟨hL.resolve_right h.1, hR.resolve_right h.2⟩
  simp only [headBlocked, headCoin, headHit, headTile, footCoin, footAxeAt, pipeEntryAt, impeded, lands, footSolid, footProbed, footTile, footTileL, footTileR,
    headSpeed, headBumps, coinTile, hH]
  generalize bbTile prg r 0 (bbOffset prg y + 1) = a at *
  generalize bbTile prg r 0 (bbOffset prg y + 2) = b at *
  generalize headProbed prg r = hp at *
  generalize r 0xCE &&& 15 = q at *
  rcases hL with rfl | rfl <;> rcases hR with rfl | rfl <;> simp [floorTile, climbable, climbExt] <;> simp_all [floorTile] 

/-- What the head and foot sensors give of the foot check. -/
theorem foot_of_sensors {sp : UInt8} {R : UInt16 → UInt8} (h : Sensors0 R) :
    headBlocked romFn (bgRam R) (bgY R) = false ∧ headCoin romFn (bgRam R) (bgY R) = false ∧ headHit romFn (bgRam R) (bgY R) = false ∧ footCoin romFn (bgRam R) (bgY R) = false ∧
      footAxeAt romFn (bgRam R) (bgY R) = false ∧ pipeEntryAt romFn (bgRam R) (bgY R) = false ∧ impeded romFn (bgRam R) (bgY R) = false ∧
      (footTile romFn (bgRam R) (bgY R) != 0x67 && footTile romFn (bgRam R) (bgY R) != 0x68) = true ∧
      footCheck_pc (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) romFn = 0xDD5E ∧ bgFootRam sp romFn R 0xEB = 0x0E := by
  have hg := sensors_go h
  have hy := sensors_y h
  have ht := sensors_tile h
  have e0 : bbOffset romFn 2 = 0x0E := rom_offset
  have e1 : (0x0E : UInt8) + 1 = 0x0F := rfl
  have e2 : (0x0E : UInt8) + 2 = 0x10 := rfl
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := open_foot romFn (bgRam R) (bgY R)
    (by rw [hy, e0, ht]; exact h.head)
    (by rw [hy, e0, e1, ht]; exact h.footL)
    (by rw [hy, e0, e2, ht]; exact h.footR)
    (by rw [hy, e0, e1, e2, ht, ht, ModelFrame.bgRam_cell R hg 0xCE (by decide) (by decide)]; exact h.row)
  have hje : bgRam R 0x70E = 0 := by rw [ModelFrame.bgRam_cell R hg 0x70E (by decide) (by decide)]; exact h.js
  have hpc := ModelFrame.foot_pc (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) romFn HorizontalLimitNes.rom_climbTable f1 f2 f4 f5 f6 f7 hje f8
  refine ⟨f1, f2, f3, f4, f5, f6, f7, f8, hpc, ?_⟩
  show footCheck_ram (bgY R) (bgSize_s (bgPre_s sp)) (bgRam R) romFn 0xEB = _
  rw [ModelFrame.foot_eb _ _ _ _ hpc, hy, rom_offsetAt]

/-- Sensors like these make `OpenBg` true. -/
theorem openBg_of_sensors {sp : UInt8} {R : UInt16 → UInt8} (h : Sensors sp R) : OpenBg sp R := by
  have hg := sensors_go h.toSensors0
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, hpc, heb⟩ := foot_of_sensors (sp := sp) h.toSensors0
  have heb' : bgFootRam sp romFn R 0xEB < 0x16 := by rw [heb]; decide
  have s3 := h.side3; have s4 := h.side4; have s5 := h.side5; have s6 := h.side6
  refine ⟨hg, f1, f2, f3, f4, f5, f6, f7, hpc, heb', f8, ?_, ?_, ?_, ?_, h.js, h.swim, h.st⟩
  · simp [noSideCoin, s3, s4, s5, s6, isCoin]
  · simp [noSideClimb, s4, s6, climbable, climbExt]
  · simp [noSidePipeEntry, s3, s4, s5, s6, pipeEntry]
  · simp [sideBlocks, sideHitProbe, upperHit, s3, s4, s5, s6]

end Smb.Goal.OneOne
