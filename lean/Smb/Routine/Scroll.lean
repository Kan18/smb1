import Smb.Routine.ScrollHandler

namespace Smb.Routine
/-! ## What it does to Mario -/

/-- A 16-bit position `page : x`. -/
def pos16 (page x : UInt8) : UInt16 := page.toUInt16 <<< 8 ||| x.toUInt16

/-- `GetXOffscreenBits`' right-edge test in terms of `R − P` (mod 2^16). -/
theorem offBits_right (ex ep ox op : UInt8) :
    let D := pos16 ep ex - pos16 op ox
    let b := offBits true ex ep ox op
    (b &&& 0x80 != 0) = (D ≥ 0x8000) ∧ (b &&& 0x80 == 0 && b &&& 0x20 != 0) = (D < 0x10) ∧
    (b == 0) = (0x38 ≤ D && D < 0x8000) := by
  simp only [offBits, edgePageDiff, pos16, bne]
  bv_decide

/-- … and its left-edge test in terms of `L − P`. -/
theorem offBits_left (ex ep ox op : UInt8) :
    let D := pos16 ep ex - pos16 op ox
    let b := offBits false ex ep ox op
    (b == 0) = (D ≥ 0x8000) ∧ (b &&& 0x80 != 0) = (D < 0x8000) := by
  simp only [offBits, edgePageDiff, pos16, bne]
  bv_decide

set_option maxRecDepth 20000 in
/-- Mario's position, speed and vertical state after `ScrollHandler`. `L`, `R`: the screen
edges after the scroll; `P`: Mario's position before. -/
theorem scrollRam_spec (sp : UInt8) (ram : UInt16 → UInt8) :
    let r := scrollRam sp ram
    let P := pos16 (ram 0x6D) (ram 0x86)
    let L := pos16 (scrLeftPage ram) (scrLeftX ram)
    let R := pos16 (scrRightPage ram) (scrRightX ram)
    let toLeft := R - P ≥ 0x8000 || (0x38 ≤ R - P && L - P < 0x8000)
    let toRight := R - P < 0x10
    pos16 (r 0x6D) (r 0x86) = (bif toLeft then L else bif toRight then R - 0x10 else P) ∧
    r 0x57 = (bif (toLeft && ram 0x0C != 1) || (toRight && ram 0x0C != 2) then 0 else ram 0x57) ∧
    r 0x400 = ram 0x400 ∧ r 0x9F = ram 0x9F ∧ r 0x433 = ram 0x433 ∧ r 0x416 = ram 0x416 ∧
    r 0xCE = ram 0xCE ∧ r 0xB5 = ram 0xB5 := by
  sym_exec [scrollRam, stopsSpeed, clampPage, clampX, clampRight, clampLeft, scrBits, gxoRam,
    gxoCalled, gxoBits, gxoL, gxoR, objX, objPage, offDiv, offBits, edgePageDiff, scrMid, pos16,
    scrLeftX, scrLeftPage, scrRightX, scrRightPage, bne]
  fun_congr
  bv_decide (config := { enums := false })

set_option maxRecDepth 20000 in
/-- Only these bytes change: `$00`, `$04`–`$07`, four stack bytes, Mario's position and speed
(`$6D`, `$86`, `$57`), the platform force, and the scroll variables. -/
theorem scrollRam_frame (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16)
    (hi : i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 5 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 0x57 ∧ i ≠ 0x6D ∧ i ≠ 0x86 ∧ i ≠ 0x3A1 ∧
      i ≠ 0x6FF ∧ i ≠ 0x71A ∧ i ≠ 0x71B ∧ i ≠ 0x71C ∧ i ≠ 0x71D ∧ i ≠ 0x73D ∧ i ≠ 0x73F ∧
      i ≠ 0x775 ∧ i ≠ 0x778 ∧ i ≠ 0x795 ∧
      i ≠ (0x100 ||| sp.toUInt16) &&& 0x7FF ∧ i ≠ (0x100 ||| (sp + 255).toUInt16) &&& 0x7FF ∧
      i ≠ (0x100 ||| (sp + 254).toUInt16) &&& 0x7FF ∧ i ≠ (0x100 ||| (sp + 253).toUInt16) &&& 0x7FF) :
    scrollRam sp ram i = ram i := by
  simp only [scrollRam, gxoRam, scrMid, bne]
  fun_congr
  bv_decide (config := { enums := false })

/-- Precondition of `scrollRam_clamp`: the right screen edge is the left one plus 255, as
`GetScreenPosition` sets it. It holds after any frame in which the screen scrolls (the
routine recomputes the right edge), so it is needed only for frames without a scroll; whether
every other writer of `$071A`–`$071D` keeps it is not checked here. -/
def screenEdgesConsistent (ram : UInt16 → UInt8) : Bool :=
  pos16 (ram 0x71B) (ram 0x71D) == pos16 (ram 0x71A) (ram 0x71C) + 0xFF

set_option maxRecDepth 20000 in
/-- With consistent edges, in terms of Mario's offset `D = P − L` from the left edge. -/
theorem scrollRam_clamp (sp : UInt8) (ram : UInt16 → UInt8)
    (h : (scrolls ram || screenEdgesConsistent ram) = true) :
    let r := scrollRam sp ram
    let L := pos16 (scrLeftPage ram) (scrLeftX ram)
    let D := pos16 (ram 0x6D) (ram 0x86) - L
    let toLeft := D == 0 || D ≥ 0x100
    let toRight := 0xF0 ≤ D && D < 0x100
    pos16 (r 0x6D) (r 0x86) = (bif toLeft then L else bif toRight then L + 0xEF else L + D) ∧
    r 0x57 = (bif (toLeft && ram 0x0C != 1) || (toRight && ram 0x0C != 2) then 0 else ram 0x57) := by
  have hs := scrollRam_spec sp ram
  have hR : pos16 (scrRightPage ram) (scrRightX ram) = pos16 (scrLeftPage ram) (scrLeftX ram) + 0xFF := by
    revert h
    simp only [screenEdgesConsistent, scrRightPage, scrRightX, scrLeftPage, scrLeftX, pos16, bne]
    generalize scrolls ram = s
    generalize scrAmt ram = amt
    cases s <;> simp only [Bool.cond_true, Bool.cond_false, Bool.true_or, Bool.false_or] <;> bv_decide
  simp only [] at hs ⊢
  rw [hR] at hs
  generalize scrollRam sp ram = r at hs ⊢
  generalize pos16 (scrLeftPage ram) (scrLeftX ram) = L at hs ⊢
  simp only [pos16, bne] at hs ⊢
  bv_decide

end Smb.Routine
