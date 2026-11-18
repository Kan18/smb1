import Smb.Routine.PlayerFramePosition

/-!
# Mario's horizontal speed limit, through movement, scrolling and wall collision

From `PlayerCtrlRoutine` to `PlayerHole` (`$B0E9`–`$B179`), on the existing ground, jumping and falling
frame theorems' execution paths:

- the X speed stays in [-40, 40], the bound `MaximumRightSpeed`/`MaximumLeftSpeed` allow;
- Mario's 24-bit position (`page:x:sub-pixel`) advances by at most 640 = 2.5 pixels.

The per-frame advance is measured by `phi`: his position, or the left screen edge when a wall has
pushed him one pixel behind it. `XInv` lists what the argument needs of the state at entry. It is a
hypothesis here: nothing below shows the rest of the frame preserves it.

This stops before `PlayerHole`, enemies and the NMI. It keeps the frame theorems' exclusions (coins,
head hits, climbing, pipes, the axe, a changing size). Other writers of these bytes, such as platforms, flagpole
and pipe code, are outside it.
-/
namespace Smb.Routine.HorizontalLimit
open Smb.Routine.PlayerFramePosition
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- The X speed, as a signed byte, lies in [-40, 40]. -/
def speedOk (v : UInt8) : Bool := v ≤ 0x28 || 0xD8 ≤ v

/-- A byte's sign extension, for the pixel count in `Player_X_Scroll`. -/
def sext16b (v : UInt8) : UInt16 := bif v < 0x80 then v.toUInt16 else v.toUInt16 ||| 0xFF00

/-- Page, pixel and sub-pixel as one 24-bit position. -/
def pack (p : UInt16) (s : UInt8) : UInt32 := p.toUInt32 <<< 8 ||| s.toUInt32

/-- `new` is at most `lim` ahead of `old` and not far behind it, in 24-bit arithmetic. -/
def fwdLe (new old lim : UInt32) : Bool :=
  let d := (new - old) &&& 0xFFFFFF
  d ≤ lim || 0xFE0000 ≤ d

/-- `fwdLe` with room for the one more pixel a wall can push Mario back. -/
def fwdLe' (new old lim : UInt32) : Bool :=
  let d := (new - old) &&& 0xFFFFFF
  d ≤ lim || 0xFF0000 ≤ d

def pixelP (ram : UInt16 → UInt8) : UInt16 := pos16 (ram 0x6D) (ram 0x86)
def leftL (ram : UInt16 → UInt8) : UInt16 := pos16 (ram 0x71A) (ram 0x71C)
def edgeR (ram : UInt16 → UInt8) : UInt16 := pos16 (ram 0x71B) (ram 0x71D)

/-- Mario's progress measure: his position, or the screen's left edge if he is just behind it. -/
def phi (ram : UInt16 → UInt8) : UInt32 :=
  bif pixelP ram - leftL ram < 0x8000 then pack (pixelP ram) (ram 0x400) else pack (leftL ram) 0

/-- What the argument needs at `PlayerCtrlRoutine`'s entry. `$0755` is last frame's on-screen X and
`$0785` the side-collision timer; between them they stop the screen scrolling past him. -/
def XInv (ram : UInt16 → UInt8) : Prop :=
  speedOk (ram 0x57) = true ∧ edgeR ram = leftL ram + 255 ∧ ram 0x3A1 = 0 ∧
  (pixelP ram - leftL ram ≤ 0xF0 ∨ pixelP ram - leftL ram = 0xFFFF) ∧
  (0x50 ≤ ram 0x755 → ram 0x785 = 0 → pixelP ram - leftL ram ≠ 0 ∧ pixelP ram - leftL ram < 0x8000)

/-- What one frame's control and collision code gives. -/
def XStep (ram out : UInt16 → UInt8) : Prop :=
  speedOk (out 0x57) = true ∧ edgeR out = leftL out + 255 ∧ out 0x3A1 = 0 ∧
  (pixelP out - leftL out ≤ 0xF0 ∨ (pixelP out - leftL out = 0xFFFF ∧ out 0x785 = 0x10)) ∧
  fwdLe (phi out) (phi ram) 640 = true ∧
  leftL out - leftL ram ≤ 3 ∧ pixelP out - pixelP ram + 4 ≤ 8

/-! ## Movement -/

/-- What `PlayerMovementSubs` does to the horizontal state. -/
def MoveX (ram out : UInt16 → UInt8) : Prop :=
  speedOk (out 0x57) = true ∧
  pos24 out 0 = (pos24 ram 0 + sext (out 0x57) * 16) &&& 0xFFFFFF ∧
  pos16 (out 0x6D) (out 0x86) = pos16 (ram 0x6D) (ram 0x86) + sext16b (out 0x6FF)

macro "ms_x_tac" msr:ident c0:ident : tactic => `(tactic| (
  simp only [MoveX]
  refine ⟨?_, ?_, ?_⟩ <;>
  (sym_exec [$msr:ident, $c0:ident, startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam,
    gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, tbl3, xSpeedClass,
    xFrictionClass, xRunning, speedOk, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx,
    pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx,
    ySpeedIdx, jumpYSpeed, jumpClass, tbl7, bne] at *
   fun_congr
   bv_decide (config := { enums := false }))))

theorem ms0_x (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hv : speedOk (ram 0x57) = true) : MoveX ram (ms0_ram sp ram) := by
  ms_x_tac ms0_ram ms0_c0

theorem ms1_x (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hv : speedOk (ram 0x57) = true) : MoveX ram (ms1_ram sp ram) := by
  ms_x_tac ms1_ram ms1_c0

theorem ms2_x (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hv : speedOk (ram 0x57) = true) : MoveX ram (ms2_ram sp ram) := by
  ms_x_tac ms2_ram ms2_c0

/-- Bytes the movement summaries read through unchanged, and scroll and collision later need. -/
def carried (i : UInt16) : Bool :=
  i == 0x71A || i == 0x71B || i == 0x71C || i == 0x71D || i == 0x3A1 || i == 0x755 || i == 0x785

theorem ms0_keeps (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) (hi : carried i = true) :
    ms0_ram sp ram i = ram i := by
  apply ms0_ram_frame; simp only [carried] at hi; simp only [ms0_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; bv_decide (config := { enums := false })
theorem ms1_keeps (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) (hi : carried i = true) :
    ms1_ram sp ram i = ram i := by
  apply ms1_ram_frame; simp only [carried] at hi; simp only [ms1_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; bv_decide (config := { enums := false })
theorem ms2_keeps (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) (hi : carried i = true) :
    ms2_ram sp ram i = ram i := by
  apply ms2_ram_frame; simp only [carried] at hi; simp only [ms2_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; bv_decide (config := { enums := false })

/-! ## Scrolling and Mario's clamp at the screen edges -/

/-- The scroll stage's result, for a Mario who moved from `(P0, s0)` to the position in `r`. -/
theorem scroll_step (sp : UInt8) (r : UInt16 → UInt8) (P0 : UInt16) (s0 : UInt8)
    (hv : speedOk (r 0x57) = true)
    (hpos : pack (pixelP r) (r 0x400) = (pack P0 s0 + sext (r 0x57) * 16) &&& 0xFFFFFF)
    (hpx : pixelP r = P0 + sext16b (r 0x6FF))
    (hplat : r 0x3A1 = 0)
    (hscr : 0x50 ≤ r 0x755 → r 0x785 = 0 → P0 - leftL r ≠ 0 ∧ P0 - leftL r < 0x8000)
    (hedge : edgeR r = leftL r + 255)
    (hD : P0 - leftL r ≤ 0xF0 ∨ P0 - leftL r = 0xFFFF) :
    let s := scrollRam sp r
    let base := bif P0 - leftL r < 0x8000 then pack P0 s0 else pack (leftL r) 0
    s 0x400 = r 0x400 ∧ speedOk (s 0x57) = true ∧ s 0x3A1 = 0 ∧
    edgeR s = leftL s + 255 ∧ pixelP s - leftL s ≤ 0xEF ∧
    fwdLe' (pack (pixelP s) (s 0x400)) base 640 = true ∧
    ((s 0x57 - 1) &&& 0x80 != 0 → fwdLe' (pack (pixelP s + 1) (s 0x400)) base 640 = true) ∧
    leftL s - leftL r ≤ 3 ∧ pixelP s - P0 + 3 ≤ 6 := by
  have hc := scrollRam_clamp sp r (by
    simp only [screenEdgesConsistent, Bool.or_eq_true, beq_iff_eq]
    right
    simpa only [edgeR, leftL] using hedge)
  have h400 : scrollRam sp r 0x400 = r 0x400 := by
    apply scrollRam_frame; bv_decide (config := { enums := false })
  have h3a1 : scrollRam sp r 0x3A1 = 0 := by simp [scrollRam]
  have hL : scrollRam sp r 0x71C = scrLeftX r ∧ scrollRam sp r 0x71A = scrLeftPage r ∧
      scrollRam sp r 0x71D = scrRightX r ∧ scrollRam sp r 0x71B = scrRightPage r := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [scrollRam, gxoRam, scrMid, scrLeftX, scrLeftPage, scrRightX, scrRightPage, bne]
      fun_congr
      bv_decide (config := { enums := false })
  dsimp only at hc ⊢
  obtain ⟨hL1, hL2, hR1, hR2⟩ := hL
  simp only [edgeR, leftL, pixelP, h400, h3a1, hL1, hL2, hR1, hR2] at hc hedge hD hpx hpos hscr ⊢
  generalize scrollRam sp r 0x6D = op at hc ⊢
  generalize scrollRam sp r 0x86 = ox at hc ⊢
  generalize scrollRam sp r 0x57 = ov at hc ⊢
  clear hL1 hL2 hR1 hR2 h400 h3a1
  simp only [pack, fwdLe', speedOk, sext, sext16b, scrLeftX, scrLeftPage, scrRightX, scrRightPage, scrolls, scrAmt,
    scrPxs, pos16, hplat, bne] at *
  bv_decide (config := { enums := false })

/-! ## Wall collision -/

/-- What collision code does to the horizontal state: nothing, or a one-pixel push with the
speed zeroed, in the direction `ImpedePlayerMove` allows. -/
def BgX (ram out : UInt16 → UInt8) : Prop :=
  out 0x400 = ram 0x400 ∧
  ((pixelP out = pixelP ram ∧ out 0x57 = ram 0x57) ∨
   (pixelP out = pixelP ram + 1 ∧ out 0x57 = 0 ∧ out 0x785 = 0x10 ∧ (ram 0x57 - 1) &&& 0x80 != 0) ∨
   (pixelP out = pixelP ram - 1 ∧ out 0x57 = 0 ∧ out 0x785 = 0x10 ∧ ram 0x57 &&& 0x80 == 0))

theorem side_x (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) : BgX ram (sideRam w sp prg ram) := by
  simp only [BgX, sideRam, sideScratch, impedeRam, impedeInto, stackAt, pixelP, pos16]
  bv_decide (config := { enums := false })

/-- A foot-check exit into the side check never moved Mario. -/
theorem foot_side_x (y sp : UInt8) (ram prg : UInt16 → UInt8)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (h : footCheck_pc y sp ram prg = 0xDD5E) (i : UInt16) (hi : i = 0x57 ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400) :
    footCheck_ram y sp ram prg i = ram i := by
  have hh := headPart_keeps y sp 4 ram prg (by decide) i (by rcases hi with rfl|rfl|rfl|rfl <;> decide)
  rcases htbl with ⟨h0,h1,h2,h3⟩
  rcases hi with rfl|rfl|rfl|rfl <;>
  · sym_exec [footCheck_pc, footCheck_ram, chkFoot_ram,
      chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, chkFoot_c5, chkFoot_c6, chkFoot_c7,
      chkFoot_c8, chkFoot_c9, chkFoot_c10, chkFoot_c11, chkFoot_c12, chkFoot_c13, chkFoot_c14, chkFoot_c15, chkFoot_c16,
      chkFoot_c17, chkFoot_c18, chkFoot_c19, chkFoot_c20, chkFoot_c21, chkFoot_c22, chkFoot_c23,
      footCheck_c0, footCheck_c1, footCheck_c2, footCheck_c3, footCheck_c4, footCheck_c5, footCheck_c6, footCheck_c7,
      footCheck_c8, footCheck_c9, footCheck_c10, footCheck_c11, footCheck_c12, footCheck_c13, footCheck_c14,
      footAxe, footGround, pipeDown, climbable, climbExt, bne] at *
    fun_congr
    bv_decide (config := { enums := false })

/-- The foot check, whatever its exit. -/
theorem foot_x (y sp : UInt8) (ram prg : UInt16 → UInt8) : BgX ram (footCheck_ram y sp ram prg) := by
  have hh := fun (i : UInt16) (hi : i = 0x57 ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400) =>
    headPart_keeps y sp 4 ram prg (by decide) i (by rcases hi with rfl|rfl|rfl|rfl <;> decide)
  have h57 := hh 0x57 (by simp)
  have h86 := hh 0x86 (by simp)
  have h6d := hh 0x6D (by simp)
  have h400 := hh 0x400 (by simp)
  clear hh
  simp only [BgX, pixelP, pos16]
  sym_exec [footCheck_ram, chkFoot_ram,
      chkFoot_c0, chkFoot_c1, chkFoot_c2, chkFoot_c3, chkFoot_c4, footAxe, footGround, pipeDown, bne] at *
  fun_congr
  bv_decide (config := { enums := false })

/-! ## Composition -/

/-- The stack writes on the way to `ScrollHandler`. -/
def auxIn (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) : UInt8 :=
  bif i == (256 ||| (sp + 255).toUInt16) &&& 2047 then 78
  else bif i == (256 ||| sp.toUInt16) &&& 2047 then 177 else ram i

theorem auxIn_eta (sp : UInt8) (ram : UInt16 → UInt8) :
    (fun i : UInt16 => bif i == (256 ||| (sp + 255).toUInt16) &&& 2047 then (78 : UInt8)
      else bif i == (256 ||| sp.toUInt16) &&& 2047 then 177 else ram i) = auxIn sp ram := rfl

/-- A byte outside the stack page reads through the stack writes. -/
theorem auxIn_at (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16) (hi : (i < 0x100 || 0x200 ≤ i) = true) :
    auxIn sp ram i = ram i := by
  simp only [auxIn]
  bv_decide (config := { enums := false })

def auxByte (i : UInt16) : Bool :=
  i == 0x57 || i == 0x86 || i == 0x6D || i == 0x400 || i == 0x71A || i == 0x71B || i == 0x71C || i == 0x71D ||
  i == 0x3A1 || i == 0x785

theorem ctrlAux_x (sp : UInt8) (ram prg : UInt16 → UInt8) (i : UInt16) (hi : auxByte i = true) :
    ctrlAux_ram sp ram prg i = scrollRam sp (auxIn sp ram) i := by
  have h : i = 0x57 ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400 ∨ i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨
      i = 0x3A1 ∨ i = 0x785 := by
    simp only [auxByte] at hi; bv_decide (config := { enums := false })
  have a := auxIn_at sp ram
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · sym_exec [ctrlAux_ram, bbcRam, rppRam, gpoRam, gpoMid, gyoRam, absIdx, dummyIdx, forceIdx, pageIdx, posIdx,
      speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx, scrollRam, gxoRam, auxIn_eta, scrMid, a, bne]

theorem pos24_pack (ram : UInt16 → UInt8) : pos24 ram 0 = pack (pixelP ram) (ram 0x400) := by
  sym_exec [pos24, pageIdx, posIdx, forceIdx, pack, pixelP, pos16]
  bv_decide (config := { enums := false })

/-- What the scroll stage gives, stated against the entry state. -/
def ScrollOut (ram C : UInt16 → UInt8) : Prop :=
  speedOk (C 0x57) = true ∧ C 0x3A1 = 0 ∧ edgeR C = leftL C + 255 ∧ pixelP C - leftL C ≤ 0xEF ∧
  fwdLe' (pack (pixelP C) (C 0x400)) (phi ram) 640 = true ∧
  ((C 0x57 - 1) &&& 0x80 != 0 → fwdLe' (pack (pixelP C + 1) (C 0x400)) (phi ram) 640 = true) ∧
  leftL C - leftL ram ≤ 3 ∧ pixelP C - pixelP ram + 3 ≤ 6

/-- Movement in `M` from the state `ram`, then `ctrlMid` and `ScrollHandler`. -/
theorem ctrl_stage (sp : UInt8) (ram prg M : UInt16 → UInt8) (hinv : XInv ram)
    (hm : MoveX ram M) (hk : ∀ i, carried i = true → M i = ram i) :
    ScrollOut ram (ctrlAux_ram sp (ctrlMid_ram M) prg) := by
  have hmid (i : UInt16) (hi : (i != 1177 && i != 69) = true) : ctrlMid_ram M i = M i := by
    apply ctrlMid_ram_frame; simp only [ctrlMid_writes]; simp only [bne] at hi; bv_decide (config := { enums := false })
  obtain ⟨hv0, he0, hp0, hd0, hs0⟩ := hinv
  obtain ⟨hv, hpos, hpx⟩ := hm
  let r := auxIn sp (ctrlMid_ram M)
  have hr (i : UInt16) (hi : ((i < 0x100 || 0x200 ≤ i) && i != 1177 && i != 69) = true) : r i = M i := by
    have h1 : (i < 0x100 || 0x200 ≤ i) = true := by simp only [bne] at hi; bv_decide (config := { enums := false })
    have h2 : (i != 1177 && i != 69) = true := by simp only [bne] at hi ⊢; bv_decide (config := { enums := false })
    show auxIn sp (ctrlMid_ram M) i = M i
    rw [auxIn_at _ _ _ h1, hmid i h2]
  have r57 := hr 0x57 (by decide)
  have r6d := hr 0x6D (by decide)
  have r86 := hr 0x86 (by decide)
  have r400 := hr 0x400 (by decide)
  have r6ff := hr 0x6FF (by decide)
  have r3a1 := (hr 0x3A1 (by decide)).trans (hk 0x3A1 (by decide))
  have r755 := (hr 0x755 (by decide)).trans (hk 0x755 (by decide))
  have r785 := (hr 0x785 (by decide)).trans (hk 0x785 (by decide))
  have r71a := (hr 0x71A (by decide)).trans (hk 0x71A (by decide))
  have r71b := (hr 0x71B (by decide)).trans (hk 0x71B (by decide))
  have r71c := (hr 0x71C (by decide)).trans (hk 0x71C (by decide))
  have r71d := (hr 0x71D (by decide)).trans (hk 0x71D (by decide))
  have hL : leftL r = leftL ram := by simp only [leftL, r71a, r71c]
  have hR : edgeR r = edgeR ram := by simp only [edgeR, r71b, r71d]
  have hpM : pixelP r = pixelP M := by simp only [pixelP, r6d, r86]
  have hstep := scroll_step sp r (pixelP ram) (ram 0x400)
    (by rw [r57]; exact hv)
    (by
      rw [pos24_pack, pos24_pack] at hpos
      rw [r400, hpM, r57]
      exact hpos)
    (by rw [hpM, r6ff]; simpa only [pixelP] using hpx)
    (by rw [r3a1]; exact hp0)
    (by
      intro h1 h2
      rw [r755] at h1; rw [r785] at h2; rw [hL]
      exact hs0 h1 h2)
    (by rw [hR, hL]; exact he0)
    (by rw [hL]; exact hd0)
  have hC (i : UInt16) (hi : auxByte i = true) :
      ctrlAux_ram sp (ctrlMid_ram M) prg i = scrollRam sp r i := ctrlAux_x sp _ prg i hi
  have hbase : phi ram = (bif pixelP ram - leftL r < 0x8000 then pack (pixelP ram) (ram 0x400) else pack (leftL r) 0) := by
    rw [hL]; rfl
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hstep
  rw [hL] at h7
  simp only [ScrollOut, pixelP, leftL, edgeR, hC 0x57 (by decide), hC 0x3A1 (by decide), hC 0x71A (by decide),
    hC 0x71B (by decide), hC 0x71C (by decide), hC 0x71D (by decide), hC 0x6D (by decide), hC 0x86 (by decide),
    hC 0x400 (by decide)]
  rw [hbase]
  exact ⟨h1, h2, h3, h4, h5, h6, by simpa only [leftL] using h7, by simpa only [pixelP] using h8⟩

/-- Scroll output and one collision step give the whole statement. -/
theorem finish_stage (ram C b : UInt16 → UInt8) (hC : ScrollOut ram C) (hb : BgX C b)
    (h71a : b 0x71A = C 0x71A) (h71b : b 0x71B = C 0x71B) (h71c : b 0x71C = C 0x71C) (h71d : b 0x71D = C 0x71D)
    (h3a1 : b 0x3A1 = C 0x3A1) : XStep ram b := by
  obtain ⟨hv, hp, he, hd, h1, h2, h3, h4⟩ := hC
  obtain ⟨h400, hb⟩ := hb
  have hphi : phi b = bif pixelP b - leftL b < 0x8000 then pack (pixelP b) (b 0x400) else pack (leftL b) 0 := rfl
  simp only [XStep, hphi]
  clear hphi
  generalize phi ram = base at *
  simp only [leftL, edgeR, h71a, h71b, h71c, h71d, h3a1, h400] at he hd h2 h3 h4 ⊢
  generalize pixelP C = Pc at *
  generalize pixelP b = Pb at *
  simp only [pack, fwdLe, fwdLe', speedOk, pos16, bne] at *
  bv_decide (config := { enums := false })

theorem ctrlJ_out (s : UInt8) (ram C : UInt16 → UInt8) (h : ScrollOut ram C) : ScrollOut ram (ctrlJ_ram s C) := by
  have hk (i : UInt16) (hi : auxByte i = true) : ctrlJ_ram s C i = C i := by
    simp only [auxByte] at hi
    sym_exec [ctrlJ_ram]
    bv_decide (config := { enums := false })
  simp only [ScrollOut, pixelP, leftL, edgeR, hk 0x57 (by decide), hk 0x3A1 (by decide), hk 0x71A (by decide),
    hk 0x71B (by decide), hk 0x71C (by decide), hk 0x71D (by decide), hk 0x6D (by decide), hk 0x86 (by decide),
    hk 0x400 (by decide)]
  simpa only [ScrollOut, pixelP, leftL, edgeR] using h

/-- The attribute update at the end of the region leaves the horizontal bytes alone. -/
theorem attr_step (ram b : UInt16 → UInt8) (h : XStep ram b) : XStep ram (ctrlAttr_ram b) := by
  have hk (i : UInt16) (hi : auxByte i = true) : ctrlAttr_ram b i = b i := by
    simp only [auxByte] at hi
    sym_exec [ctrlAttr_ram]
    bv_decide (config := { enums := false })
  simp only [XStep, phi, pixelP, leftL, edgeR] at h
  simp only [XStep, phi, pixelP, leftL, edgeR, hk 0x57 (by decide), hk 0x3A1 (by decide), hk 0x71A (by decide),
    hk 0x71B (by decide), hk 0x71C (by decide), hk 0x71D (by decide), hk 0x6D (by decide), hk 0x86 (by decide),
    hk 0x400 (by decide), hk 0x785 (by decide)]
  exact h

/-! ### The three ways out of `PlayerBGCollision` -/

theorem pre_keeps (ram : UInt16 → UInt8) (i : UInt16) (hi : auxByte i = true) : bgPre_ram ram i = ram i := by
  apply bgPre_ram_frame
  simp only [auxByte] at hi
  simp only [bgPre_writes]
  bv_decide (config := { enums := false })

theorem bgRam_keeps (ram : UInt16 → UInt8) (i : UInt16) (hi : auxByte i = true) : bgRam ram i = ram i := by
  simpa only [bgRam, bgSize_ram] using pre_keeps ram i hi

theorem bgX_of_reads (ram mid out : UInt16 → UInt8) (h : BgX mid out)
    (h57 : mid 0x57 = ram 0x57) (h6d : mid 0x6D = ram 0x6D) (h86 : mid 0x86 = ram 0x86) (h400 : mid 0x400 = ram 0x400) :
    BgX ram out := by
  simpa only [BgX, pixelP, h57, h6d, h86, h400] using h

theorem bgSide_x (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (h : footCheck_pc (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg = 0xDD5E) :
    BgX ram (bgSide_ram w sp ram prg) := by
  have hf (i : UInt16) (hi : i = 0x57 ∨ i = 0x86 ∨ i = 0x6D ∨ i = 0x400) :
      footCheck_ram (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg i = ram i := by
    rw [foot_side_x _ _ _ prg htbl h i hi]
    exact bgRam_keeps ram i (by rcases hi with rfl|rfl|rfl|rfl <;> decide)
  have hs := side_x w (footCheck_s (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg) (footCheck_ram (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg) prg
  have := bgX_of_reads ram _ _ hs (hf 0x57 (by simp)) (hf 0x6D (by simp)) (hf 0x86 (by simp)) (hf 0x400 (by simp))
  have e : bgSide_ram w sp ram prg = sideRam w (footCheck_s (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg) prg
      (footCheck_ram (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg) := by
    funext i; simp only [bgSide_ram, bgY, bgRam]
  rw [e]
  exact this

theorem bgImpede_x (sp : UInt8) (ram prg : UInt16 → UInt8) : BgX ram (bgImpede_ram sp ram prg) := by
  have hk (i : UInt16) (hi : auxByte i = true) := bgRam_keeps ram i hi
  have := bgX_of_reads ram _ _ (foot_x (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg)
    (hk 0x57 (by decide)) (hk 0x6D (by decide)) (hk 0x86 (by decide)) (hk 0x400 (by decide))
  have e : bgImpede_ram sp ram prg = footCheck_ram (bgY ram) (bgSize_s (bgPre_s sp)) (bgRam ram) prg := by
    funext i; simp only [bgImpede_ram, bgY, bgRam]
  rw [e]
  exact this

theorem bgExit_x (ram : UInt16 → UInt8) : BgX ram (bgPre_ram ram) := by
  have hk (i : UInt16) (hi : auxByte i = true) := pre_keeps ram i hi
  simp only [BgX, pixelP, hk 0x400 (by decide), hk 0x57 (by decide), hk 0x6D (by decide), hk 0x86 (by decide)]
  simp

/-- `moveIn`, the RAM at `PlayerMovementSubs`, on the bytes movement and scrolling use from the entry state. -/
theorem moveIn_x (sp : UInt8) (ram : UInt16 → UInt8) (i : UInt16)
    (hi : i = 0x57 ∨ i = 0x6D ∨ i = 0x86 ∨ i = 0x400 ∨ i = 0x1D ∨ i = 0x704 ∨ i = 0x70B ∨ i = 0x70E ∨ carried i = true) :
    moveIn sp ram i = ram i := by
  have hp : ctrlPre_ram ram i = ram i := by
    apply ctrlPre_ram_frame
    simp only [carried] at hi
    simp only [ctrlPre_writes]
    bv_decide (config := { enums := false })
  simp only [moveIn, hp]
  simp only [carried] at hi
  bv_decide (config := { enums := false })

theorem moveX_transport (sp : UInt8) (ram M : UInt16 → UInt8) (h : MoveX (moveIn sp ram) M) : MoveX ram M := by
  have h6d := moveIn_x sp ram 0x6D (by simp)
  have h86 := moveIn_x sp ram 0x86 (by simp)
  have h400 := moveIn_x sp ram 0x400 (by simp)
  simp only [MoveX, pos24_pack, pixelP, h6d, h86, h400] at h ⊢
  exact h

/-! ### State 0 -/

theorem ctrlA0_out (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ScrollOut ram (ctrlA0_ram sp ram prg) := by
  have hm := ms0_x (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  have hk (i : UInt16) (hi : carried i = true) : ms0_ram (sp + 254) (moveIn sp ram) i = ram i := by
    rw [ms0_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hc := ctrl_stage (ctrlMid_s sp) ram prg _ hinv (moveX_transport sp ram _ hm) hk
  have hcomp : ctrlA0_ram sp ram prg =
      ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms0_ram (sp + 254) (moveIn sp ram))) prg := by
    unfold ctrlA0_ram moveIn
    simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]
  rw [hcomp]
  exact hc

/-- Ground/jump/fall frame through the side checks: speed limit and 2.5-pixel advance. -/
theorem frame0_side_limit (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hfoot : footCheck_pc (bgY (frameR0 sp ram prg)) (bgSize_s (bgPre_s (frameS0 sp))) (bgRam (frameR0 sp ram prg)) prg = 0xDD5E) :
    XStep ram (frame0_side_ram w sp ram prg) := by
  have hC := ctrlJ_out (ctrlA0_s sp) ram _ (ctrlA0_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1) :
      bgSide_ram w (frameS0 sp) (frameR0 sp ram prg) prg i = frameR0 sp ram prg i := by
    apply bgSide_ram_frame
    simp only [bgSide_writes, stackAt]
    bv_decide (config := { enums := false })
  unfold frame0_side_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgSide_x w _ _ prg htbl hfoot)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)))

/-- The same when a foot in a wall ends the collision code. -/
theorem frame0_impede_limit (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    XStep ram (frame0_impede_ram sp ram prg) := by
  have hC := ctrlJ_out (ctrlA0_s sp) ram _ (ctrlA0_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1) :
      bgImpede_ram (frameS0 sp) (frameR0 sp ram prg) prg i = frameR0 sp ram prg i := by
    apply bgImpede_ram_frame
    simp only [bgImpede_writes]
    bv_decide (config := { enums := false })
  unfold frame0_impede_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgImpede_x _ _ prg)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)))

/-- The same on the collision code's early exit. -/
theorem frame0_exit_limit (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    XStep ram (frame0_exit_ram sp ram prg) := by
  have hC := ctrlJ_out (ctrlA0_s sp) ram _ (ctrlA0_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : auxByte i = true) := pre_keeps (frameR0 sp ram prg) i hi
  unfold frame0_exit_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgExit_x _)
    (hk 0x71A (by decide)) (hk 0x71B (by decide)) (hk 0x71C (by decide)) (hk 0x71D (by decide)) (hk 0x3A1 (by decide)))

/-! ### State 1 -/

theorem ctrlA1_out (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ScrollOut ram (ctrlA1_ram sp ram prg) := by
  have hm := ms1_x (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  have hk (i : UInt16) (hi : carried i = true) : ms1_ram (sp + 254) (moveIn sp ram) i = ram i := by
    rw [ms1_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hc := ctrl_stage (ctrlMid_s sp) ram prg _ hinv (moveX_transport sp ram _ hm) hk
  have hcomp : ctrlA1_ram sp ram prg =
      ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms1_ram (sp + 254) (moveIn sp ram))) prg := by
    unfold ctrlA1_ram moveIn
    simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]
  rw [hcomp]
  exact hc

/-- Ground/jump/fall frame through the side checks: speed limit and 2.5-pixel advance. -/
theorem frame1_side_limit (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hfoot : footCheck_pc (bgY (frameR1 sp ram prg)) (bgSize_s (bgPre_s (frameS1 sp))) (bgRam (frameR1 sp ram prg)) prg = 0xDD5E) :
    XStep ram (frame1_side_ram w sp ram prg) := by
  have hC := ctrlJ_out (ctrlA1_s sp) ram _ (ctrlA1_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1) :
      bgSide_ram w (frameS1 sp) (frameR1 sp ram prg) prg i = frameR1 sp ram prg i := by
    apply bgSide_ram_frame
    simp only [bgSide_writes, stackAt]
    bv_decide (config := { enums := false })
  unfold frame1_side_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgSide_x w _ _ prg htbl hfoot)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)))

/-- The same when a foot in a wall ends the collision code. -/
theorem frame1_impede_limit (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    XStep ram (frame1_impede_ram sp ram prg) := by
  have hC := ctrlJ_out (ctrlA1_s sp) ram _ (ctrlA1_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1) :
      bgImpede_ram (frameS1 sp) (frameR1 sp ram prg) prg i = frameR1 sp ram prg i := by
    apply bgImpede_ram_frame
    simp only [bgImpede_writes]
    bv_decide (config := { enums := false })
  unfold frame1_impede_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgImpede_x _ _ prg)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)))

/-- The same on the collision code's early exit. -/
theorem frame1_exit_limit (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    XStep ram (frame1_exit_ram sp ram prg) := by
  have hC := ctrlJ_out (ctrlA1_s sp) ram _ (ctrlA1_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : auxByte i = true) := pre_keeps (frameR1 sp ram prg) i hi
  unfold frame1_exit_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgExit_x _)
    (hk 0x71A (by decide)) (hk 0x71B (by decide)) (hk 0x71C (by decide)) (hk 0x71D (by decide)) (hk 0x3A1 (by decide)))

/-! ### State 2 -/

theorem ctrlA2_out (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ScrollOut ram (ctrlA2_ram sp ram prg) := by
  have hm := ms2_x (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  have hk (i : UInt16) (hi : carried i = true) : ms2_ram (sp + 254) (moveIn sp ram) i = ram i := by
    rw [ms2_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hc := ctrl_stage (ctrlMid_s sp) ram prg _ hinv (moveX_transport sp ram _ hm) hk
  have hcomp : ctrlA2_ram sp ram prg =
      ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms2_ram (sp + 254) (moveIn sp ram))) prg := by
    unfold ctrlA2_ram moveIn
    simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]
  rw [hcomp]
  exact hc

/-- Ground/jump/fall frame through the side checks: speed limit and 2.5-pixel advance. -/
theorem frame2_side_limit (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hfoot : footCheck_pc (bgY (frameR2 sp ram prg)) (bgSize_s (bgPre_s (frameS2 sp))) (bgRam (frameR2 sp ram prg)) prg = 0xDD5E) :
    XStep ram (frame2_side_ram w sp ram prg) := by
  have hC := ctrlJ_out (ctrlA2_s sp) ram _ (ctrlA2_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1) :
      bgSide_ram w (frameS2 sp) (frameR2 sp ram prg) prg i = frameR2 sp ram prg i := by
    apply bgSide_ram_frame
    simp only [bgSide_writes, stackAt]
    bv_decide (config := { enums := false })
  unfold frame2_side_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgSide_x w _ _ prg htbl hfoot)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)))

/-- The same when a foot in a wall ends the collision code. -/
theorem frame2_impede_limit (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    XStep ram (frame2_impede_ram sp ram prg) := by
  have hC := ctrlJ_out (ctrlA2_s sp) ram _ (ctrlA2_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1) :
      bgImpede_ram (frameS2 sp) (frameR2 sp ram prg) prg i = frameR2 sp ram prg i := by
    apply bgImpede_ram_frame
    simp only [bgImpede_writes]
    bv_decide (config := { enums := false })
  unfold frame2_impede_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgImpede_x _ _ prg)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)))

/-- The same on the collision code's early exit. -/
theorem frame2_exit_limit (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    XStep ram (frame2_exit_ram sp ram prg) := by
  have hC := ctrlJ_out (ctrlA2_s sp) ram _ (ctrlA2_out sp ram prg hinv ht hs hz hjs)
  have hk (i : UInt16) (hi : auxByte i = true) := pre_keeps (frameR2 sp ram prg) i hi
  unfold frame2_exit_ram
  exact attr_step ram _ (finish_stage ram _ _ hC (bgExit_x _)
    (hk 0x71A (by decide)) (hk 0x71B (by decide)) (hk 0x71C (by decide)) (hk 0x71D (by decide)) (hk 0x3A1 (by decide)))

end Smb.Routine.HorizontalLimit
