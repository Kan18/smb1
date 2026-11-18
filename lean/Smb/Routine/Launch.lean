import Smb.Routine.HorizontalLimitNes
import Smb.LocalBound.HorizontalDistance

/-!
# How fast Mario can get up to speed

`HorizontalLimit` gives at most 2.5 pixels per update, which ignores that Mario starts from rest. Here: `ImposeFriction`'s step is at most `$1.C8`, so the 8.8 speed `upSpeed` (X speed and `Player_X_MoveForce`)
rises by at most `$1C8` per update. The doubled `$E4` is the largest step in the table, so it's the rate when turning at a run; on the TAS's launch the rate is lower.

`LStep` adds that to `XStep`'s conclusion, and bounds the update's advance by what the speed allows, or a pixel, whichever is more: a wall can eject Mario one pixel at any speed.
`launch_run` sums those over a run from rest. `launch_updates` gives its consequence: from rest, covering 224,256 sub-pixels takes at least 360 updates, not the 351 that 2.5 pixels per update gives.

Same paths and entry conditions as the frame theorems, plus `Far`: Mario is at least 8 pixels from the screen's left edge and not at its right one, so the screen-edge clamp doesn't act.
The clamp keeps the sub-pixel while resetting the pixel, which can move him forward even at negative speed.
-/
namespace Smb.Routine.Launch
open Smb.Routine.PlayerFramePosition Smb.Routine.HorizontalLimit Smb.Routine.HorizontalLimitNes

/-- The X speed and its fraction, as an 8.8 number, and 0 when moving left. -/
def upSpeed (ram : UInt16 → UInt8) : UInt16 :=
  bif ram 0x57 < 0x80 then (ram 0x57).toUInt16 <<< 8 ||| (ram 0x705).toUInt16 else 0

/-- The most an update can advance `phi`, from the speed it starts with. -/
def stepLim (u : UInt16) : UInt32 :=
  let v := ((u + 0x1C8) >>> 8).toUInt32 * 16
  bif v < 0x100 then 0x100 else bif v < 640 then v else 640

def Far (ram : UInt16 → UInt8) : Prop := 8 ≤ pixelP ram - leftL ram ∧ pixelP ram - leftL ram ≤ 0xE0

def LStep (ram out : UInt16 → UInt8) : Prop :=
  fwdLe (phi out) (phi ram) (stepLim (upSpeed ram)) = true ∧ upSpeed out ≤ upSpeed ram + 0x1C8

macro "ms_u_tac" msr:ident c0:ident : tactic => `(tactic| (
  simp only [upSpeed]
  (sym_exec [$msr:ident, $c0:ident, startsJump, physicsRam, jumpRam, xphysRam, frictionRam, mphRam, mpvRam,
    gravityRam, animRam, frictionSpeed, frictionDir, frictionRaw, frictionClamped, tbl3, xSpeedClass,
    xFrictionClass, xRunning, speedOk, mphPos, mphCarry, mphHi, mphLo, pos24, pos16, sext, sext16b, posIdx,
    pageIdx, forceIdx, speedIdx, yvel16, ypos24, sext16, nextPos, dummyIdx, yPosIdx, yHighIdx, yForceIdx,
    ySpeedIdx, jumpYSpeed, jumpClass, tbl7, frictionForce, bne] at *
   fun_congr
   bv_decide (config := { enums := false }))))

theorem ms0_u (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hv : speedOk (ram 0x57) = true) : upSpeed (ms0_ram sp ram) ≤ upSpeed ram + 0x1C8 := by
  ms_u_tac ms0_ram ms0_c0

theorem ms1_u (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hv : speedOk (ram 0x57) = true) : upSpeed (ms1_ram sp ram) ≤ upSpeed ram + 0x1C8 := by
  ms_u_tac ms1_ram ms1_c0

theorem ms2_u (sp : UInt8) (ram : UInt16 → UInt8)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hv : speedOk (ram 0x57) = true) : upSpeed (ms2_ram sp ram) ≤ upSpeed ram + 0x1C8 := by
  ms_u_tac ms2_ram ms2_c0

theorem moveIn_705 (sp : UInt8) (ram : UInt16 → UInt8) : moveIn sp ram 0x705 = ram 0x705 := by
  have hp : ctrlPre_ram ram 0x705 = ram 0x705 := by
    apply ctrlPre_ram_frame
    simp only [ctrlPre_writes]
    bv_decide (config := { enums := false })
  simp only [moveIn, hp]
  bv_decide (config := { enums := false })

theorem upSpeed_moveIn (sp : UInt8) (ram : UInt16 → UInt8) : upSpeed (moveIn sp ram) = upSpeed ram := by
  simp only [upSpeed, moveIn_705, moveIn_x sp ram 0x57 (by simp)]

theorem phi_far {ram : UInt16 → UInt8} (h : Far ram) : phi ram = pack (pixelP ram) (ram 0x400) := by
  obtain ⟨h1, h2⟩ := h
  have h3 : pixelP ram - leftL ram < 0x8000 := by
    generalize pixelP ram - leftL ram = d at *
    bv_decide (config := { enums := false })
  simp [phi, h3]

theorem stepLim_range (u : UInt16) : 0x100 ≤ stepLim u ∧ stepLim u ≤ 640 := by
  simp only [stepLim]
  bv_decide (config := { enums := false })

/-- What the speed gives: the new speed, in pixels, is within the limit. -/
theorem stepLim_speed (w : UInt16) (a b : UInt8) (hb : b ≤ 0x28)
    (h : (b.toUInt16 <<< 8 ||| a.toUInt16) ≤ w + 0x1C8) (hw : w ≤ 0x3000) : b.toUInt32 * 16 ≤ stepLim w := by
  simp only [stepLim]
  bv_decide (config := { enums := false })

theorem cond_zero_or (c : Bool) (a : UInt8) : (bif c then 0 else a) = a ∨ (bif c then 0 else a) = 0 := by
  cases c <;> simp

/-- `scroll_step`, with the advance bounded by the speed. -/
theorem scroll_stepL (sp : UInt8) (r : UInt16 → UInt8) (P0 : UInt16) (s0 : UInt8) (L : UInt32)
    (hv : speedOk (r 0x57) = true)
    (hpos : pack (pixelP r) (r 0x400) = (pack P0 s0 + sext (r 0x57) * 16) &&& 0xFFFFFF)
    (hpx : pixelP r = P0 + sext16b (r 0x6FF))
    (hplat : r 0x3A1 = 0)
    (hscr : 0x50 ≤ r 0x755 → r 0x785 = 0 → P0 - leftL r ≠ 0 ∧ P0 - leftL r < 0x8000)
    (hedge : edgeR r = leftL r + 255)
    (hfar : 8 ≤ P0 - leftL r ∧ P0 - leftL r ≤ 0xE0)
    (hL : 0x100 ≤ L ∧ L ≤ 640)
    (hLv : r 0x57 < 0x80 → (r 0x57).toUInt32 * 16 ≤ L) :
    let s := scrollRam sp r
    (s 0x57 = r 0x57 ∨ s 0x57 = 0) ∧
    fwdLe' (pack (pixelP s) (s 0x400)) (pack P0 s0) L = true ∧
    ((s 0x57 - 1) &&& 0x80 != 0 → fwdLe' (pack (pixelP s + 1) (s 0x400)) (pack P0 s0) L = true) := by
  have hc := scrollRam_clamp sp r (by
    simp only [screenEdgesConsistent, Bool.or_eq_true, beq_iff_eq]
    right
    simpa only [edgeR, leftL] using hedge)
  have h400 : scrollRam sp r 0x400 = r 0x400 := by
    apply scrollRam_frame; bv_decide (config := { enums := false })
  have hL' : scrollRam sp r 0x71C = scrLeftX r ∧ scrollRam sp r 0x71A = scrLeftPage r ∧
      scrollRam sp r 0x71D = scrRightX r ∧ scrollRam sp r 0x71B = scrRightPage r := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [scrollRam, gxoRam, scrMid, scrLeftX, scrLeftPage, scrRightX, scrRightPage, bne]
      fun_congr
      bv_decide (config := { enums := false })
  dsimp only at hc ⊢
  have h57 : scrollRam sp r 0x57 = r 0x57 ∨ scrollRam sp r 0x57 = 0 := by
    rw [hc.2]
    exact cond_zero_or _ _
  obtain ⟨hL1, hL2, hR1, hR2⟩ := hL'
  obtain ⟨hL3, hL4⟩ := hL
  obtain ⟨hf1, hf2⟩ := hfar
  simp only [edgeR, leftL, pixelP, h400, hL1, hL2, hR1, hR2] at hc hedge hf1 hf2 hpx hpos hscr ⊢
  generalize scrollRam sp r 0x6D = op at hc ⊢
  generalize scrollRam sp r 0x86 = ox at hc ⊢
  generalize scrollRam sp r 0x57 = ov at hc h57 ⊢
  clear hL1 hL2 hR1 hR2 h400
  refine ⟨h57, ?_⟩
  simp only [pack, fwdLe', speedOk, sext, sext16b, scrLeftX, scrLeftPage, scrRightX, scrRightPage, scrolls, scrAmt,
    scrPxs, pos16, hplat, bne] at *
  bv_decide (config := { enums := false })

/-- What the scroll stage adds to `ScrollOut`. -/
def ScrollL (ram C : UInt16 → UInt8) : Prop :=
  fwdLe' (pack (pixelP C) (C 0x400)) (phi ram) (stepLim (upSpeed ram)) = true ∧
  ((C 0x57 - 1) &&& 0x80 != 0 → fwdLe' (pack (pixelP C + 1) (C 0x400)) (phi ram) (stepLim (upSpeed ram)) = true) ∧
  upSpeed C ≤ upSpeed ram + 0x1C8

theorem ctrlAux_705 (sp : UInt8) (ram prg : UInt16 → UInt8) : ctrlAux_ram sp ram prg 0x705 = ram 0x705 := by
  have a := auxIn_at sp ram
  have h : ctrlAux_ram sp ram prg 0x705 = scrollRam sp (auxIn sp ram) 0x705 := by
    sym_exec [ctrlAux_ram, bbcRam, rppRam, gpoRam, gpoMid, gyoRam, absIdx, dummyIdx, forceIdx, pageIdx, posIdx,
      speedIdx, yForceIdx, yHighIdx, yPosIdx, ySpeedIdx, scrollRam, gxoRam, auxIn_eta, scrMid, a, bne]
  rw [h, scrollRam_frame _ _ _ (by bv_decide (config := { enums := false })), a _ (by decide)]

theorem upSpeed_le_of (f f' v v' : UInt8) (w : UInt16) (hw : w ≤ 0x3000) (hf : f' = f)
    (h : (bif v < 0x80 then v.toUInt16 <<< 8 ||| f.toUInt16 else 0) ≤ w + 0x1C8) (hv : v' = v ∨ v' = 0) :
    (bif v' < 0x80 then v'.toUInt16 <<< 8 ||| f'.toUInt16 else 0) ≤ w + 0x1C8 := by
  subst hf
  rcases hv with rfl | rfl
  · exact h
  · have e : (0 : UInt8).toUInt16 = 0 := rfl
    have e2 : ∀ x : UInt16, (0 : UInt16) <<< 8 ||| x = x := by intro x; bv_decide (config := { enums := false })
    simp only [cond, e, e2]
    have h255 : f'.toUInt16 ≤ 255 := by
      have := f'.toNat_lt
      rw [UInt16.le_iff_toNat_le, UInt8.toNat_toUInt16]
      show _ ≤ 255
      omega
    generalize f'.toUInt16 = x at *
    clear h
    revert h255 hw
    bv_decide (config := { enums := false })

/-- Movement in `M` from the state `ram`, then `ctrlMid` and `ScrollHandler`. -/
theorem ctrl_stageL (sp : UInt8) (ram prg M : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (hm : MoveX ram M) (hk : ∀ i, carried i = true → M i = ram i) (hu : upSpeed M ≤ upSpeed ram + 0x1C8) :
    ScrollL ram (ctrlAux_ram sp (ctrlMid_ram M) prg) := by
  have hmid (i : UInt16) (hi : (i != 1177 && i != 69) = true) : ctrlMid_ram M i = M i := by
    apply ctrlMid_ram_frame; simp only [ctrlMid_writes]; simp only [bne] at hi; bv_decide (config := { enums := false })
  obtain ⟨hv0, he0, hp0, hd0, hs0⟩ := hinv
  have hmx := hm
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
  have r705 := hr 0x705 (by decide)
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
  have hUram : upSpeed ram ≤ 0x3000 := by
    simp only [upSpeed, speedOk] at hv0 ⊢
    bv_decide (config := { enums := false })
  have hLv : r 0x57 < 0x80 → (r 0x57).toUInt32 * 16 ≤ stepLim (upSpeed ram) := by
    intro hb
    rw [r57] at hb ⊢
    have hb' : (M 0x57).toUInt16 <<< 8 ||| (M 0x705).toUInt16 ≤ upSpeed ram + 0x1C8 := by
      have := hu
      simp only [upSpeed, hb, decide_true, cond_true] at this
      exact this
    have hb2 : M 0x57 ≤ 0x28 := by
      simp only [speedOk] at hv
      bv_decide (config := { enums := false })
    exact stepLim_speed _ _ _ hb2 hb' hUram
  have hstep := scroll_stepL sp r (pixelP ram) (ram 0x400) (stepLim (upSpeed ram))
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
    (by rw [hL]; exact hfar)
    (stepLim_range _)
    hLv
  have hC (i : UInt16) (hi : auxByte i = true) :
      ctrlAux_ram sp (ctrlMid_ram M) prg i = scrollRam sp r i := HorizontalLimit.ctrlAux_x sp _ prg i hi
  have hc705 : ctrlAux_ram sp (ctrlMid_ram M) prg 0x705 = M 0x705 := by
    rw [ctrlAux_705]; exact hmid 0x705 (by decide)
  obtain ⟨h1, h2, h3⟩ := hstep
  simp only [ScrollL, phi_far hfar, pixelP, hC 0x57 (by decide), hC 0x6D (by decide), hC 0x86 (by decide), hC 0x400 (by decide)]
  refine ⟨h2, h3, ?_⟩
  simp only [upSpeed] at hu ⊢
  exact upSpeed_le_of _ _ _ _ _ hUram hc705 hu (by rw [hC 0x57 (by decide)]; rw [r57] at h1; exact h1)

/-- Scroll output and one collision step give the update's advance. -/
theorem finish_stageL (ram C b : UInt16 → UInt8) (hO : ScrollOut ram C) (hC : ScrollL ram C) (hUram : upSpeed ram ≤ 0x3000) (hb : BgX C b)
    (h71a : b 0x71A = C 0x71A) (h71b : b 0x71B = C 0x71B) (h71c : b 0x71C = C 0x71C) (h71d : b 0x71D = C 0x71D)
    (h3a1 : b 0x3A1 = C 0x3A1) (h705 : b 0x705 = C 0x705) : LStep ram b := by
  obtain ⟨hv, hp, he, hd, _, _⟩ := hO
  obtain ⟨h1, h2, h3⟩ := hC
  obtain ⟨hL0, hL1⟩ := stepLim_range (upSpeed ram)
  have hbx := hb
  obtain ⟨h400, hb⟩ := hb
  refine ⟨?_, ?_⟩
  · have hphi : phi b = bif pixelP b - leftL b < 0x8000 then pack (pixelP b) (b 0x400) else pack (leftL b) 0 := rfl
    rw [hphi]
    clear hphi
    generalize stepLim (upSpeed ram) = L at *
    generalize phi ram = base at *
    simp only [leftL, edgeR, h71a, h71b, h71c, h71d, h3a1, h400] at he hd h2 ⊢
    generalize pixelP C = Pc at *
    generalize pixelP b = Pb at *
    simp only [pack, fwdLe, fwdLe', speedOk, pos16, bne] at *
    bv_decide (config := { enums := false })
  · have h57 : b 0x57 = C 0x57 ∨ b 0x57 = 0 := by
      rcases hb with ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h
    simp only [upSpeed] at h3 hUram ⊢
    exact upSpeed_le_of _ _ _ _ _ (by simpa only [upSpeed] using hUram) h705 h3 h57

theorem ctrlJ_outL (s : UInt8) (ram C : UInt16 → UInt8) (h : ScrollL ram C) : ScrollL ram (ctrlJ_ram s C) := by
  have hk (i : UInt16) (hi : auxByte i = true ∨ i = 0x705) : ctrlJ_ram s C i = C i := by
    simp only [auxByte] at hi
    sym_exec [ctrlJ_ram]
    bv_decide (config := { enums := false })
  simp only [ScrollL, upSpeed, pixelP, hk 0x57 (by simp [auxByte]), hk 0x6D (by simp [auxByte]), hk 0x86 (by simp [auxByte]), hk 0x400 (by simp [auxByte]), hk 0x705 (by simp)]
  simpa only [ScrollL, upSpeed, pixelP] using h

theorem attr_stepL (ram b : UInt16 → UInt8) (h : LStep ram b) : LStep ram (ctrlAttr_ram b) := by
  have hk (i : UInt16) (hi : auxByte i = true ∨ i = 0x705) : ctrlAttr_ram b i = b i := by
    simp only [auxByte] at hi
    sym_exec [ctrlAttr_ram]
    bv_decide (config := { enums := false })
  simp only [LStep, phi, pixelP, leftL, upSpeed] at h
  simp only [LStep, phi, pixelP, leftL, upSpeed, hk 0x57 (by simp [auxByte]), hk 0x71A (by simp [auxByte]), hk 0x71C (by simp [auxByte]),
    hk 0x6D (by simp [auxByte]), hk 0x86 (by simp [auxByte]), hk 0x400 (by simp [auxByte]), hk 0x705 (by simp)]
  exact h

theorem upSpeed_bound {ram : UInt16 → UInt8} (hinv : XInv ram) : upSpeed ram ≤ 0x3000 := by
  have hv := hinv.1
  simp only [upSpeed, speedOk] at hv ⊢
  bv_decide (config := { enums := false })

theorem bgPre_705 (ram : UInt16 → UInt8) : bgPre_ram ram 0x705 = ram 0x705 := by
  apply bgPre_ram_frame
  simp only [bgPre_writes]
  bv_decide (config := { enums := false })

theorem ctrlA0_outL (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ScrollL ram (ctrlA0_ram sp ram prg) := by
  have hm := HorizontalLimit.ms0_x (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  have hu := ms0_u (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  rw [upSpeed_moveIn] at hu
  have hk (i : UInt16) (hi : carried i = true) : ms0_ram (sp + 254) (moveIn sp ram) i = ram i := by
    rw [HorizontalLimit.ms0_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hc := ctrl_stageL (ctrlMid_s sp) ram prg _ hinv hfar (moveX_transport sp ram _ hm) hk hu
  have hcomp : ctrlA0_ram sp ram prg =
      ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms0_ram (sp + 254) (moveIn sp ram))) prg := by
    unfold ctrlA0_ram moveIn
    simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]
  rw [hcomp]
  exact hc

theorem frame0_side_launch (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hfoot : footCheck_pc (bgY (frameR0 sp ram prg)) (bgSize_s (bgPre_s (frameS0 sp))) (bgRam (frameR0 sp ram prg)) prg = 0xDD5E) :
    LStep ram (frame0_side_ram w sp ram prg) := by
  have hO := ctrlJ_out (ctrlA0_s sp) ram _ (ctrlA0_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA0_s sp) ram _ (ctrlA0_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1 ∨ i = 0x705) :
      bgSide_ram w (frameS0 sp) (frameR0 sp ram prg) prg i = frameR0 sp ram prg i := by
    apply bgSide_ram_frame
    simp only [bgSide_writes, stackAt]
    bv_decide (config := { enums := false })
  unfold frame0_side_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgSide_x w _ _ prg htbl hfoot)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)) (hk 0x705 (by simp)))

theorem frame0_impede_launch (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    LStep ram (frame0_impede_ram sp ram prg) := by
  have hO := ctrlJ_out (ctrlA0_s sp) ram _ (ctrlA0_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA0_s sp) ram _ (ctrlA0_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1 ∨ i = 0x705) :
      bgImpede_ram (frameS0 sp) (frameR0 sp ram prg) prg i = frameR0 sp ram prg i := by
    apply bgImpede_ram_frame
    simp only [bgImpede_writes]
    bv_decide (config := { enums := false })
  unfold frame0_impede_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgImpede_x _ _ prg)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)) (hk 0x705 (by simp)))

theorem frame0_exit_launch (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    LStep ram (frame0_exit_ram sp ram prg) := by
  have hO := ctrlJ_out (ctrlA0_s sp) ram _ (ctrlA0_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA0_s sp) ram _ (ctrlA0_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : auxByte i = true) := pre_keeps (frameR0 sp ram prg) i hi
  unfold frame0_exit_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgExit_x _)
    (hk 0x71A (by decide)) (hk 0x71B (by decide)) (hk 0x71C (by decide)) (hk 0x71D (by decide)) (hk 0x3A1 (by decide)) (bgPre_705 _))

theorem ctrlA1_outL (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ScrollL ram (ctrlA1_ram sp ram prg) := by
  have hm := HorizontalLimit.ms1_x (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  have hu := ms1_u (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  rw [upSpeed_moveIn] at hu
  have hk (i : UInt16) (hi : carried i = true) : ms1_ram (sp + 254) (moveIn sp ram) i = ram i := by
    rw [HorizontalLimit.ms1_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hc := ctrl_stageL (ctrlMid_s sp) ram prg _ hinv hfar (moveX_transport sp ram _ hm) hk hu
  have hcomp : ctrlA1_ram sp ram prg =
      ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms1_ram (sp + 254) (moveIn sp ram))) prg := by
    unfold ctrlA1_ram moveIn
    simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]
  rw [hcomp]
  exact hc

theorem frame1_side_launch (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hfoot : footCheck_pc (bgY (frameR1 sp ram prg)) (bgSize_s (bgPre_s (frameS1 sp))) (bgRam (frameR1 sp ram prg)) prg = 0xDD5E) :
    LStep ram (frame1_side_ram w sp ram prg) := by
  have hO := ctrlJ_out (ctrlA1_s sp) ram _ (ctrlA1_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA1_s sp) ram _ (ctrlA1_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1 ∨ i = 0x705) :
      bgSide_ram w (frameS1 sp) (frameR1 sp ram prg) prg i = frameR1 sp ram prg i := by
    apply bgSide_ram_frame
    simp only [bgSide_writes, stackAt]
    bv_decide (config := { enums := false })
  unfold frame1_side_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgSide_x w _ _ prg htbl hfoot)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)) (hk 0x705 (by simp)))

theorem frame1_impede_launch (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    LStep ram (frame1_impede_ram sp ram prg) := by
  have hO := ctrlJ_out (ctrlA1_s sp) ram _ (ctrlA1_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA1_s sp) ram _ (ctrlA1_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1 ∨ i = 0x705) :
      bgImpede_ram (frameS1 sp) (frameR1 sp ram prg) prg i = frameR1 sp ram prg i := by
    apply bgImpede_ram_frame
    simp only [bgImpede_writes]
    bv_decide (config := { enums := false })
  unfold frame1_impede_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgImpede_x _ _ prg)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)) (hk 0x705 (by simp)))

theorem frame1_exit_launch (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    LStep ram (frame1_exit_ram sp ram prg) := by
  have hO := ctrlJ_out (ctrlA1_s sp) ram _ (ctrlA1_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA1_s sp) ram _ (ctrlA1_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : auxByte i = true) := pre_keeps (frameR1 sp ram prg) i hi
  unfold frame1_exit_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgExit_x _)
    (hk 0x71A (by decide)) (hk 0x71B (by decide)) (hk 0x71C (by decide)) (hk 0x71D (by decide)) (hk 0x3A1 (by decide)) (bgPre_705 _))

theorem ctrlA2_outL (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    ScrollL ram (ctrlA2_ram sp ram prg) := by
  have hm := HorizontalLimit.ms2_x (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  have hu := ms2_u (sp + 254) (moveIn sp ram)
    (by rw [moveIn_x sp ram 0x1D (by simp)]; exact ht) (by rw [moveIn_x sp ram 0x704 (by simp)]; exact hs)
    (by rw [moveIn_x sp ram 0x70B (by simp)]; exact hz) (by rw [moveIn_x sp ram 0x70E (by simp)]; exact hjs)
    (by rw [moveIn_x sp ram 0x57 (by simp)]; exact hinv.1)
  rw [upSpeed_moveIn] at hu
  have hk (i : UInt16) (hi : carried i = true) : ms2_ram (sp + 254) (moveIn sp ram) i = ram i := by
    rw [HorizontalLimit.ms2_keeps _ _ i hi]
    exact moveIn_x sp ram i (by simp [hi])
  have hc := ctrl_stageL (ctrlMid_s sp) ram prg _ hinv hfar (moveX_transport sp ram _ hm) hk hu
  have hcomp : ctrlA2_ram sp ram prg =
      ctrlAux_ram (ctrlMid_s sp) (ctrlMid_ram (ms2_ram (sp + 254) (moveIn sp ram))) prg := by
    unfold ctrlA2_ram moveIn
    simp only [ctrlPre_ram_read, ctrlPre_writes, Bool.or_false]
  rw [hcomp]
  exact hc

theorem frame2_side_launch (w : UInt16 → UInt8) (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (htbl : prg 0x5F96 = 0x24 ∧ prg 0x5F97 = 0x6D ∧ prg 0x5F98 = 0x8A ∧ prg 0x5F99 = 0xC6)
    (hfoot : footCheck_pc (bgY (frameR2 sp ram prg)) (bgSize_s (bgPre_s (frameS2 sp))) (bgRam (frameR2 sp ram prg)) prg = 0xDD5E) :
    LStep ram (frame2_side_ram w sp ram prg) := by
  have hO := ctrlJ_out (ctrlA2_s sp) ram _ (ctrlA2_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA2_s sp) ram _ (ctrlA2_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1 ∨ i = 0x705) :
      bgSide_ram w (frameS2 sp) (frameR2 sp ram prg) prg i = frameR2 sp ram prg i := by
    apply bgSide_ram_frame
    simp only [bgSide_writes, stackAt]
    bv_decide (config := { enums := false })
  unfold frame2_side_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgSide_x w _ _ prg htbl hfoot)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)) (hk 0x705 (by simp)))

theorem frame2_impede_launch (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    LStep ram (frame2_impede_ram sp ram prg) := by
  have hO := ctrlJ_out (ctrlA2_s sp) ram _ (ctrlA2_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA2_s sp) ram _ (ctrlA2_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1 ∨ i = 0x705) :
      bgImpede_ram (frameS2 sp) (frameR2 sp ram prg) prg i = frameR2 sp ram prg i := by
    apply bgImpede_ram_frame
    simp only [bgImpede_writes]
    bv_decide (config := { enums := false })
  unfold frame2_impede_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgImpede_x _ _ prg)
    (hk 0x71A (by simp)) (hk 0x71B (by simp)) (hk 0x71C (by simp)) (hk 0x71D (by simp)) (hk 0x3A1 (by simp)) (hk 0x705 (by simp)))

theorem frame2_exit_launch (sp : UInt8) (ram prg : UInt16 → UInt8) (hinv : XInv ram) (hfar : Far ram)
    (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0) :
    LStep ram (frame2_exit_ram sp ram prg) := by
  have hO := ctrlJ_out (ctrlA2_s sp) ram _ (ctrlA2_out sp ram prg hinv ht hs hz hjs)
  have hC := ctrlJ_outL (ctrlA2_s sp) ram _ (ctrlA2_outL sp ram prg hinv hfar ht hs hz hjs)
  have hk (i : UInt16) (hi : auxByte i = true) := pre_keeps (frameR2 sp ram prg) i hi
  unfold frame2_exit_ram
  exact attr_stepL ram _ (finish_stageL ram _ _ hO hC (upSpeed_bound hinv) (HorizontalLimit.bgExit_x _)
    (hk 0x71A (by decide)) (hk 0x71B (by decide)) (hk 0x71C (by decide)) (hk 0x71D (by decide)) (hk 0x3A1 (by decide)) (bgPre_705 _))

/-! ## On the full NES -/

theorem lstep_of_rel {r : UInt16 → UInt8} {s : NES} {t : Plain} (h : Rel s t) (hx : LStep r t.ram) : LStep r (ramAt s) := by
  have e (i : UInt16) (hi : i < 0x800) : ramAt s i = t.ram i := by rw [ramAt_of_rel h, and7ff_of_lt i hi]
  simp only [LStep, phi, pixelP, leftL, upSpeed] at hx
  simp only [LStep, phi, pixelP, leftL, upSpeed, e 0x57 (by decide), e 0x6D (by decide), e 0x86 (by decide), e 0x400 (by decide),
    e 0x71A (by decide), e 0x71C (by decide), e 0x705 (by decide)]
  exact hx

set_option maxRecDepth 20000 in
theorem frame0_side_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 0)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR0 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS0 s.s))) (bgRam (frameR0 s.s (ramAt s) romFn)) romFn = 0xDD5E)
    (hx_eb : bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn) 0xEB < 0x16)
    (hx_coin : noSideCoin romFn (bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn)) = true)
    (hx_climb : noSideClimb romFn (bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn)) = true)
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS0 s.s) romFn (frameR0 s.s (ramAt s) romFn)) = true)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame0_side_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  exact lstep_of_rel hr (frame0_side_launch w s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs rom_climbTable hx_foot)

set_option maxRecDepth 20000 in
theorem frame0_impede_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 0)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR0 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS0 s.s))) (bgRam (frameR0 s.s (ramAt s) romFn)) romFn = 0xDF8A)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame0_impede_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  exact lstep_of_rel hr (frame0_impede_launch s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame0_exit_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 0)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR0 s.s (ramAt s) romFn) = 0xDC97)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame0_exit_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go
  exact lstep_of_rel hr (frame0_exit_launch s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame1_side_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 1)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR1 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS1 s.s))) (bgRam (frameR1 s.s (ramAt s) romFn)) romFn = 0xDD5E)
    (hx_eb : bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn) 0xEB < 0x16)
    (hx_coin : noSideCoin romFn (bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn)) = true)
    (hx_climb : noSideClimb romFn (bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn)) = true)
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS1 s.s) romFn (frameR1 s.s (ramAt s) romFn)) = true)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame1_side_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  exact lstep_of_rel hr (frame1_side_launch w s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs rom_climbTable hx_foot)

set_option maxRecDepth 20000 in
theorem frame1_impede_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 1)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR1 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS1 s.s))) (bgRam (frameR1 s.s (ramAt s) romFn)) romFn = 0xDF8A)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame1_impede_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  exact lstep_of_rel hr (frame1_impede_launch s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame1_exit_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 1)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR1 s.s (ramAt s) romFn) = 0xDC97)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame1_exit_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go
  exact lstep_of_rel hr (frame1_exit_launch s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame2_side_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 2)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR2 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS2 s.s))) (bgRam (frameR2 s.s (ramAt s) romFn)) romFn = 0xDD5E)
    (hx_eb : bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn) 0xEB < 0x16)
    (hx_coin : noSideCoin romFn (bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn)) = true)
    (hx_climb : noSideClimb romFn (bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn)) = true)
    (hx_pipe : noSidePipeEntry romFn (bgFootRam (frameS2 s.s) romFn (frameR2 s.s (ramAt s) romFn)) = true)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', a', x', y', c', w, hr, _⟩ := Smb.Routine.frame2_side_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot hx_eb hx_coin hx_climb hx_pipe
  exact lstep_of_rel hr (frame2_side_launch w s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs rom_climbTable hx_foot)

set_option maxRecDepth 20000 in
theorem frame2_impede_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 2)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 s.s (ramAt s) romFn) = 0xDC98)
    (hx_hc : headCoin romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_hh : headHit romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_fc : footCoin romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_fa : footAxeAt romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_pe : pipeEntryAt romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) = false)
    (hx_foot : footCheck_pc (bgY (frameR2 s.s (ramAt s) romFn)) (bgSize_s (bgPre_s (frameS2 s.s))) (bgRam (frameR2 s.s (ramAt s) romFn)) romFn = 0xDF8A)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame2_impede_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go hx_hc hx_hh hx_fc hx_fa hx_pe hx_foot
  exact lstep_of_rel hr (frame2_impede_launch s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs)

set_option maxRecDepth 20000 in
theorem frame2_exit_launch_nes (s : NES) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (m : Nat)
    (hI : (s.p &&& 4 == 0) = false)
    (hst : (ramAt s) 0x1D = 2)
    (hsize : (ramAt s) 0x70B = 0)
    (hswim : (ramAt s) 0x704 = 0)
    (hjs : (ramAt s) 0x70E = 0)
    (hspd : (ramAt s) 0x9F + 0x40 < 0x80)
    (hx_go : bgPre_pc (frameR2 s.s (ramAt s) romFn) = 0xDC97)
    (hinv : XInv (ramAt s)) (hfar : Far (ramAt s)) :
    LStep (ramAt s) (ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2) := by
  obtain ⟨p', c', hr, _⟩ := Smb.Routine.frame2_exit_nes s hq hprg hpc m hI hst hsize hswim hjs hspd hx_go
  exact lstep_of_rel hr (frame2_exit_launch s.s (ramAt s) romFn hinv hfar hst hswim hsize hjs)

/-! ## A run from rest -/

/-- `stepLim` as a number, after `k` updates from a speed below 1. -/
def limN (k : Nat) : Nat :=
  let v := (255 + 456 * (k + 1)) / 256 * 16
  if v < 256 then 256 else if v < 640 then v else 640

/-- The most `n` updates from rest can advance `phi`. -/
def gain : Nat → Nat
  | 0 => 0
  | n + 1 => gain n + limN n

theorem gain_mono {m n : Nat} (h : m ≤ n) : gain m ≤ gain n := by
  induction n with
  | zero => cases h; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := ih (by omega)
      simp only [gain]
      omega
    · rw [h]
      exact Nat.le_refl _

theorem stepLim_mono {a b : UInt16} (h : a ≤ b) (hb : b ≤ 0x3000) : stepLim a ≤ stepLim b := by
  simp only [stepLim]
  bv_decide (config := { enums := false })

theorem stepLim_table : ∀ k : Fin 23, (stepLim (UInt16.ofNat (255 + 456 * k.val))).toNat ≤ limN k.val := by decide +kernel

theorem stepLim_le (k : Nat) (hk : k < 23) (u : UInt16) (hu : u.toNat ≤ 255 + 456 * k) : (stepLim u).toNat ≤ limN k := by
  have h1 : u ≤ UInt16.ofNat (255 + 456 * k) := by
    rw [UInt16.le_iff_toNat_le, UInt16.toNat_ofNat']
    have : (255 + 456 * k) % 2 ^ 16 = 255 + 456 * k := Nat.mod_eq_of_lt (by omega)
    omega
  have h2 : UInt16.ofNat (255 + 456 * k) ≤ 0x3000 := by
    rw [UInt16.le_iff_toNat_le, UInt16.toNat_ofNat']
    have : (255 + 456 * k) % 2 ^ 16 = 255 + 456 * k := Nat.mod_eq_of_lt (by omega)
    rw [this]; show _ ≤ 0x3000; omega
  have h3 := stepLim_mono h1 h2
  have h4 := stepLim_table ⟨k, hk⟩
  have h5 : (stepLim u).toNat ≤ (stepLim (UInt16.ofNat (255 + 456 * k))).toNat := h3
  exact Nat.le_trans h5 h4

/-- In the non-wrapping window, `fwdLe` is a bound on the numbers. -/
theorem fwdLe_nat (old new L : UInt32) (ho : old.toNat < 0x800000) (hn : new.toNat < 0x800000) (hL : L ≤ 640)
    (h : fwdLe new old L = true) : new.toNat ≤ old.toNat + L.toNat := by
  have ho' : old < 0x800000 := ho
  have hn' : new < 0x800000 := hn
  have hb : new ≤ old + L := by
    unfold fwdLe at h
    bv_decide (config := { enums := false })
  have hL' : L.toNat ≤ 640 := hL
  change new.toNat ≤ (old + L).toNat at hb
  rw [UInt32.toNat_add] at hb
  have : (old.toNat + L.toNat) % 2 ^ 32 = old.toNat + L.toNat := Nat.mod_eq_of_lt (by omega)
  omega

/-- From rest, `n` updates advance `phi` by at most `gain n`. `LStep` is needed only for the first 23: after that the speed limit gives the same. -/
theorem launch_run (entry out : Nat → UInt16 → UInt8) (n : Nat)
    (hw : ∀ k, k ≤ n → Smb.LocalBound.HorizontalDistance.InWindow (entry k))
    (ho : ∀ k, k < n → Smb.LocalBound.HorizontalDistance.InWindow (out k))
    (hs : ∀ k, k < n → XStep (entry k) (out k))
    (hl : ∀ k, k < n → k < 23 → LStep (entry k) (out k))
    (hr : ∀ k, k < n → (phi (entry (k + 1))).toNat ≤ (phi (out k)).toNat)
    (hu : ∀ k, k < n → upSpeed (entry (k + 1)) ≤ upSpeed (out k))
    (h0 : (upSpeed (entry 0)).toNat ≤ 255) :
    (phi (entry n)).toNat ≤ (phi (entry 0)).toNat + gain n := by
  have hU : ∀ k, k ≤ n → k ≤ 23 → (upSpeed (entry k)).toNat ≤ 255 + 456 * k := by
    intro k
    induction k with
    | zero => intro _ _; simpa using h0
    | succ k ih =>
      intro h1 h2
      have h3 := ih (by omega) (by omega)
      have h4 := (hl k (by omega) (by omega)).2
      have h5 := hu k (by omega)
      have h6 : (upSpeed (entry (k + 1))).toNat ≤ (upSpeed (out k)).toNat := h5
      have h7 : (upSpeed (out k)).toNat ≤ (upSpeed (entry k) + 0x1C8).toNat := h4
      have h8 : (upSpeed (entry k) + 0x1C8).toNat = (upSpeed (entry k)).toNat + 456 := by
        rw [UInt16.toNat_add]
        exact Nat.mod_eq_of_lt (by show _ + 456 < _; omega)
      omega
  induction n with
  | zero => simp [gain]
  | succ n ih =>
    have prev := ih (fun k hk => hw k (by omega)) (fun k hk => ho k (by omega)) (fun k hk => hs k (by omega))
      (fun k hk => hl k (by omega)) (fun k hk => hr k (by omega)) (fun k hk => hu k (by omega))
      (fun k h1 h2 => hU k (by omega) h2)
    have rest := hr n (by omega)
    have step : (phi (out n)).toNat ≤ (phi (entry n)).toNat + limN n := by
      by_cases h23 : n < 23
      · have h1 := (hl n (by omega) h23).1
        have h2 := fwdLe_nat _ _ _ (hw n (by omega)) (ho n (by omega)) (stepLim_range _).2 h1
        have h3 := stepLim_le n h23 _ (hU n (by omega) (by omega))
        omega
      · have h1 := Smb.LocalBound.HorizontalDistance.update_bound (hw n (by omega)) (ho n (by omega)) (hs n (by omega))
        have h2 : limN n = 640 := by
          simp only [limN]
          have : 40 ≤ (255 + 456 * (n + 1)) / 256 := by omega
          rw [if_neg (by omega), if_neg (by omega)]
        omega
    simp only [gain]
    omega

/-- Covering more than `gain m` takes more than `m` updates. -/
theorem launch_updates (entry out : Nat → UInt16 → UInt8) (n m D : Nat)
    (hw : ∀ k, k ≤ n → Smb.LocalBound.HorizontalDistance.InWindow (entry k))
    (ho : ∀ k, k < n → Smb.LocalBound.HorizontalDistance.InWindow (out k))
    (hs : ∀ k, k < n → XStep (entry k) (out k))
    (hl : ∀ k, k < n → k < 23 → LStep (entry k) (out k))
    (hr : ∀ k, k < n → (phi (entry (k + 1))).toNat ≤ (phi (out k)).toNat)
    (hu : ∀ k, k < n → upSpeed (entry (k + 1)) ≤ upSpeed (out k))
    (h0 : (upSpeed (entry 0)).toNat ≤ 255)
    (hd : (phi (entry 0)).toNat + D ≤ (phi (entry n)).toNat) (hm : gain m < D) : m + 1 ≤ n := by
  have h1 := launch_run entry out n hw ho hs hl hr hu h0
  rcases Nat.lt_or_ge m n with h2 | h2
  · exact h2
  · have h3 := gain_mono h2
    omega

/-- To the pipe, the bonus room's side pipe and the flag, from rest. -/
theorem gain_pipe : gain 359 < 224256 := by decide +kernel
theorem gain_bonus : gain 78 < 44224 := by decide +kernel
theorem gain_flag : gain 225 < 138752 := by decide +kernel

end Smb.Routine.Launch
