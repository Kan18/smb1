import Smb.Goal.LaunchSensors
import Smb.Routine.FrameRun

/-!
# A launch frame follows the model

`Smb.Routine.LaunchPhase.frame_run` gives the regions over a whole frame, given what the routine does. This file supplies that from `ModelFrame`, using the bounds, the vertical closure and Mario's position, and turns the result into `Follows`.
-/
namespace Smb.Goal.OneOne

open Smb.Abs Smb.Abs.LaunchPhase
open Smb.Routine
open Smb.Routine.HorizontalLimit (pixelP leftL edgeR)
open Smb.Routine.ModelFrame
open Smb.Routine.ModelBridge (cellsOf inOfRam modelMove)
open Smb.Routine.PlayerFramePosition (moveIn)
open Smb.Routine.LaunchExit
open Smb.Routine.LaunchPhase (forall_u8 forall_u16 RoutineRun)
open Smb.Routine.LaunchVert (VFacts)

/-- The regions' invariant, at a frame's start. -/
abbrev Smb.Abs.FInvAt (s : NES) : Prop := Smb.Routine.FrameGuard.FInv (Smb.Abs.romOf Smb.prg) G Smb.Routine.LaunchPhase.rsP (Smb.Routine.LaunchPhase.reg Z) s

/-! ## The bounds, as facts -/

theorem g_consts : onlyAll 0x0E 8 = true ∧ onlyAll 0x74E 1 = true ∧ onlyAll 0x704 0 = true ∧ onlyAll 0x70B 0 = true ∧ onlyAll 0x70E 0 = true ∧ onlyAll 0x490 0xFF = true ∧
    onlyAll 0x754 1 = true ∧ onlyAll 0xB5 1 = true ∧ onlyAll 0x716 0 = true ∧ onlyAll 0x71A 0 = true ∧ onlyAll 0x71B 0 = true ∧ onlyAll 0x71C 0 = true ∧ onlyAll 0x71D 0xFF = true ∧
    onlyAll 0x3A1 0 = true ∧ onlyAll 0x6D 0 = true := by native_decide

def lessAt (a : UInt16) (x : UInt8) : Bool := !((gAt G a).mem x) || decide (x < 0x50)

def lessAll (a : UInt16) : Bool := (List.range 256).all fun n => lessAt a (UInt8.ofNat n)

theorem g_less : lessAll 0x86 = true ∧ lessAll 0x755 = true := by native_decide

theorem less_sound {a : UInt16} {x : UInt8} (h : lessAll a = true) (hm : (gAt G a).mem x = true) : x < 0x50 := by
  have h2 := forall_u8 (lessAt a) h x
  simpa [lessAt, hm] using h2

/-- What the launch's bounds say of the routine's entry. -/
structure LCells (ram : UInt16 → UInt8) : Prop where
  eng : ram 0x0E = 8
  area : ram 0x74E = 1
  swim : ram 0x704 = 0
  z : ram 0x70B = 0
  js : ram 0x70E = 0
  coll : ram 0x490 = 0xFF
  small : ram 0x754 = 1
  high : ram 0xB5 = 1
  noExit : ram 0x716 = 0
  l1 : ram 0x71A = 0
  r1 : ram 0x71B = 0
  l2 : ram 0x71C = 0
  r2 : ram 0x71D = 0xFF
  plat : ram 0x3A1 = 0
  page : ram 0x6D = 0
  x : ram 0x86 < 0x50
  scroll : ram 0x755 < 0x50
  buf : ∀ a, inBuf a = true → ram a = bufTile a

theorem lcells {ram : UInt16 → UInt8} (hG : ∀ i, (gAt G i).mem (ram i) = true) : LCells ram := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := g_consts
  exact ⟨only_sound h1 (hG _), only_sound h2 (hG _), only_sound h3 (hG _), only_sound h4 (hG _), only_sound h5 (hG _), only_sound h6 (hG _), only_sound h7 (hG _), only_sound h8 (hG _),
    only_sound h9 (hG _), only_sound h10 (hG _), only_sound h11 (hG _), only_sound h12 (hG _), only_sound h13 (hG _), only_sound h14 (hG _), only_sound h15 (hG _),
    less_sound g_less.1 (hG _), less_sound g_less.2 (hG _), buf_of_glob hG⟩

theorem away_of {ram : UInt16 → UInt8} (h : LCells ram) (hlo : 12 ≤ ram 0x86) : Away ram := by
  have hx := h.x
  refine ⟨?_, h.plat, ?_, ?_⟩
  · simp only [edgeR, leftL, Smb.Routine.pos16, h.l1, h.l2, h.r1, h.r2]; decide
  · simp only [pixelP, leftL, Smb.Routine.pos16, h.l1, h.l2, h.page]
    generalize ram 0x86 = X at *
    bv_decide (config := { enums := false })
  · simp only [pixelP, leftL, Smb.Routine.pos16, h.l1, h.l2, h.page]
    generalize ram 0x86 = X at *
    bv_decide (config := { enums := false })

/-- The pixel after a small move, from a position on the first page. -/
theorem near_pure (X p x d : UInt8) (hlo : 12 ≤ X) (hhi : X ≤ 75) (hd : d ≤ 3 ∨ 0xFC ≤ d)
    (h : Smb.Routine.pos16 p x = Smb.Routine.pos16 0 X + Smb.Routine.HorizontalLimit.sext16b d) : p = 0 ∧ x < 0x50 := by
  simp only [Smb.Routine.pos16, Smb.Routine.HorizontalLimit.sext16b] at h
  by_cases hs : d < 0x80 <;> simp only [hs, decide_true, decide_false, cond_true, cond_false] at h <;> revert hlo hhi hd hs h <;> bv_decide (config := { enums := false })

/-- What the routine doesn't touch before the collision code, of what the sensors read. -/
def keepC (i : UInt16) : Bool := i == 0x716 || i == 0x0E || i == 0x704 || i == 0x70E || i == 0x754 || inBuf i

theorem pre_keepC (ram : UInt16 → UInt8) (i : UInt16) (hi : keepC i = true) : moveIn 0xF7 ram i = ram i := by
  simp only [keepC, inBuf] at hi
  have hp : ctrlPre_ram ram i = ram i := by
    apply ctrlPre_ram_frame
    simp only [ctrlPre_writes]
    revert hi
    bv_decide (config := { enums := false })
  simp only [moveIn, hp]
  revert hi
  bv_decide (config := { enums := false })

theorem aux_keepC (r prg : UInt16 → UInt8) (i : UInt16) (hi : keepC i = true) : ctrlAux_ram (ctrlMid_s 0xF7) (ctrlMid_ram r) prg i = r i := by
  simp only [keepC, inBuf] at hi
  rw [ctrlAux_ram_frame _ _ _ _ (by simp only [ctrlAux_writes, absIdx]; delta ctrlMid_s; revert hi; bv_decide (config := { enums := false })),
    ctrlMid_ram_frame _ _ (by simp only [ctrlMid_writes]; revert hi; bv_decide (config := { enums := false }))]

theorem j_keepC (i : UInt16) (hi : keepC i = true) : i < 0x100 ∨ 0x200 ≤ i := by
  simp only [keepC, inBuf] at hi
  revert hi
  bv_decide (config := { enums := false })

theorem pixel_pure (X : UInt8) (hlo : 12 ≤ X) (hx : X < 0x50) : 8 ≤ Smb.Routine.pos16 0 X ∧ Smb.Routine.pos16 0 X < 0x8000 := by
  simp only [Smb.Routine.pos16]
  constructor <;> (revert hlo hx; bv_decide (config := { enums := false }))

theorem y_entry (y : UInt8) (h1 : 0x40 ≤ y) (h2 : y ≤ 176) : 0x20 ≤ y ∧ y < 0xE0 := by
  constructor <;> (revert h1 h2; bv_decide (config := { enums := false }))

theorem x_lt (x : UInt8) (h : x < 0x50) : x < 0x60 := by
  revert h; bv_decide (config := { enums := false })

/-! ### State 0 -/

theorem ctrlA0_keepC (ram prg : UInt16 → UInt8) (i : UInt16) (hi : keepC i = true) : ctrlA0_ram 0xF7 ram prg i = ram i := by
  rw [Smb.Routine.ModelFrame.ctrlA0_composition, aux_keepC _ _ _ hi, ms0_ram_frame _ _ _ (by
    simp only [keepC, inBuf] at hi; simp only [ms0_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
  exact pre_keepC ram i hi

/-- At the start of the collision code, in state 0. -/
theorem atBg0 (ram : UInt16 → UInt8) (hL : LCells ram) (hV : VFacts (cellsOf ram)) (ht : ram 0x1D = 0) (hlo : 12 ≤ ram 0x86) (hhi : ram 0x86 ≤ 75)
    (hv : Smb.Routine.HorizontalLimit.speedOk (ram 0x57) = true) :
    Move0Hyps ram ∧ AtBg (frameR0 0xF7 ram romFn) ∧ (frameR0 0xF7 ram romFn 0xCE < 176 ∨ frameR0 0xF7 ram romFn 0x9F < 0x80) ∧
      (frameR0 0xF7 ram romFn 0x1D = 0 → frameR0 0xF7 ram romFn 0xCE = 176 ∧ frameR0 0xF7 ram romFn 0x9F = 0) ∧
      frameR0 0xF7 ram romFn 0xCE = (modelMove ram).y ∧ frameR0 0xF7 ram romFn 0x1D = (modelMove ram).st ∧ frameR0 0xF7 ram romFn 0x9F = (modelMove ram).vy ∧
      ctrlA0_ram 0xF7 ram romFn 0x6D = 0 ∧ ctrlA0_ram 0xF7 ram romFn 0x86 < 0x50 := by
  have hm : Move0Hyps ram := ⟨ht, hL.swim, hL.z, hL.js, by
    have := hV.vy
    show ram 0x9F + 0x40 < 0x80
    have e : (cellsOf ram).vy = ram 0x9F := rfl
    rw [e] at this
    generalize ram 0x9F = q at *
    revert this
    bv_decide (config := { enums := false }), hL.eng, by rw [hL.area]; decide, hL.coll⟩
  have hA := away_of hL hlo
  have hJ (i : UInt16) (hi : i < 0x100 ∨ 0x200 ≤ i) : frameR0 0xF7 ram romFn i = ctrlA0_ram 0xF7 ram romFn i := by
    show ctrlJ_ram (ctrlA0_s 0xF7) (ctrlA0_ram 0xF7 ram romFn) i = _
    rw [ctrlA0_s_eq']
    exact j_other _ i hi
  have hkc (i : UInt16) (hi : keepC i = true) : frameR0 0xF7 ram romFn i = ram i := by
    rw [hJ i (j_keepC i hi)]
    exact ctrlA0_keepC ram romFn i hi
  have hM : modelMove ram = Smb.Movement.fallS (Smb.Movement.moved (inOfRam ram) (cellsOf ram)) := rfl
  have hy : frameR0 0xF7 ram romFn 0xCE = (modelMove ram).y := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA0_y _ _ _ hm
  have hst : frameR0 0xF7 ram romFn 0x1D = (modelMove ram).st := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA0_st _ _ _ hm
  have hvy : frameR0 0xF7 ram romFn 0x9F = (modelMove ram).vy := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA0_vy _ _ _ hm
  have hnear := ctrlA0_near 0xF7 ram romFn hm hA hv
  obtain ⟨hp, hx⟩ := near_pure (ram 0x86) (ctrlA0_ram 0xF7 ram romFn 0x6D) (ctrlA0_ram 0xF7 ram romFn 0x86) _ hlo hhi hnear.2
    (by simpa only [pixelP, hL.page] using hnear.1)
  have e1 : (cellsOf ram).y = ram 0xCE := rfl
  have e2 : (cellsOf ram).vy = ram 0x9F := rfl
  have hb5 : frameR0 0xF7 ram romFn 0xB5 = 1 := by
    rw [hJ _ (Or.inl (by decide)), ctrlA0_post_keep _ _ _ (by decide)]
    refine ms0_b5 _ _ (by rw [pre_other ram _ (by simp)]; exact hL.high) (by rw [pre_other ram _ (by simp)]; exact y_entry _ (e1 ▸ hV.ylo) (e1 ▸ hV.yhi)) (by rw [pre_other ram _ (by simp)]; exact e2 ▸ hV.vy)
      (by rw [pre_other ram _ (by simp)]; exact ht) (by rw [pre_other ram _ (by simp)]; exact hL.swim) (by rw [pre_other ram _ (by simp)]; exact hL.z) (by rw [pre_other ram _ (by simp)]; exact hL.js)
  have hland := hV.mland (inOfRam ram)
  refine ⟨hm, ⟨by rw [hkc _ (by decide)]; exact hL.noExit, by rw [hkc _ (by decide)]; exact hL.eng, hb5, by rw [hst]; exact hV.mst _, by rw [hkc _ (by decide)]; exact hL.swim,
    by rw [hkc _ (by decide)]; exact hL.js, by rw [hkc _ (by decide)]; rw [hL.small]; decide, by rw [hJ _ (Or.inl (by decide))]; exact hp,
    by rw [hJ _ (Or.inl (by decide))]; exact x_lt _ hx, by rw [hy]; exact hV.mlo _, ?_, fun a ha => by rw [hkc a (by simp [keepC, ha])]; exact hL.buf a ha⟩, ?_, fun e => ?_, hy, hst, hvy, hp, hx⟩
  · rw [hy]
    rcases hland with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1⟩
  · rw [hy, hvy]
    rcases hland with h | h
    · exact Or.inl h
    · exact Or.inr h.2.2
  · rw [hst] at e
    rw [hy, hvy]
    exact hV.mground _ e

/-- State 0: the routine's run, from what's known at its entry. -/
theorem routine0 (s : NES) (m : Nat) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (hsS : s.s = 0xF7) (hI : (s.p &&& 4 == 0) = false) (hL : LCells (ramAt s))
    (hV : Smb.Movement.VReach (Smb.Movement.vcells (cellsOf (ramAt s)))) (ht : ramAt s 0x1D = 0) (hlo : 12 ≤ ramAt s 0x86) (hhi : ramAt s 0x86 ≤ 75)
    (hv : Smb.Routine.HorizontalLimit.speedOk (ramAt s 0x57) = true) :
    (∃ F, RoutineRun s m F) ∧ ∀ (inputs : List UInt8) (i f : Nat), PlayerFrame inputs f s m →
      Follows Smb.Movement.openGround inputs i f ∧ Smb.Movement.VReach (Smb.Movement.vcells (stateOf (at' inputs (f + 1)))) := by
  have hVf := Smb.Routine.LaunchVert.vfacts hV
  obtain ⟨hm, hat, hv1, hg, hy, hst, hvy, hp6, hp8⟩ := atBg0 (ramAt s) hL hVf ht hlo hhi hv
  have hsens : Sensors (frameS0 0xF7) (frameR0 0xF7 (ramAt s) romFn) := sensors_of hat
  have hb : OpenBg (frameS0 s.s) (frameR0 s.s (ramAt s) romFn) := by rw [hsS]; exact openBg_of_sensors hsens
  have hb7 : OpenBg (frameS0 0xF7) (frameR0 0xF7 (ramAt s) romFn) := openBg_of_sensors hsens
  have hA := away_of hL hlo
  have hl0 := lands_of hat hv1 hg
  obtain ⟨p', a', x', y', c', w, hr, hf⟩ := frame0_side_nes s hq hprg hpc m hI hm.ht hm.hz hm.hs hm.hjs hm.hspd hb.go hb.headc hb.headh hb.coin hb.axe hb.pipe hb.foot hb.eb hb.noCoin hb.noClimb hb.noPipe
  have hexit : Exit (ramAt s) (frame0_side_ram w 0xF7 (ramAt s) romFn) :=
    side0_exit w (ramAt s) romFn hm ⟨by rw [hL.small]; decide, hL.high, y_entry _ hVf.ylo hVf.yhi, hVf.vy, hL.scroll⟩ (hb7.clear w) rom_climbTilesCode (by
      have e : frameS0 0xF7 = 0xF5 := by show ctrlJ_s (ctrlA0_s 0xF7) = 0xF5; delta ctrlJ_s ctrlA0_s ctrlAux_s ctrlMid_s; rfl
      have := hb7.foot
      rw [e] at this
      exact this)
  have hxp := side0_xpos w (ramAt s) romFn (hb7.clear w) HorizontalLimitNes.rom_climbTable
  refine ⟨⟨⟨⟨frame0_side_pc, a', x', y', frame0_side_s s.s, p'⟩, frame0_side_ram w s.s (ramAt s) romFn, romFn, c', frame0_side_bad s.s (ramAt s) romFn⟩, ?_⟩, fun inputs i f hc => ?_⟩
  · refine ⟨hr, ?_, ?_, by simpa using hf, frame0_side_no_bad _ _ _, ?_, ?_, ?_, ?_⟩
    · delta frame0_side_pc; rfl
    · show frame0_side_s s.s = 0xF7
      rw [hsS]; delta frame0_side_s ctrlAttr_s; rfl
    · intro a _; show romFn (a &&& 0x7FFF) = Smb.Abs.romOf Smb.prg a; simp only [romFn, Smb.Abs.romOf]; rw [Smb.and_idem]
    · show Exit (ramAt s) (frame0_side_ram w s.s (ramAt s) romFn)
      rw [hsS]; exact hexit
    · show frame0_side_ram w s.s (ramAt s) romFn 0x86 < 0x50
      rw [hsS, hxp 0x86 (Or.inl rfl)]; exact hp8
    · show frame0_side_ram w s.s (ramAt s) romFn 0x6D = 0
      rw [hsS, hxp 0x6D (Or.inr rfl)]; exact hp6
  · have hent := hc.entry
    have hyarg : (stateOf (at' inputs f)).st = 0 → (stateOf (at' inputs f)).y &&& 0xF0 = (stateOf (at' inputs f)).y := fun e => by
      have e1 : (cellsOf (ramAt s)).st = (stateOf (at' inputs f)).st := by rw [hent]
      have e2 : (cellsOf (ramAt s)).y = (stateOf (at' inputs f)).y := by rw [hent]
      rw [← e1] at e
      rw [← e2, (hVf.ground e).1]; decide
    have hw : 8 ≤ pixelP (ramAt s) ∧ pixelP (ramAt s) < 0x8000 := by
      simp only [pixelP, hL.page]
      exact pixel_pure _ hlo hL.x
    have hl : lands romFn (bgRam (frameR0 s.s (ramAt s) romFn)) (bgY (frameR0 s.s (ramAt s) romFn)) =
        ((modelMove (ramAt s)).st == 0 || Smb.Routine.ModelStep.landC 176 (modelMove (ramAt s))) := by
      rw [hsS, hl0, hy, hst, hvy]
      rfl
    refine ⟨follows_of_contract0 hc hm hA hv hyarg hb hw hl, ?_⟩
    have hstate := state_of_parts hc (frame0_side_ram w s.s (ramAt s) romFn) _ (fun a ha => by rw [ramAt_of_rel hr a, and7ff_of_lt a ha])
      (frame0_model w s.s (ramAt s) romFn hm hA hv HorizontalLimitNes.rom_climbTable (hb.clear w))
    rw [hstate]
    exact Smb.Routine.LaunchVert.vreach_after (inOfRam (ramAt s)) _ (cellsOf (ramAt s)) hl hVf.ground hV


/-! ### State 1 -/

theorem ctrlA1_keepC (ram prg : UInt16 → UInt8) (i : UInt16) (hi : keepC i = true) : ctrlA1_ram 0xF7 ram prg i = ram i := by
  rw [Smb.Routine.ModelFrame.ctrlA1_composition, aux_keepC _ _ _ hi, ms1_ram_frame _ _ _ (by
    simp only [keepC, inBuf] at hi; simp only [ms1_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
  exact pre_keepC ram i hi

/-- At the start of the collision code, in state 1. -/
theorem atBg1 (ram : UInt16 → UInt8) (hL : LCells ram) (hV : VFacts (cellsOf ram)) (ht : ram 0x1D = 1) (hlo : 12 ≤ ram 0x86) (hhi : ram 0x86 ≤ 75)
    (hv : Smb.Routine.HorizontalLimit.speedOk (ram 0x57) = true) :
    Move1Hyps ram ∧ AtBg (frameR1 0xF7 ram romFn) ∧ (frameR1 0xF7 ram romFn 0xCE < 176 ∨ frameR1 0xF7 ram romFn 0x9F < 0x80) ∧
      (frameR1 0xF7 ram romFn 0x1D = 0 → frameR1 0xF7 ram romFn 0xCE = 176 ∧ frameR1 0xF7 ram romFn 0x9F = 0) ∧
      frameR1 0xF7 ram romFn 0xCE = (modelMove ram).y ∧ frameR1 0xF7 ram romFn 0x1D = (modelMove ram).st ∧ frameR1 0xF7 ram romFn 0x9F = (modelMove ram).vy ∧
      ctrlA1_ram 0xF7 ram romFn 0x6D = 0 ∧ ctrlA1_ram 0xF7 ram romFn 0x86 < 0x50 := by
  have hm : Move1Hyps ram := ⟨ht, hL.swim, hL.z, hL.js, by
    have := hV.vy
    show ram 0x9F + 0x40 < 0x80
    have e : (cellsOf ram).vy = ram 0x9F := rfl
    rw [e] at this
    generalize ram 0x9F = q at *
    revert this
    bv_decide (config := { enums := false }), hL.eng, by rw [hL.area]; decide, hL.coll⟩
  have hA := away_of hL hlo
  have hJ (i : UInt16) (hi : i < 0x100 ∨ 0x200 ≤ i) : frameR1 0xF7 ram romFn i = ctrlA1_ram 0xF7 ram romFn i := by
    show ctrlJ_ram (ctrlA1_s 0xF7) (ctrlA1_ram 0xF7 ram romFn) i = _
    rw [ctrlA1_s_eq']
    exact j_other _ i hi
  have hkc (i : UInt16) (hi : keepC i = true) : frameR1 0xF7 ram romFn i = ram i := by
    rw [hJ i (j_keepC i hi)]
    exact ctrlA1_keepC ram romFn i hi
  have hM : modelMove ram = Smb.Movement.fallS (Smb.Movement.moved (inOfRam ram) (cellsOf ram)) := rfl
  have hy : frameR1 0xF7 ram romFn 0xCE = (modelMove ram).y := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA1_y _ _ _ hm
  have hst : frameR1 0xF7 ram romFn 0x1D = (modelMove ram).st := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA1_st _ _ _ hm
  have hvy : frameR1 0xF7 ram romFn 0x9F = (modelMove ram).vy := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA1_vy _ _ _ hm
  have hnear := ctrlA1_near 0xF7 ram romFn hm hA hv
  obtain ⟨hp, hx⟩ := near_pure (ram 0x86) (ctrlA1_ram 0xF7 ram romFn 0x6D) (ctrlA1_ram 0xF7 ram romFn 0x86) _ hlo hhi hnear.2
    (by simpa only [pixelP, hL.page] using hnear.1)
  have e1 : (cellsOf ram).y = ram 0xCE := rfl
  have e2 : (cellsOf ram).vy = ram 0x9F := rfl
  have hb5 : frameR1 0xF7 ram romFn 0xB5 = 1 := by
    rw [hJ _ (Or.inl (by decide)), ctrlA1_post_keep _ _ _ (by decide)]
    refine ms1_b5 _ _ (by rw [pre_other ram _ (by simp)]; exact hL.high) (by rw [pre_other ram _ (by simp)]; exact y_entry _ (e1 ▸ hV.ylo) (e1 ▸ hV.yhi)) (by rw [pre_other ram _ (by simp)]; exact e2 ▸ hV.vy)
      (by rw [pre_other ram _ (by simp)]; exact ht) (by rw [pre_other ram _ (by simp)]; exact hL.swim) (by rw [pre_other ram _ (by simp)]; exact hL.z) (by rw [pre_other ram _ (by simp)]; exact hL.js)
  have hland := hV.mland (inOfRam ram)
  refine ⟨hm, ⟨by rw [hkc _ (by decide)]; exact hL.noExit, by rw [hkc _ (by decide)]; exact hL.eng, hb5, by rw [hst]; exact hV.mst _, by rw [hkc _ (by decide)]; exact hL.swim,
    by rw [hkc _ (by decide)]; exact hL.js, by rw [hkc _ (by decide)]; rw [hL.small]; decide, by rw [hJ _ (Or.inl (by decide))]; exact hp,
    by rw [hJ _ (Or.inl (by decide))]; exact x_lt _ hx, by rw [hy]; exact hV.mlo _, ?_, fun a ha => by rw [hkc a (by simp [keepC, ha])]; exact hL.buf a ha⟩, ?_, fun e => ?_, hy, hst, hvy, hp, hx⟩
  · rw [hy]
    rcases hland with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1⟩
  · rw [hy, hvy]
    rcases hland with h | h
    · exact Or.inl h
    · exact Or.inr h.2.2
  · rw [hst] at e
    rw [hy, hvy]
    exact hV.mground _ e

/-- State 1: the routine's run, from what's known at its entry. -/
theorem routine1 (s : NES) (m : Nat) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (hsS : s.s = 0xF7) (hI : (s.p &&& 4 == 0) = false) (hL : LCells (ramAt s))
    (hV : Smb.Movement.VReach (Smb.Movement.vcells (cellsOf (ramAt s)))) (ht : ramAt s 0x1D = 1) (hlo : 12 ≤ ramAt s 0x86) (hhi : ramAt s 0x86 ≤ 75)
    (hv : Smb.Routine.HorizontalLimit.speedOk (ramAt s 0x57) = true) :
    (∃ F, RoutineRun s m F) ∧ ∀ (inputs : List UInt8) (i f : Nat), PlayerFrame inputs f s m →
      Follows Smb.Movement.openGround inputs i f ∧ Smb.Movement.VReach (Smb.Movement.vcells (stateOf (at' inputs (f + 1)))) := by
  have hVf := Smb.Routine.LaunchVert.vfacts hV
  obtain ⟨hm, hat, hv1, hg, hy, hst, hvy, hp6, hp8⟩ := atBg1 (ramAt s) hL hVf ht hlo hhi hv
  have hsens : Sensors (frameS1 0xF7) (frameR1 0xF7 (ramAt s) romFn) := sensors_of hat
  have hb : OpenBg (frameS1 s.s) (frameR1 s.s (ramAt s) romFn) := by rw [hsS]; exact openBg_of_sensors hsens
  have hb7 : OpenBg (frameS1 0xF7) (frameR1 0xF7 (ramAt s) romFn) := openBg_of_sensors hsens
  have hA := away_of hL hlo
  have hl0 := lands_of hat hv1 hg
  obtain ⟨p', a', x', y', c', w, hr, hf⟩ := frame1_side_nes s hq hprg hpc m hI hm.ht hm.hz hm.hs hm.hjs hm.hspd hb.go hb.headc hb.headh hb.coin hb.axe hb.pipe hb.foot hb.eb hb.noCoin hb.noClimb hb.noPipe
  have hexit : Exit (ramAt s) (frame1_side_ram w 0xF7 (ramAt s) romFn) :=
    side1_exit w (ramAt s) romFn hm ⟨by rw [hL.small]; decide, hL.high, y_entry _ hVf.ylo hVf.yhi, hVf.vy, hL.scroll⟩ (hb7.clear w) rom_climbTilesCode (by
      have e : frameS1 0xF7 = 0xF5 := by show ctrlJ_s (ctrlA1_s 0xF7) = 0xF5; delta ctrlJ_s ctrlA1_s ctrlAux_s ctrlMid_s; rfl
      have := hb7.foot
      rw [e] at this
      exact this)
  have hxp := side1_xpos w (ramAt s) romFn (hb7.clear w) HorizontalLimitNes.rom_climbTable
  refine ⟨⟨⟨⟨frame1_side_pc, a', x', y', frame1_side_s s.s, p'⟩, frame1_side_ram w s.s (ramAt s) romFn, romFn, c', frame1_side_bad s.s (ramAt s) romFn⟩, ?_⟩, fun inputs i f hc => ?_⟩
  · refine ⟨hr, ?_, ?_, by simpa using hf, frame1_side_no_bad _ _ _, ?_, ?_, ?_, ?_⟩
    · delta frame1_side_pc; rfl
    · show frame1_side_s s.s = 0xF7
      rw [hsS]; delta frame1_side_s ctrlAttr_s; rfl
    · intro a _; show romFn (a &&& 0x7FFF) = Smb.Abs.romOf Smb.prg a; simp only [romFn, Smb.Abs.romOf]; rw [Smb.and_idem]
    · show Exit (ramAt s) (frame1_side_ram w s.s (ramAt s) romFn)
      rw [hsS]; exact hexit
    · show frame1_side_ram w s.s (ramAt s) romFn 0x86 < 0x50
      rw [hsS, hxp 0x86 (Or.inl rfl)]; exact hp8
    · show frame1_side_ram w s.s (ramAt s) romFn 0x6D = 0
      rw [hsS, hxp 0x6D (Or.inr rfl)]; exact hp6
  · have hent := hc.entry
    have hyarg : (stateOf (at' inputs f)).st = 0 → (stateOf (at' inputs f)).y &&& 0xF0 = (stateOf (at' inputs f)).y := fun e => by
      have e1 : (cellsOf (ramAt s)).st = (stateOf (at' inputs f)).st := by rw [hent]
      have e2 : (cellsOf (ramAt s)).y = (stateOf (at' inputs f)).y := by rw [hent]
      rw [← e1] at e
      rw [← e2, (hVf.ground e).1]; decide
    have hw : 8 ≤ pixelP (ramAt s) ∧ pixelP (ramAt s) < 0x8000 := by
      simp only [pixelP, hL.page]
      exact pixel_pure _ hlo hL.x
    have hl : lands romFn (bgRam (frameR1 s.s (ramAt s) romFn)) (bgY (frameR1 s.s (ramAt s) romFn)) =
        ((modelMove (ramAt s)).st == 0 || Smb.Routine.ModelStep.landC 176 (modelMove (ramAt s))) := by
      rw [hsS, hl0, hy, hst, hvy]
      rfl
    refine ⟨follows_of_contract1 hc hm hA hv hyarg hb hw hl, ?_⟩
    have hstate := state_of_parts hc (frame1_side_ram w s.s (ramAt s) romFn) _ (fun a ha => by rw [ramAt_of_rel hr a, and7ff_of_lt a ha])
      (frame1_model w s.s (ramAt s) romFn hm hA hv HorizontalLimitNes.rom_climbTable (hb.clear w))
    rw [hstate]
    exact Smb.Routine.LaunchVert.vreach_after (inOfRam (ramAt s)) _ (cellsOf (ramAt s)) hl hVf.ground hV


/-! ### State 2 -/

theorem ctrlA2_keepC (ram prg : UInt16 → UInt8) (i : UInt16) (hi : keepC i = true) : ctrlA2_ram 0xF7 ram prg i = ram i := by
  rw [Smb.Routine.ModelFrame.ctrlA2_composition, aux_keepC _ _ _ hi, ms2_ram_frame _ _ _ (by
    simp only [keepC, inBuf] at hi; simp only [ms2_writes, dummyIdx, yPosIdx, yHighIdx, yForceIdx, ySpeedIdx]; revert hi; bv_decide (config := { enums := false }))]
  exact pre_keepC ram i hi

/-- At the start of the collision code, in state 2. -/
theorem atBg2 (ram : UInt16 → UInt8) (hL : LCells ram) (hV : VFacts (cellsOf ram)) (ht : ram 0x1D = 2) (hlo : 12 ≤ ram 0x86) (hhi : ram 0x86 ≤ 75)
    (hv : Smb.Routine.HorizontalLimit.speedOk (ram 0x57) = true) :
    Move2Hyps ram ∧ AtBg (frameR2 0xF7 ram romFn) ∧ (frameR2 0xF7 ram romFn 0xCE < 176 ∨ frameR2 0xF7 ram romFn 0x9F < 0x80) ∧
      (frameR2 0xF7 ram romFn 0x1D = 0 → frameR2 0xF7 ram romFn 0xCE = 176 ∧ frameR2 0xF7 ram romFn 0x9F = 0) ∧
      frameR2 0xF7 ram romFn 0xCE = (modelMove ram).y ∧ frameR2 0xF7 ram romFn 0x1D = (modelMove ram).st ∧ frameR2 0xF7 ram romFn 0x9F = (modelMove ram).vy ∧
      ctrlA2_ram 0xF7 ram romFn 0x6D = 0 ∧ ctrlA2_ram 0xF7 ram romFn 0x86 < 0x50 := by
  have hm : Move2Hyps ram := ⟨ht, hL.swim, hL.z, hL.js, by
    have := hV.vy
    show ram 0x9F + 0x40 < 0x80
    have e : (cellsOf ram).vy = ram 0x9F := rfl
    rw [e] at this
    generalize ram 0x9F = q at *
    revert this
    bv_decide (config := { enums := false }), hL.eng, by rw [hL.area]; decide, hL.coll⟩
  have hA := away_of hL hlo
  have hJ (i : UInt16) (hi : i < 0x100 ∨ 0x200 ≤ i) : frameR2 0xF7 ram romFn i = ctrlA2_ram 0xF7 ram romFn i := by
    show ctrlJ_ram (ctrlA2_s 0xF7) (ctrlA2_ram 0xF7 ram romFn) i = _
    rw [ctrlA2_s_eq']
    exact j_other _ i hi
  have hkc (i : UInt16) (hi : keepC i = true) : frameR2 0xF7 ram romFn i = ram i := by
    rw [hJ i (j_keepC i hi)]
    exact ctrlA2_keepC ram romFn i hi
  have hM : modelMove ram = Smb.Movement.fallS (Smb.Movement.moved (inOfRam ram) (cellsOf ram)) := rfl
  have hy : frameR2 0xF7 ram romFn 0xCE = (modelMove ram).y := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA2_y _ _ _ hm
  have hst : frameR2 0xF7 ram romFn 0x1D = (modelMove ram).st := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA2_st _ _ _ hm
  have hvy : frameR2 0xF7 ram romFn 0x9F = (modelMove ram).vy := by
    rw [hJ _ (Or.inl (by decide))]; exact ctrlA2_vy _ _ _ hm
  have hnear := ctrlA2_near 0xF7 ram romFn hm hA hv
  obtain ⟨hp, hx⟩ := near_pure (ram 0x86) (ctrlA2_ram 0xF7 ram romFn 0x6D) (ctrlA2_ram 0xF7 ram romFn 0x86) _ hlo hhi hnear.2
    (by simpa only [pixelP, hL.page] using hnear.1)
  have e1 : (cellsOf ram).y = ram 0xCE := rfl
  have e2 : (cellsOf ram).vy = ram 0x9F := rfl
  have hb5 : frameR2 0xF7 ram romFn 0xB5 = 1 := by
    rw [hJ _ (Or.inl (by decide)), ctrlA2_post_keep _ _ _ (by decide)]
    refine ms2_b5 _ _ (by rw [pre_other ram _ (by simp)]; exact hL.high) (by rw [pre_other ram _ (by simp)]; exact y_entry _ (e1 ▸ hV.ylo) (e1 ▸ hV.yhi)) (by rw [pre_other ram _ (by simp)]; exact e2 ▸ hV.vy)
      (by rw [pre_other ram _ (by simp)]; exact ht) (by rw [pre_other ram _ (by simp)]; exact hL.swim) (by rw [pre_other ram _ (by simp)]; exact hL.z) (by rw [pre_other ram _ (by simp)]; exact hL.js)
  have hland := hV.mland (inOfRam ram)
  refine ⟨hm, ⟨by rw [hkc _ (by decide)]; exact hL.noExit, by rw [hkc _ (by decide)]; exact hL.eng, hb5, by rw [hst]; exact hV.mst _, by rw [hkc _ (by decide)]; exact hL.swim,
    by rw [hkc _ (by decide)]; exact hL.js, by rw [hkc _ (by decide)]; rw [hL.small]; decide, by rw [hJ _ (Or.inl (by decide))]; exact hp,
    by rw [hJ _ (Or.inl (by decide))]; exact x_lt _ hx, by rw [hy]; exact hV.mlo _, ?_, fun a ha => by rw [hkc a (by simp [keepC, ha])]; exact hL.buf a ha⟩, ?_, fun e => ?_, hy, hst, hvy, hp, hx⟩
  · rw [hy]
    rcases hland with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1⟩
  · rw [hy, hvy]
    rcases hland with h | h
    · exact Or.inl h
    · exact Or.inr h.2.2
  · rw [hst] at e
    rw [hy, hvy]
    exact hV.mground _ e

/-- State 2: the routine's run, from what's known at its entry. -/
theorem routine2 (s : NES) (m : Nat) (hq : s.Quiet) (hprg : s.prg = Smb.prg) (hpc : s.pc = 0xB0E9) (hsS : s.s = 0xF7) (hI : (s.p &&& 4 == 0) = false) (hL : LCells (ramAt s))
    (hV : Smb.Movement.VReach (Smb.Movement.vcells (cellsOf (ramAt s)))) (ht : ramAt s 0x1D = 2) (hlo : 12 ≤ ramAt s 0x86) (hhi : ramAt s 0x86 ≤ 75)
    (hv : Smb.Routine.HorizontalLimit.speedOk (ramAt s 0x57) = true) :
    (∃ F, RoutineRun s m F) ∧ ∀ (inputs : List UInt8) (i f : Nat), PlayerFrame inputs f s m →
      Follows Smb.Movement.openGround inputs i f ∧ Smb.Movement.VReach (Smb.Movement.vcells (stateOf (at' inputs (f + 1)))) := by
  have hVf := Smb.Routine.LaunchVert.vfacts hV
  obtain ⟨hm, hat, hv1, hg, hy, hst, hvy, hp6, hp8⟩ := atBg2 (ramAt s) hL hVf ht hlo hhi hv
  have hsens : Sensors (frameS2 0xF7) (frameR2 0xF7 (ramAt s) romFn) := sensors_of hat
  have hb : OpenBg (frameS2 s.s) (frameR2 s.s (ramAt s) romFn) := by rw [hsS]; exact openBg_of_sensors hsens
  have hb7 : OpenBg (frameS2 0xF7) (frameR2 0xF7 (ramAt s) romFn) := openBg_of_sensors hsens
  have hA := away_of hL hlo
  have hl0 := lands_of hat hv1 hg
  obtain ⟨p', a', x', y', c', w, hr, hf⟩ := frame2_side_nes s hq hprg hpc m hI hm.ht hm.hz hm.hs hm.hjs hm.hspd hb.go hb.headc hb.headh hb.coin hb.axe hb.pipe hb.foot hb.eb hb.noCoin hb.noClimb hb.noPipe
  have hexit : Exit (ramAt s) (frame2_side_ram w 0xF7 (ramAt s) romFn) :=
    side2_exit w (ramAt s) romFn hm ⟨by rw [hL.small]; decide, hL.high, y_entry _ hVf.ylo hVf.yhi, hVf.vy, hL.scroll⟩ (hb7.clear w) rom_climbTilesCode (by
      have e : frameS2 0xF7 = 0xF5 := by show ctrlJ_s (ctrlA2_s 0xF7) = 0xF5; delta ctrlJ_s ctrlA2_s ctrlAux_s ctrlMid_s; rfl
      have := hb7.foot
      rw [e] at this
      exact this)
  have hxp := side2_xpos w (ramAt s) romFn (hb7.clear w) HorizontalLimitNes.rom_climbTable
  refine ⟨⟨⟨⟨frame2_side_pc, a', x', y', frame2_side_s s.s, p'⟩, frame2_side_ram w s.s (ramAt s) romFn, romFn, c', frame2_side_bad s.s (ramAt s) romFn⟩, ?_⟩, fun inputs i f hc => ?_⟩
  · refine ⟨hr, ?_, ?_, by simpa using hf, frame2_side_no_bad _ _ _, ?_, ?_, ?_, ?_⟩
    · delta frame2_side_pc; rfl
    · show frame2_side_s s.s = 0xF7
      rw [hsS]; delta frame2_side_s ctrlAttr_s; rfl
    · intro a _; show romFn (a &&& 0x7FFF) = Smb.Abs.romOf Smb.prg a; simp only [romFn, Smb.Abs.romOf]; rw [Smb.and_idem]
    · show Exit (ramAt s) (frame2_side_ram w s.s (ramAt s) romFn)
      rw [hsS]; exact hexit
    · show frame2_side_ram w s.s (ramAt s) romFn 0x86 < 0x50
      rw [hsS, hxp 0x86 (Or.inl rfl)]; exact hp8
    · show frame2_side_ram w s.s (ramAt s) romFn 0x6D = 0
      rw [hsS, hxp 0x6D (Or.inr rfl)]; exact hp6
  · have hent := hc.entry
    have hyarg : (stateOf (at' inputs f)).st = 0 → (stateOf (at' inputs f)).y &&& 0xF0 = (stateOf (at' inputs f)).y := fun e => by
      have e1 : (cellsOf (ramAt s)).st = (stateOf (at' inputs f)).st := by rw [hent]
      have e2 : (cellsOf (ramAt s)).y = (stateOf (at' inputs f)).y := by rw [hent]
      rw [← e1] at e
      rw [← e2, (hVf.ground e).1]; decide
    have hw : 8 ≤ pixelP (ramAt s) ∧ pixelP (ramAt s) < 0x8000 := by
      simp only [pixelP, hL.page]
      exact pixel_pure _ hlo hL.x
    have hl : lands romFn (bgRam (frameR2 s.s (ramAt s) romFn)) (bgY (frameR2 s.s (ramAt s) romFn)) =
        ((modelMove (ramAt s)).st == 0 || Smb.Routine.ModelStep.landC 176 (modelMove (ramAt s))) := by
      rw [hsS, hl0, hy, hst, hvy]
      rfl
    refine ⟨follows_of_contract2 hc hm hA hv hyarg hb hw hl, ?_⟩
    have hstate := state_of_parts hc (frame2_side_ram w s.s (ramAt s) romFn) _ (fun a ha => by rw [ramAt_of_rel hr a, and7ff_of_lt a ha])
      (frame2_model w s.s (ramAt s) romFn hm hA hv HorizontalLimitNes.rom_climbTable (hb.clear w))
    rw [hstate]
    exact Smb.Routine.LaunchVert.vreach_after (inOfRam (ramAt s)) _ (cellsOf (ramAt s)) hl hVf.ground hV


/-! ## A whole frame -/

theorem at_succ (inputs : List UInt8) (f : Nat) (hf : f < inputs.length) : at' inputs (f + 1) = NES.frame inputs[f] 0 (at' inputs f) := by
  simp only [at', NES.runFrames, List.take_add_one, List.getElem?_eq_getElem hf, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- What's assumed of a frame's timing: the hypotheses of `frame_run`. -/
structure Timing (s0 : NES) (j : Nat) : Prop where
  hu : ∀ i, i ≤ j → (Smb.Abs.stepN i s0).unmodelled = false
  hend : (Smb.Abs.stepN j s0).pc = 0x8057
  hcut : ∀ k k2, k ≤ j → (Smb.Abs.stepN k s0).pc = 0xB0E9 → (Smb.Abs.stepN (k + k2) s0).pc = 0xB179 → k + k2 ≤ j
  hT : ∀ i, i ≤ j → (Smb.Abs.stepN i s0).pc ≠ 0xB79A
  hN : ∀ i i', i ≤ i' → i' ≤ j → (Smb.Abs.stepN i s0).pc = 0xAF6B → (Smb.Abs.stepN i' s0).pc ≠ 0x808F

theorem g_clean : (List.range 256).all (fun n => !(decide (UInt8.ofNat n ≤ cleanLimit)) || (gAt G 0x300).mem (UInt8.ofNat n)) = true ∧
    (List.range 256).all (fun n => !(decide (UInt8.ofNat n ≤ cleanLimit2)) || (gAt G 0x340).mem (UInt8.ofNat n)) = true := by native_decide

/-- `NoOverflow`'s form of the limits gives `CleanIf`. -/
theorem cleanIf_of_cleanAt {x : NES} (h : cleanAt x = true) : Smb.Routine.LaunchPhase.CleanIf x := fun h1 h2 => by
  refine clean_of_cleanAt (fun v hv => ?_) (fun v hv => ?_) ?_ h
  · have := forall_u8 (fun v => !(decide (v ≤ cleanLimit)) || (gAt G 0x300).mem v) g_clean.1 v
    simpa [hv] using this
  · have := forall_u8 (fun v => !(decide (v ≤ cleanLimit2)) || (gAt G 0x340).mem v) g_clean.2 v
    simpa [hv] using this
  · have e1 : byte x 0x770 = 1 := h1
    have e2 : byte x 0x772 = 3 := h2
    simp [inPlay, inGame, e1, e2]

/-- A frame's loop that stays clean does so at each of its instructions. -/
theorem goClean_steps (n : Nat) (s : NES) (h : goClean n s = true) (j : Nat) (hgo : NES.frame.go n s = Smb.Abs.stepN j s) (hu : (NES.frame.go n s).unmodelled = false)
    (hd : ∀ i, i < j → (Smb.Abs.stepN i s).frameDone = false) : ∀ i, i < j → cleanAt (Smb.Abs.stepN (i + 1) s) = true := by
  induction n generalizing s j with
  | zero => simp [NES.frame.go] at hu
  | succ n ih =>
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h0 : s.frameDone = false := hd 0 (by omega)
    simp only [goClean, h0, Bool.false_or, Bool.and_eq_true] at h
    simp only [NES.frame.go, h0, Bool.false_eq_true, if_false] at hgo hu
    cases i with
    | zero => exact h.1
    | succ i => exact ih _ h.2 j hgo hu (fun i' hi' => hd (i' + 1) (by omega)) i (by omega)

/-- The vertical cells don't see `$783`. -/
theorem vcells_t783 (x : Smb.Movement.S) (t : UInt8) : Smb.Movement.vcells { x with t783 := t } = Smb.Movement.vcells x := by
  simp only [Smb.Movement.vcells]

theorem norm_t783 (m : Smb.Movement.Mode) (x : Smb.Movement.S) (t : UInt8) : Smb.Movement.norm m { x with t783 := t } = Smb.Movement.norm m x := by
  simp only [Smb.Movement.norm]
  repeat' split
  all_goals simp_all

/-- The model's cells, when everything but `$783` is as it was. -/
theorem cells_of_kept {r r' : UInt16 → UInt8} (h : ∀ a ∈ Smb.Routine.LaunchPhase.keptAll, r a = r' a) : cellsOf r = { cellsOf r' with t783 := r 0x783 } := by
  have m (a : UInt16) (ha : a ∈ Smb.Routine.LaunchPhase.keptAll) := h a ha
  simp only [cellsOf]
  rw [m 0x57 (by decide), m 0x705 (by decide), m 0x700 (by decide), m 0x33 (by decide), m 0x45 (by decide), m 0x1D (by decide), m 0x703 (by decide), m 0xCE (by decide), m 0x416 (by decide),
    m 0x9F (by decide), m 0x433 (by decide), m 0x709 (by decide), m 0x70A (by decide), m 0x708 (by decide), m 0x706 (by decide), m 0x0D (by decide)]

/-- The facts at the routine's entry, from the bounds and the kept cells. -/
theorem entry_facts {s A : NES} (hG : ∀ i, (gAt G i).mem (ramAt s i) = true) (hk : ∀ a ∈ Smb.Routine.LaunchPhase.keptAll, ramAt s a = ramAt A a)
    (hV : Smb.Movement.VReach (Smb.Movement.vcells (stateOf A))) (hlo : 12 ≤ ramAt A 0x86) (hhi : ramAt A 0x86 ≤ 75)
    (hv : Smb.Routine.HorizontalLimit.speedOk (ramAt A 0x57) = true) :
    LCells (ramAt s) ∧ Smb.Movement.VReach (Smb.Movement.vcells (cellsOf (ramAt s))) ∧ 12 ≤ ramAt s 0x86 ∧ ramAt s 0x86 ≤ 75 ∧
      Smb.Routine.HorizontalLimit.speedOk (ramAt s 0x57) = true ∧ ramAt s 0x1D ≤ 2 := by
  have e := cells_of_kept hk
  have hVs : Smb.Movement.VReach (Smb.Movement.vcells (cellsOf (ramAt s))) := by
    rw [e, vcells_t783]; exact hV
  have e86 := hk 0x86 (by decide)
  have e57 := hk 0x57 (by decide)
  refine ⟨lcells hG, hVs, by rw [e86]; exact hlo, by rw [e86]; exact hhi, by rw [e57]; exact hv, (Smb.Routine.LaunchVert.vfacts hVs).st⟩

theorem st_cases (x : UInt8) (h : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  revert h; bv_decide (config := { enums := false })

theorem ab_bit (x : UInt8) : (x &&& 0xC0) &&& 0x80 = x &&& 0x80 := by bv_decide (config := { enums := false })

theorem screen_pure (x : UInt8) (h : x < 0x50) : Smb.Routine.pos16 0 x - Smb.Routine.pos16 0 0 < 0x8000 := by
  simp only [Smb.Routine.pos16]
  revert h; bv_decide (config := { enums := false })

set_option maxHeartbeats 8000000 in
/-- **A launch frame follows the model.** Given the regions' invariant at its start, a vertical state in the closure, a position on the first screen, and the frame's timing, the frame follows the model and the invariant holds again at its end. -/
theorem launch_frame {inputs : List UInt8} {i f : Nat} (hf : f < inputs.length) (h0 : Smb.Abs.FInvAt (at' inputs f))
    (hstart : (at' inputs f).pc = 0x8057) (hV : Smb.Movement.VReach (Smb.Movement.vcells (stateOf (at' inputs f))))
    (hlo : 12 ≤ ramAt (at' inputs f) 0x86) (hhi : ramAt (at' inputs f) 0x86 ≤ 75) (hv : Smb.Routine.HorizontalLimit.speedOk (ramAt (at' inputs f) 0x57) = true)
    (hun : (at' inputs (f + 1)).unmodelled = false)
    (hC : goClean NES.frameFuel (startFrame inputs[f] (at' inputs f)) = true)
    (hT : ∀ j, at' inputs (f + 1) = Smb.Abs.stepN j (Smb.Routine.FrameRun.startFrame inputs[f] 0 (at' inputs f)) → Timing (Smb.Routine.FrameRun.startFrame inputs[f] 0 (at' inputs f)) j) :
    (at' inputs (f + 1)).pc = 0x8057 ∧ Smb.Abs.FInvAt (at' inputs (f + 1)) ∧ Smb.Movement.VReach (Smb.Movement.vcells (stateOf (at' inputs (f + 1)))) ∧ Follows Smb.Movement.openGround inputs i f := by
  generalize hA : at' inputs f = A at *
  have hstep : at' inputs (f + 1) = NES.frame.go NES.frameFuel (Smb.Routine.FrameRun.startFrame inputs[f] 0 A) := by
    rw [at_succ inputs f hf, hA]; rfl
  have hgoU : (NES.frame.go NES.frameFuel (Smb.Routine.FrameRun.startFrame inputs[f] 0 A)).unmodelled = false := by rw [← hstep]; exact hun
  obtain ⟨j, hj, _, hnd⟩ := Smb.Routine.RunSteps.go_stepN NES.frameFuel _ hgoU
  have hC' : goClean NES.frameFuel (Smb.Routine.FrameRun.startFrame inputs[f] 0 A) = true := hC
  have hAj := fun i hi => cleanIf_of_cleanAt (goClean_steps _ _ hC' j hj hgoU hnd i hi)
  generalize hs0 : Smb.Routine.FrameRun.startFrame inputs[f] 0 A = s0 at *
  have hE : at' inputs (f + 1) = Smb.Abs.stepN j s0 := by rw [hstep, hj]
  have hTm := hT j hE
  have hF0 : Smb.Abs.FInvAt s0 := by rw [← hs0]; exact Smb.Routine.FrameRun.finv_start _ _ h0
  have hram : ∀ a, ramAt s0 a = ramAt A a := fun a => by rw [← hs0]; rfl
  have hpc0 : s0.pc ≠ 0xB0E9 := by
    have : s0.pc = 0x8057 := by rw [← hs0]; exact hstart
    rw [this]; decide
  have hkeep0 {s : NES} (hk : ∀ a ∈ Smb.Routine.LaunchPhase.keptAll, ramAt s a = ramAt s0 a) : ∀ a ∈ Smb.Routine.LaunchPhase.keptAll, ramAt s a = ramAt A a := fun a ha => by
    rw [hk a ha, hram]
  obtain ⟨hFend, hcase⟩ := Smb.Routine.LaunchPhase.frame_run s0 j hF0 hTm.hu hAj hpc0 hTm.hend
    (fun s hpc hq hprg hsS hI hG hk => by
      obtain ⟨hL, hVs, hl, hh, hvs, hst⟩ := entry_facts hG (hkeep0 hk) hV hlo hhi hv
      rcases st_cases _ hst with ht | ht | ht
      · obtain ⟨⟨F, hR⟩, _⟩ := routine0 s 0 hq hprg hpc hsS hI hL hVs ht hl hh hvs
        exact ⟨0, F, hR⟩
      · obtain ⟨⟨F, hR⟩, _⟩ := routine1 s 0 hq hprg hpc hsS hI hL hVs ht hl hh hvs
        exact ⟨0, F, hR⟩
      · obtain ⟨⟨F, hR⟩, _⟩ := routine2 s 0 hq hprg hpc hsS hI hL hVs ht hl hh hvs
        exact ⟨0, F, hR⟩)
    hTm.hcut hTm.hT hTm.hN
  rw [← hE] at hFend hcase
  refine ⟨by rw [hE]; exact hTm.hend, hFend, ?_⟩
  rcases hcase with ⟨hk, _⟩ | ⟨k, m, F, _, hpc, hk, hR, hq, hprg, hsS, hI, hG, hkept, h0D, h783⟩
  · have hk' : ∀ a ∈ Smb.Routine.LaunchPhase.keptAll, ramAt (at' inputs (f + 1)) a = ramAt A a := hkeep0 hk
    have e := cells_of_kept hk'
    refine ⟨?_, follows_of_still ⟨?_, ?_⟩⟩
    · rw [stateOf_eq, e, vcells_t783, ← stateOf_eq]; exact hV
    · simp only [view]
      rw [hA, stateOf_eq, stateOf_eq, e, norm_t783]
    · simp only [pos, Smb.Routine.HorizontalLimit.phi, pixelP, leftL, hA, hk' 0x6D (by decide), hk' 0x86 (by decide), hk' 0x71A (by decide), hk' 0x71C (by decide), hk' 0x400 (by decide)]
  · generalize hs : Smb.Abs.stepN k s0 = s at *
    have hkA := hkeep0 hk
    obtain ⟨hL, hVs, hl, hh, hvs, hst⟩ := entry_facts hG hkA hV hlo hhi hv
    have hrunRam (a : UInt16) (ha : a < 0x800) : ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 a = F.ram a := by
      rw [ramAt_of_rel hR.rel a, and7ff_of_lt a ha]
    have hO (a : UInt16) (ha : a ∈ Smb.Routine.LaunchPhase.keptAll) (hne : a ≠ 0x0D) : ramAt (at' inputs (f + 1)) a = ramAt ((CPU.runTo (σ := NES) 0xB179 (m + 3000)).run s).2 a := by
      rw [hkept a ha hne, hrunRam a (by simpa using List.all_eq_true.mp Smb.Routine.LaunchPhase.kept_lt a ha)]
    have hc : PlayerFrame inputs f s m := by
      refine { quiet := hq, prg := hprg, pc := hpc, iflag := hI, entry := ?_, page := ?_, pixel := ?_, frac := ?_, left1 := ?_, left2 := ?_,
               out57 := hO _ (by decide) (by decide), out705 := hO _ (by decide) (by decide), out700 := hO _ (by decide) (by decide), out33 := hO _ (by decide) (by decide), out45 := hO _ (by decide) (by decide),
               out1d := hO _ (by decide) (by decide), out783 := ?_, out703 := hO _ (by decide) (by decide), outce := hO _ (by decide) (by decide), out416 := hO _ (by decide) (by decide),
               out9f := hO _ (by decide) (by decide), out433 := hO _ (by decide) (by decide), out709 := hO _ (by decide) (by decide), out70a := hO _ (by decide) (by decide), out708 := hO _ (by decide) (by decide),
               out706 := hO _ (by decide) (by decide), outPage := hO _ (by decide) (by decide), outPixel := hO _ (by decide) (by decide), outFrac := hO _ (by decide) (by decide), saveAB := ?_, onScreen := ?_ }
      · rw [hA, stateOf_eq]; exact cells_of_kept hkA
      · rw [hA]; exact hkA _ (by decide)
      · rw [hA]; exact hkA _ (by decide)
      · rw [hA]; exact hkA _ (by decide)
      · rw [hA]; exact hkA _ (by decide)
      · rw [hA]; exact hkA _ (by decide)
      · rw [h783, hrunRam _ (by decide)]
      · show ramAt (at' inputs (f + 1)) 0x0D &&& 0x80 = _
        rw [h0D, hR.exit.ab, ab_bit]
      · simp only [pixelP, leftL]
        rw [hkept 0x6D (by decide) (by decide), hkept 0x86 (by decide) (by decide), hkept 0x71A (by decide) (by decide), hkept 0x71C (by decide) (by decide),
          hR.page, hR.exit.left1, hR.exit.left2, hL.l1, hL.l2]
        exact screen_pure _ hR.low
    have fin (h : Follows Smb.Movement.openGround inputs i f ∧ Smb.Movement.VReach (Smb.Movement.vcells (stateOf (at' inputs (f + 1))))) := And.intro h.2 h.1
    rcases st_cases _ hst with ht | ht | ht
    · exact fin ((routine0 s m hq hprg hpc hsS hI hL hVs ht hl hh hvs).2 inputs i f hc)
    · exact fin ((routine1 s m hq hprg hpc hsS hI hL hVs ht hl hh hvs).2 inputs i f hc)
    · exact fin ((routine2 s m hq hprg hpc hsS hI hL hVs ht hl hh hvs).2 inputs i f hc)

theorem pack_pure (X q : UInt8) : (Smb.Routine.HorizontalLimit.pack (Smb.Routine.pos16 0 X) q).toNat = X.toNat * 256 + q.toNat := by
  have e : Smb.Routine.HorizontalLimit.pack (Smb.Routine.pos16 0 X) q = X.toUInt32 * 256 + q.toUInt32 := by
    simp only [Smb.Routine.HorizontalLimit.pack, Smb.Routine.pos16]
    bv_decide (config := { enums := false })
  have hX := X.toNat_lt
  have hq := q.toNat_lt
  have h256 : (256 : UInt32).toNat = 256 := rfl
  rw [e, UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, h256]
  omega

/-- On the first screen, the position is the pixel and the fraction. -/
theorem pos_of_cells {s : NES} (hL : LCells (ramAt s)) : pos s = (ramAt s 0x86).toNat * 256 + (ramAt s 0x400).toNat := by
  have hx := hL.x
  have e : Smb.Routine.HorizontalLimit.phi (ramAt s) = Smb.Routine.HorizontalLimit.pack (Smb.Routine.pos16 0 (ramAt s 0x86)) (ramAt s 0x400) := by
    simp only [Smb.Routine.HorizontalLimit.phi, pixelP, leftL, hL.page, hL.l1, hL.l2]
    have := screen_pure _ hx
    simp [this]
  simp only [pos, e]
  exact pack_pure _ _

end Smb.Goal.OneOne
