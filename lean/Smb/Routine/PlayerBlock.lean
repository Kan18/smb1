import Smb.Routine.FrameCollision
import Smb.Routine.PlayerSplit
import Smb.Routine.HoldsAfter
import Smb.Routine.Launch

/-!
# The player block: `PlayerCtrlRoutine` and what follows it, to the return into the engine

`block0`: a ground-state frame's player code from `PlayerCtrlRoutine` (`$B0E9`) to the player region's return into
the engine (`$AF01`), on the plain machine. A run that reaches `$AF01` keeps the speed limit and moves Mario at most
2.5 pixels (`XStep` from the entry RAM to the RAM there), or passed one of the exits that end normal play: a pipe
entry, the side pipe, the flag grab, climbing, or a death in a pit.

It's `FrameCollision.frame0_any` carried on past `PlayerHole`: the collision region's boxes at its return and at
`ImpedePlayerMove`, carried through the impede, the RTS steps and the attribute update (`coverAfter`), lie in the
second region's entry (`PlayerSplit`), which keeps the horizontal bytes to `$AF01`.
-/
namespace Smb.Routine.PlayerBlock
open Smb Smb.Abs Smb.Routine Smb.Routine.HorizontalLimit Smb.Abs.Collision Smb.Routine.Collision
open Smb.Routine.FrameCollision Smb.Routine.Launch

theorem stopA' : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ 0xAF01 := by
  intro a h; revert h; bv_decide (config := { enums := false })
theorem stopJ' : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ 0xAF01 := by
  intro a h; revert h; bv_decide (config := { enums := false })
theorem stopAttr' : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ 0xAF01 := by
  intro a h; revert h; bv_decide (config := { enums := false })
theorem stopImp' : ∀ a : UInt16, (0xDF4B ≤ a && a ≤ 0xDF8A) = true → a ≠ 0xAF01 := by
  intro a h; revert h; bv_decide (config := { enums := false })

theorem attr_keep (r : UInt16 → UInt8) (i : UInt16) (hi : i ≠ 0x3C4) : ctrlAttr_ram r i = r i := by
  sym_exec [ctrlAttr_ram]
  revert hi
  bv_decide (config := { enums := false })

theorem impede_keep (side : UInt8) (ram : UInt16 → UInt8) (i : UInt16) (h1 : i ≠ 0x490) (h2 : i ≠ 0x57)
    (h3 : i ≠ 0x785) (h4 : i ≠ 0x86) (h5 : i ≠ 0x6D) (h6 : i ≠ 0) : impedeRam side ram i = ram i := by
  unfold impedeRam
  have e1 : (i == 0x490) = false := beq_false_of_ne h1
  have e2 : (i == 0x57) = false := beq_false_of_ne h2
  have e3 : (i == 0x785) = false := beq_false_of_ne h3
  have e4 : (i == 0x86) = false := beq_false_of_ne h4
  have e5 : (i == 0x6D) = false := beq_false_of_ne h5
  have e6 : (i == 0) = false := beq_false_of_ne h6
  cases impedeInto side ram <;> simp only [e1, e2, e3, e4, e5, e6, cond_false, cond_true]

theorem impede_57 (side : UInt8) (ram : UInt16 → UInt8) : impedeRam side ram 0x57 = 0 ∨ impedeRam side ram 0x57 = ram 0x57 := by
  unfold impedeRam
  have e1 : ((0x57 : UInt16) == 0x490) = false := by decide
  have e2 : ((0x57 : UInt16) == 0x57) = true := by decide
  cases impedeInto side ram <;> simp only [e1, e2, cond_false, cond_true] <;> simp

/-- The impede and the attribute update write only `impAttrWritten`'s cells, where the second region's bounds are open. -/
theorem written_top_all : (List.range 0x10000).all (fun n =>
    !impAttrWritten (UInt16.ofNat n) || topB (gAt PlayerPost.conf.globals (UInt16.ofNat n))) = true := by native_decide

theorem written_top (i : UInt16) (h : impAttrWritten i = true) : gAt PlayerPost.conf.globals i = .top := by
  have h1 := List.all_eq_true.mp written_top_all i.toNat (List.mem_range.mpr i.toNat_lt)
  simp only [UInt16.ofNat_toNat, h, Bool.not_true, Bool.false_or] at h1
  exact eq_top_of_topB h1

/-- The end-of-play exits after `PlayerHole`, as one of those the whole block allows. -/
theorem lift (X : Prop) (F : Nat → Plain → Plain) (A : Plain) (h : X ∨ ∃ k v, v.regs.pc = 0xB1B8 ∧ A = F k v) :
    X ∨ ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88 ∨
      u.regs.pc = 0xB1B8) ∧ A = F k u := by
  rcases h with h | ⟨k, v, hv, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, v, Or.inr (Or.inr (Or.inr (Or.inr hv))), e⟩

theorem code_of_prg {rom : UInt16 → UInt8} {u : Plain} (h : Code rom u) (r : Regs) (ram : UInt16 → UInt8) (c : UInt64)
    (bad : Bool) : Code rom ⟨r, ram, u.prg, c, bad⟩ := fun a ha => h a ha

theorem post_entry_fields : ∀ e ∈ PlayerPost.conf.entries, e.pc = 0xB179 ∧ e.s = 0xF7 ∧
    (∀ v : UInt8, (v &&& 4 == 0) = false → e.p.mem v = true) := by
  have h : PlayerPost.conf.entries.all (fun e => e.pc == 0xB179 && e.s == 0xF7 &&
      (List.range 256).all fun n => (UInt8.ofNat n &&& 4 == 0) || e.p.mem (UInt8.ofNat n)) = true := by native_decide
  intro e he
  have := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at this
  obtain ⟨⟨hpc, hs⟩, hp⟩ := this
  refine ⟨hpc, hs, fun v hv => ?_⟩
  rcases hp v.toNat v.toNat_lt with h1 | h1
  · simp only [UInt8.ofNat_toNat] at h1; rw [h1] at hv; cases hv
  · simpa using h1

/-- The second region's bounds are unconstrained at the cells the impede and the attribute update write, and
contain the collision region's elsewhere. -/
def postWithin : Bool :=
  (List.range 0x800).all fun i => (List.range 256).all fun v =>
    !(gAt Collision.conf.globals (UInt16.ofNat i)).mem (UInt8.ofNat v) ||
      (gAt PlayerPost.conf.globals (UInt16.ofNat i)).mem (UInt8.ofNat v)

theorem postWithin_true : postWithin = true := by native_decide
theorem post_size : PlayerPost.conf.globals.size = 0x800 := by native_decide

theorem post_glob (i : UInt16) (v : UInt8) (hw : impAttrWritten i = true ∨ (gAt Collision.conf.globals i).mem v = true) :
    (gAt PlayerPost.conf.globals i).mem v = true := by
  have hw2 := postWithin_true
  simp only [postWithin] at hw2
  rcases hw with hw | hm
  · rw [written_top i hw]; rfl
  · by_cases hi : i.toNat < 0x800
    · have h1 := List.all_eq_true.mp hw2 i.toNat (List.mem_range.mpr hi)
      have h2 := List.all_eq_true.mp h1 v.toNat (List.mem_range.mpr v.toNat_lt)
      simp only [UInt16.ofNat_toNat, UInt8.ofNat_toNat, hm, Bool.not_true, Bool.false_or] at h2
      exact h2
    · unfold gAt Array.getD
      rw [dif_neg (by rw [post_size]; omega)]
      rfl

theorem post_prot : [0x57, 0x86, 0x6D, 0x400, 0x71A, 0x71B, 0x71C, 0x71D, 0x3A1, 0x785].all
    (fun i : UInt16 => PlayerPost.conf.protFn i) = true := by native_decide

theorem isTopV_eq {v : VS} (h : isTopV v = true) : v = .top := by
  cases v with
  | top => rfl
  | set l => simp [isTopV] at h

theorem cover_parts {g : Global} {b e : Box} {w : UInt16 → Bool} (h : coverAfter g b e w = true) :
    e.a = .top ∧ e.x = .top ∧ e.y = .top ∧
      ∀ c ∈ e.cells, cellCovered g b [] c = true ∧ (w c.1 = false ∨ (zeroed c.1 = true ∧ c.2.mem 0 = true)) := by
  simp only [coverAfter, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨ha, hx⟩, hy⟩, hc⟩ := h
  exact ⟨isTopV_eq ha, isTopV_eq hx, isTopV_eq hy, hc⟩

/-- `XStep` reads only the horizontal bytes of its second state. -/
theorem xstep_congr (ram out out' : UInt16 → UInt8) (h : XStep ram out) (h57 : out' 0x57 = out 0x57)
    (h86 : out' 0x86 = out 0x86) (h6d : out' 0x6D = out 0x6D) (h400 : out' 0x400 = out 0x400)
    (h71a : out' 0x71A = out 0x71A) (h71b : out' 0x71B = out 0x71B) (h71c : out' 0x71C = out 0x71C)
    (h71d : out' 0x71D = out 0x71D) (h3a1 : out' 0x3A1 = out 0x3A1) (h785 : out' 0x785 = out 0x785) :
    XStep ram out' := by
  have hP : pixelP out' = pixelP out := by simp only [pixelP, h86, h6d]
  have hL : leftL out' = leftL out := by simp only [leftL, h71a, h71c]
  have hR : edgeR out' = edgeR out := by simp only [edgeR, h71b, h71d]
  have hphi : phi out' = phi out := by simp only [phi, hP, hL, h400]
  simp only [XStep, hP, hL, hR, hphi, h57, h3a1, h785]
  exact h

theorem post_prot705 : PlayerPost.conf.protFn 0x705 = true := by native_decide

/-- `LStep` reads only the horizontal bytes and `$0705` of its second state. -/
theorem lstep_congr (ram out out' : UInt16 → UInt8) (h : LStep ram out) (h57 : out' 0x57 = out 0x57)
    (h705 : out' 0x705 = out 0x705) (h86 : out' 0x86 = out 0x86) (h6d : out' 0x6D = out 0x6D)
    (h400 : out' 0x400 = out 0x400) (h71a : out' 0x71A = out 0x71A) (h71c : out' 0x71C = out 0x71C) :
    LStep ram out' := by
  have hp : phi out' = phi out := by unfold phi pixelP leftL; rw [h86, h6d, h400, h71a, h71c]
  have hu : upSpeed out' = upSpeed out := by unfold upSpeed; rw [h57, h705]
  obtain ⟨h1, h2⟩ := h
  exact ⟨by rw [hp]; exact h1, by rw [hu]; exact h2⟩

/-- **From `PlayerHole` to the engine.** A state at `$B179` that agrees, away from the cells the code since the
collision region's exit wrote, with a state in one of that region's boxes there, and satisfies `XStep`, runs to
`$AF01` keeping it, or dies in a pit first. -/
theorem post_from (ram : UInt16 → UInt8) {u : Plain} {ram0 : UInt16 → UInt8} (b : Box)
    (hb : Holds Collision.conf.protFn Collision.conf.globals ram0 b u) (e : Box) (he : e ∈ PlayerPost.conf.entries)
    {written : UInt16 → Bool} (hwr : written = attrWritten ∨ written = impAttrWritten)
    (hcov : coverAfter Collision.conf.globals b e written = true) (w : Plain) (hX : XStep ram w.ram)
    (hL : Far ram → LStep ram w.ram)
    (hkeep : ∀ i, written i = false → w.ram i = u.ram i) (hzero : ∀ i, zeroed i = true → w.ram i = 0 ∨ w.ram i = u.ram i)
    (hpc : w.regs.pc = 0xB179) (hs : w.regs.s = 0xF7)
    (hi : (w.regs.p &&& 4 == 0) = false) (hbad : w.bad = false) (hcw : Code (romOf Smb.prg) w) (K : Nat)
    (hr : ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.regs.pc = 0xAF01) :
    (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.ram ∧
      (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.ram) ∧
      ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.bad = false) ∨
      ∃ k v, v.regs.pc = 0xB1B8 ∧ ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2 =
        ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2 := by
  obtain ⟨epc, es, ep⟩ := post_entry_fields e he
  have hsub : ∀ i, written i = true → impAttrWritten i = true := by
    intro i h
    rcases hwr with rfl | rfl
    · simp only [attrWritten, beq_iff_eq] at h; subst h; rfl
    · exact h
  have hglob : ∀ i, (gAt PlayerPost.conf.globals i).mem (w.ram i) = true := by
    intro i
    cases hw : written i with
    | true => exact post_glob i _ (Or.inl (hsub i hw))
    | false => rw [hkeep i hw]; exact post_glob i _ (Or.inr (hb.glob i))
  obtain ⟨ha, hx, hy, hcc⟩ := cover_parts hcov
  have hh : Holds PlayerPost.conf.protFn PlayerPost.conf.globals w.ram e w :=
    holds_after hb ha hx hy hcc hkeep hzero (hpc.trans epc.symm) (hs.trans es.symm) (ep _ hi) (by simpa using hi) hbad hglob
  rcases PlayerSplit.post_plain w hcw e he hh K with hinv | hpit
  · left
    obtain ⟨_, _, hbf⟩ := hinv
    have hp := post_prot
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hp
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := hp
    exact ⟨xstep_congr ram w.ram _ hX (hbf.frame _ q1) (hbf.frame _ q2) (hbf.frame _ q3) (hbf.frame _ q4)
      (hbf.frame _ q5) (hbf.frame _ q6) (hbf.frame _ q7) (hbf.frame _ q8) (hbf.frame _ q9) (hbf.frame _ q10),
      fun hf => lstep_congr ram w.ram _ (hL hf) (hbf.frame _ q1) (hbf.frame _ post_prot705) (hbf.frame _ q2)
        (hbf.frame _ q3) (hbf.frame _ q4) (hbf.frame _ q5) (hbf.frame _ q7), hbf.bad⟩
  · exact Or.inr hpit

set_option maxHeartbeats 8000000 in
/-- **A ground-state frame's player code, from `PlayerCtrlRoutine` to the return into the engine**, keeps the
2.5-pixel limit, unless it ends normal play. -/
theorem block0 (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hcells : ∀ e ∈ conf.entries, ∀ c ∈ e.cells, c.2.mem (bg0 ram c.1) = true)
    (hglob : ∀ i, (gAt conf.globals i).mem (bg0 ram i) = true)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xAF01) :
    (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∧
      (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram) ∧
      ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.bad = false) ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88 ∨ u.regs.pc = 0xB1B8) ∧
        ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  generalize hs0 : (⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩ : Plain) = s0 at hreach ⊢
  generalize ht0 : ((CPU.runTo (σ := Plain) 0xAF01 n).run s0).2 = t at hreach ⊢
  -- More fuel, then movement and scrolling up to `PlayerBGCollision`.
  have hmore := runTo_more 0xAF01 n 1600 s0 (by rw [ht0]; exact hreach)
  rw [ht0] at hmore
  subst hs0
  obtain ⟨j1, p1, c1, heq1, hp1⟩ := ctrlA0_call 0xAF01 stopA' (n + 100) a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  rw [show n + 100 + 1500 = n + 1600 by omega, hmore] at heq1
  have hpc1 : ctrlA0_pc = 45402 := by delta ctrlA0_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨j2, p2, heq2, hp2⟩ := ctrlJ_call 0xAF01 stopJ' (j1 + (n + 100) - 4)
    ctrlA0_a ctrlA0_x ctrlA0_y (ctrlA0_s 0xF7) p1 (ctrlA0_ram 0xF7 ram romFn) romFn c1 ctrlA0_bad rom_ctrlJsrBgCode hp1
  rw [show j1 + (n + 100) - 4 + 4 = j1 + (n + 100) by omega] at heq2
  rw [heq2] at heq1
  have hpc2 : ctrlJ_pc = 0xDC64 := by delta ctrlJ_pc; rfl
  have hsp2 : ctrlJ_s (ctrlA0_s 0xF7) = 0xF5 := by delta ctrlJ_s ctrlA0_s ctrlAux_s ctrlMid_s; rfl
  have hbad2 : ctrlJ_bad ctrlA0_bad = false := by
    delta ctrlJ_bad ctrlA0_bad; simp only [ctrlAux_bad_eq, ctrlMid_bad_eq]
  rw [hpc2, hsp2, hbad2] at heq1
  -- The collision region.
  generalize hs2 : (⟨⟨0xDC64, ctrlJ_a ctrlA0_a, ctrlJ_x ctrlA0_x, ctrlJ_y ctrlA0_y, 0xF5, p2⟩, bg0 ram, romFn,
    ctrlJ_cyc c1, false⟩ : Plain) = s2 at heq1
  have hreach2 : ((CPU.runTo (σ := Plain) 0xAF01 (j2 + (j1 + (n + 100) - 4))).run s2).2.regs.pc = 0xAF01 := by
    rw [← heq1]; exact hreach
  obtain ⟨e, he⟩ : ∃ e, e ∈ conf.entries := by
    have := entry_eq
    cases h : conf.entries with
    | nil => rw [h] at this; cases this
    | cons e _ => exact ⟨e, List.mem_cons_self⟩
  obtain ⟨epc, es, ea, ex, ey, ep⟩ := entry_fields e he
  have hcode2 : Code (romOf Smb.prg) s2 := by subst hs2; exact code_romFn _ _ _ _ _ _ _ _ _
  have hh2 : Holds conf.protFn conf.globals s2.ram e s2 := by
    subst hs2
    exact { pc := epc.symm, sp := es.symm, a := by rw [ea]; rfl, x := by rw [ex]; rfl, y := by rw [ey]; rfl,
            p := ep _ hp2, i := by simpa using hp2, bad := rfl, cells := hcells e he, glob := hglob,
            frame := fun _ _ => rfl }
  obtain ⟨k, u, hex, hcu, hiu, heq3⟩ := collision_through_af01 s2 hcode2 e he hh2 _ hreach2
  rw [heq3] at heq1
  -- The scroll stage's output at the region's entry, and what the region keeps.
  have hC : ScrollOut ram (bg0 ram) :=
    ctrlJ_out (ctrlA0_s 0xF7) ram _ (ctrlA0_out 0xF7 ram romFn hinv ht hs hz hjs)
  have hCL : Far ram → ScrollL ram (bg0 ram) := fun hf =>
    ctrlJ_outL (ctrlA0_s 0xF7) ram _ (ctrlA0_outL 0xF7 ram romFn hinv hf ht hs hz hjs)
  have hk := kept hiu
  have k705 := kept705 hiu
  have hs2ram : s2.ram = bg0 ram := by subst hs2; rfl
  rw [hs2ram] at hk k705
  obtain ⟨k57, k86, k6d, k400, k71a, k71b, k71c, k71d, k3a1, _, _⟩ := hk
  have hreach3 : ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2.regs.pc = 0xAF01 := by rw [← heq1]; exact hreach
  rcases exit_cases _ hex with hu | hu | hu | hu | hu | hu
  · -- `ImpedePlayerMove`, back to `$B15D`, the attribute update, then the second region.
    have hst := impede_stack hiu hu
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu hst
    subst hu
    obtain ⟨b, hbm, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    obtain ⟨epost, hepost, hcov⟩ := facts.2.2.2.2.2.2 b hbm
    have hmore3 := runTo_more 0xAF01 k 40 _ hreach3
    obtain ⟨j5, p5, a5, x5, y5, c5, heq5, hp5⟩ := impede_call 0xAF01 stopImp' k ua ux uy us up uram uprg ucyc false
      (codeAt_of_code hcu _ _ impede_len rom_impedeCode) hI'
    rw [hmore3] at heq5
    rw [heq5] at heq1
    have hr1 : uprg 0x5F8A = 0x60 := (code_low hcu 0x5F8A (by decide)).trans rom_rts1
    have hr2 : uprg 0x5E02 = 0x60 := (code_low hcu 0x5E02 (by decide)).trans rom_rts2
    have hattr : CodeAt uprg 0x315D ctrlAttrCode := codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode
    have hI5 : p5 &&& 4 ≠ 0 := by simpa using hp5
    have hRs (i : UInt16) (hi : i = 0x1F4 ∨ i = 0x1F5 ∨ i = 0x1F6 ∨ i = 0x1F7) : impedeRam (uram 0) uram i = uram i := by
      rcases hi with rfl | rfl | rfl | rfl <;> (unfold impedeRam; cases impedeInto (uram 0) uram <;> rfl)
    have hX : XStep ram (ctrlAttr_ram (impedeRam (uram 0) uram)) :=
      attr_step ram _ (finish_stage ram (bg0 ram) _ hC (bgX_of_kept (bg0 ram) uram _ k400 k86 k6d k57 (impede_bgX uram))
        ((impede_keeps _ _ _ (by simp)).trans k71a) ((impede_keeps _ _ _ (by simp)).trans k71b)
        ((impede_keeps _ _ _ (by simp)).trans k71c) ((impede_keeps _ _ _ (by simp)).trans k71d)
        ((impede_keeps _ _ _ (by simp)).trans k3a1))
    have hL : Far ram → LStep ram (ctrlAttr_ram (impedeRam (uram 0) uram)) := fun hf =>
      attr_stepL ram _ (finish_stageL ram (bg0 ram) _ hC (hCL hf) (upSpeed_bound hinv)
        (bgX_of_kept (bg0 ram) uram _ k400 k86 k6d k57 (impede_bgX uram))
        ((impede_keeps _ _ _ (by simp)).trans k71a) ((impede_keeps _ _ _ (by simp)).trans k71b)
        ((impede_keeps _ _ _ (by simp)).trans k71c) ((impede_keeps _ _ _ (by simp)).trans k71d)
        ((impede_keeps _ _ _ (by simp)).trans k3a1)
        ((impede_keep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans k705))
    have hkeepW (i : UInt16) (hw : impAttrWritten i = false) :
        ctrlAttr_ram (impedeRam (uram 0) uram) i = uram i := by
      simp only [impAttrWritten, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hw
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hw
      rw [attr_keep _ _ h1]
      exact impede_keep _ _ _ h2 h3 h4 h5 h6 h7
    have hzeroW (i : UInt16) (hz : zeroed i = true) :
        ctrlAttr_ram (impedeRam (uram 0) uram) i = 0 ∨ ctrlAttr_ram (impedeRam (uram 0) uram) i = uram i := by
      simp only [zeroed, beq_iff_eq] at hz
      subst hz
      rw [attr_keep _ _ (by decide)]
      exact impede_57 _ _
    have hreach5 : ((CPU.runTo (σ := Plain) 0xAF01 (j5 + k)).run
        ⟨⟨0xDF8A, a5, x5, y5, us, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩).2.regs.pc = 0xAF01 := by
      rw [← heq1]; exact hreach
    have hstep (K : Nat) (w : Plain) (hw : w.regs.pc ≠ 0xAF01)
        (h : ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.regs.pc = 0xAF01) :
        ∃ K', K = K' + 1 ∧ ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 K').run (CPU.step.run w).2).2 := by
      cases K with
      | zero => rw [runTo_zero] at h; exact absurd h hw
      | succ K' => exact ⟨K', rfl, runTo_succ _ _ _ hw⟩
    obtain ⟨K, _, hK⟩ := hstep _ _ (by simp) hreach5
    rw [hK] at heq1 hreach5
    have hfin (K : Nat) (w : Plain) (hwpc : w.regs.pc = 0xB15D) (hws : w.ram = impedeRam (uram 0) uram)
        (hwprg : w.prg = uprg) (hwbad : w.bad = false) (hwp : (w.regs.p &&& 4 == 0) = false) (hwsp : w.regs.s = 0xF7)
        (hr : ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.regs.pc = 0xAF01) :
        (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.ram ∧
          (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.ram) ∧
          ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.bad = false) ∨
          ∃ k v, v.regs.pc = 0xB1B8 ∧ ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2 =
            ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2 := by
      obtain ⟨⟨wpc, wa, wx, wy, ws, wp⟩, wram, wprg, wcyc, wbad⟩ := w
      simp only at hwpc hws hwprg hwbad hwp hwsp
      subst wpc wram wprg wbad ws
      have hmore6 := runTo_more 0xAF01 K 20 _ hr
      obtain ⟨j6, p6, heq6, hp6⟩ := ctrlAttr_call 0xAF01 stopAttr' K wa wx wy 0xF7 wp _ uprg wcyc false hattr hwp
      rw [hmore6] at heq6
      have hpc6 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
      have hsp6 : ctrlAttr_s 0xF7 = 0xF7 := by delta ctrlAttr_s; rfl
      rw [hpc6, hsp6, ctrlAttr_bad_eq] at heq6
      rw [heq6] at hr ⊢
      refine post_from ram b hb epost hepost (Or.inr rfl) hcov _ hX ?_ hkeepW hzeroW rfl rfl hp6 rfl (code_of_prg hcu _ _ _ _) _ hr
      exact hL
    rcases hst.2.2 with hsF5 | ⟨hsF3, h4, h5⟩
    · subst hsF5
      have h1 := rts_foot a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h1
      obtain ⟨e1, e2, e3, _, _, _, e7, e8, e9⟩ := h1
      rw [heq1]
      exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ (hfin K _ e1 e7 e8 e9 (by rw [e3]; exact hp5) e2 hreach5)
    · subst hsF3
      have h1 := rts_side1 a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans h4) ((hRs _ (by simp)).trans h5) hI5
      rw [runTo_one 0xDE02 _ (by simp)] at h1
      generalize hw1 : (CPU.step.run (⟨⟨0xDF8A, a5, x5, y5, 0xF3, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩ : Plain)).2 = w1 at h1 hreach5 heq1
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h1
      obtain ⟨K2, _, hK2⟩ := hstep _ _ (by rw [f1]; simp) hreach5
      rw [hK2] at hreach5 heq1
      obtain ⟨⟨w1pc, w1a, w1x, w1y, w1s, w1p⟩, w1ram, w1prg, w1cyc, w1bad⟩ := w1
      simp only at f1 f2 f3 f4 f5 f6 f7 f8 f9
      subst w1pc w1s w1p w1a w1x w1y w1ram w1prg w1bad
      have h2 := rts_side2 a5 x5 y5 p5 _ uprg w1cyc hr2 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h2
      obtain ⟨e1, e2, e3, _, _, _, e7, e8, e9⟩ := h2
      rw [heq1]
      exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ (hfin K2 _ e1 e7 e8 e9 (by rw [e3]; exact hp5) e2 hreach5)
  · -- Back at `$B15D`: the attribute update, then the second region.
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu
    subst hu
    obtain ⟨b, hbm, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    obtain ⟨hbs, epost, hepost, hcov⟩ := facts.2.2.2.2.2.1 b hbm
    have hsp : us = 0xF7 := hb.sp.trans hbs
    subst hsp
    have hmore3 := runTo_more 0xAF01 k 20 _ hreach3
    obtain ⟨j4, p4, heq4, hp4⟩ := ctrlAttr_call 0xAF01 stopAttr' k ua ux uy 0xF7 up uram uprg
      ucyc false (codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode) hI'
    rw [hmore3] at heq4
    have hpc4 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
    have hsp4 : ctrlAttr_s 0xF7 = 0xF7 := by delta ctrlAttr_s; rfl
    rw [hpc4, hsp4, ctrlAttr_bad_eq] at heq4
    rw [heq4] at heq1
    have hX : XStep ram (ctrlAttr_ram uram) :=
      attr_step ram uram (finish_stage ram (bg0 ram) uram hC (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1)
    have hL : Far ram → LStep ram (ctrlAttr_ram uram) := fun hf =>
      attr_stepL ram uram (finish_stageL ram (bg0 ram) uram hC (hCL hf) (upSpeed_bound hinv)
        (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1 k705)
    have hkeepW (i : UInt16) (hw : attrWritten i = false) : ctrlAttr_ram uram i = uram i := by
      simp only [attrWritten, beq_eq_false_iff_ne, ne_eq] at hw
      exact attr_keep _ _ hw
    have hzeroW (i : UInt16) (hz : zeroed i = true) : ctrlAttr_ram uram i = 0 ∨ ctrlAttr_ram uram i = uram i := by
      simp only [zeroed, beq_iff_eq] at hz
      subst hz
      exact Or.inr (attr_keep _ _ (by decide))
    have hr : ((CPU.runTo (σ := Plain) 0xAF01 (j4 + k)).run
        ⟨⟨0xB179, ctrlAttr_a uram, ctrlAttr_x ux, ctrlAttr_y uy, 0xF7, p4⟩, ctrlAttr_ram uram, uprg,
          ctrlAttr_cyc uram ucyc, false⟩).2.regs.pc = 0xAF01 := by rw [← heq1]; exact hreach
    rw [heq1]
    have hpf := post_from ram b hb epost hepost (Or.inl rfl) hcov _ hX ?_ hkeepW hzeroW rfl rfl hp4 rfl (code_of_prg hcu _ _ _ _) _ hr
    · exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ hpf
    · exact hL
  · exact Or.inr ⟨k, u, Or.inl hu, heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inl hu), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inl hu)), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inr (Or.inl hu))), heq1⟩

set_option maxHeartbeats 8000000 in
/-- **The same for a jumping frame** (`$1D` = 1). -/
theorem block1 (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hcells : ∀ e ∈ conf.entries, ∀ c ∈ e.cells, c.2.mem (bg1 ram c.1) = true)
    (hglob : ∀ i, (gAt conf.globals i).mem (bg1 ram i) = true)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xAF01) :
    (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∧
      (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram) ∧
      ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.bad = false) ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88 ∨ u.regs.pc = 0xB1B8) ∧
        ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  generalize hs0 : (⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩ : Plain) = s0 at hreach ⊢
  generalize ht0 : ((CPU.runTo (σ := Plain) 0xAF01 n).run s0).2 = t at hreach ⊢
  -- More fuel, then movement and scrolling up to `PlayerBGCollision`.
  have hmore := runTo_more 0xAF01 n 1600 s0 (by rw [ht0]; exact hreach)
  rw [ht0] at hmore
  subst hs0
  obtain ⟨j1, p1, c1, heq1, hp1⟩ := ctrlA1_call 0xAF01 stopA' (n + 100) a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  rw [show n + 100 + 1500 = n + 1600 by omega, hmore] at heq1
  have hpc1 : ctrlA1_pc = 45402 := by delta ctrlA1_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨j2, p2, heq2, hp2⟩ := ctrlJ_call 0xAF01 stopJ' (j1 + (n + 100) - 4)
    ctrlA1_a ctrlA1_x ctrlA1_y (ctrlA1_s 0xF7) p1 (ctrlA1_ram 0xF7 ram romFn) romFn c1 ctrlA1_bad rom_ctrlJsrBgCode hp1
  rw [show j1 + (n + 100) - 4 + 4 = j1 + (n + 100) by omega] at heq2
  rw [heq2] at heq1
  have hpc2 : ctrlJ_pc = 0xDC64 := by delta ctrlJ_pc; rfl
  have hsp2 : ctrlJ_s (ctrlA1_s 0xF7) = 0xF5 := by delta ctrlJ_s ctrlA1_s ctrlAux_s ctrlMid_s; rfl
  have hbad2 : ctrlJ_bad ctrlA1_bad = false := by
    delta ctrlJ_bad ctrlA1_bad; simp only [ctrlAux_bad_eq, ctrlMid_bad_eq]
  rw [hpc2, hsp2, hbad2] at heq1
  -- The collision region.
  generalize hs2 : (⟨⟨0xDC64, ctrlJ_a ctrlA1_a, ctrlJ_x ctrlA1_x, ctrlJ_y ctrlA1_y, 0xF5, p2⟩, bg1 ram, romFn,
    ctrlJ_cyc c1, false⟩ : Plain) = s2 at heq1
  have hreach2 : ((CPU.runTo (σ := Plain) 0xAF01 (j2 + (j1 + (n + 100) - 4))).run s2).2.regs.pc = 0xAF01 := by
    rw [← heq1]; exact hreach
  obtain ⟨e, he⟩ : ∃ e, e ∈ conf.entries := by
    have := entry_eq
    cases h : conf.entries with
    | nil => rw [h] at this; cases this
    | cons e _ => exact ⟨e, List.mem_cons_self⟩
  obtain ⟨epc, es, ea, ex, ey, ep⟩ := entry_fields e he
  have hcode2 : Code (romOf Smb.prg) s2 := by subst hs2; exact code_romFn _ _ _ _ _ _ _ _ _
  have hh2 : Holds conf.protFn conf.globals s2.ram e s2 := by
    subst hs2
    exact { pc := epc.symm, sp := es.symm, a := by rw [ea]; rfl, x := by rw [ex]; rfl, y := by rw [ey]; rfl,
            p := ep _ hp2, i := by simpa using hp2, bad := rfl, cells := hcells e he, glob := hglob,
            frame := fun _ _ => rfl }
  obtain ⟨k, u, hex, hcu, hiu, heq3⟩ := collision_through_af01 s2 hcode2 e he hh2 _ hreach2
  rw [heq3] at heq1
  -- The scroll stage's output at the region's entry, and what the region keeps.
  have hC : ScrollOut ram (bg1 ram) :=
    ctrlJ_out (ctrlA1_s 0xF7) ram _ (ctrlA1_out 0xF7 ram romFn hinv ht hs hz hjs)
  have hCL : Far ram → ScrollL ram (bg1 ram) := fun hf =>
    ctrlJ_outL (ctrlA1_s 0xF7) ram _ (ctrlA1_outL 0xF7 ram romFn hinv hf ht hs hz hjs)
  have hk := kept hiu
  have k705 := kept705 hiu
  have hs2ram : s2.ram = bg1 ram := by subst hs2; rfl
  rw [hs2ram] at hk k705
  obtain ⟨k57, k86, k6d, k400, k71a, k71b, k71c, k71d, k3a1, _, _⟩ := hk
  have hreach3 : ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2.regs.pc = 0xAF01 := by rw [← heq1]; exact hreach
  rcases exit_cases _ hex with hu | hu | hu | hu | hu | hu
  · -- `ImpedePlayerMove`, back to `$B15D`, the attribute update, then the second region.
    have hst := impede_stack hiu hu
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu hst
    subst hu
    obtain ⟨b, hbm, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    obtain ⟨epost, hepost, hcov⟩ := facts.2.2.2.2.2.2 b hbm
    have hmore3 := runTo_more 0xAF01 k 40 _ hreach3
    obtain ⟨j5, p5, a5, x5, y5, c5, heq5, hp5⟩ := impede_call 0xAF01 stopImp' k ua ux uy us up uram uprg ucyc false
      (codeAt_of_code hcu _ _ impede_len rom_impedeCode) hI'
    rw [hmore3] at heq5
    rw [heq5] at heq1
    have hr1 : uprg 0x5F8A = 0x60 := (code_low hcu 0x5F8A (by decide)).trans rom_rts1
    have hr2 : uprg 0x5E02 = 0x60 := (code_low hcu 0x5E02 (by decide)).trans rom_rts2
    have hattr : CodeAt uprg 0x315D ctrlAttrCode := codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode
    have hI5 : p5 &&& 4 ≠ 0 := by simpa using hp5
    have hRs (i : UInt16) (hi : i = 0x1F4 ∨ i = 0x1F5 ∨ i = 0x1F6 ∨ i = 0x1F7) : impedeRam (uram 0) uram i = uram i := by
      rcases hi with rfl | rfl | rfl | rfl <;> (unfold impedeRam; cases impedeInto (uram 0) uram <;> rfl)
    have hX : XStep ram (ctrlAttr_ram (impedeRam (uram 0) uram)) :=
      attr_step ram _ (finish_stage ram (bg1 ram) _ hC (bgX_of_kept (bg1 ram) uram _ k400 k86 k6d k57 (impede_bgX uram))
        ((impede_keeps _ _ _ (by simp)).trans k71a) ((impede_keeps _ _ _ (by simp)).trans k71b)
        ((impede_keeps _ _ _ (by simp)).trans k71c) ((impede_keeps _ _ _ (by simp)).trans k71d)
        ((impede_keeps _ _ _ (by simp)).trans k3a1))
    have hL : Far ram → LStep ram (ctrlAttr_ram (impedeRam (uram 0) uram)) := fun hf =>
      attr_stepL ram _ (finish_stageL ram (bg1 ram) _ hC (hCL hf) (upSpeed_bound hinv)
        (bgX_of_kept (bg1 ram) uram _ k400 k86 k6d k57 (impede_bgX uram))
        ((impede_keeps _ _ _ (by simp)).trans k71a) ((impede_keeps _ _ _ (by simp)).trans k71b)
        ((impede_keeps _ _ _ (by simp)).trans k71c) ((impede_keeps _ _ _ (by simp)).trans k71d)
        ((impede_keeps _ _ _ (by simp)).trans k3a1)
        ((impede_keep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans k705))
    have hkeepW (i : UInt16) (hw : impAttrWritten i = false) :
        ctrlAttr_ram (impedeRam (uram 0) uram) i = uram i := by
      simp only [impAttrWritten, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hw
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hw
      rw [attr_keep _ _ h1]
      exact impede_keep _ _ _ h2 h3 h4 h5 h6 h7
    have hzeroW (i : UInt16) (hz : zeroed i = true) :
        ctrlAttr_ram (impedeRam (uram 0) uram) i = 0 ∨ ctrlAttr_ram (impedeRam (uram 0) uram) i = uram i := by
      simp only [zeroed, beq_iff_eq] at hz
      subst hz
      rw [attr_keep _ _ (by decide)]
      exact impede_57 _ _
    have hreach5 : ((CPU.runTo (σ := Plain) 0xAF01 (j5 + k)).run
        ⟨⟨0xDF8A, a5, x5, y5, us, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩).2.regs.pc = 0xAF01 := by
      rw [← heq1]; exact hreach
    have hstep (K : Nat) (w : Plain) (hw : w.regs.pc ≠ 0xAF01)
        (h : ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.regs.pc = 0xAF01) :
        ∃ K', K = K' + 1 ∧ ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 K').run (CPU.step.run w).2).2 := by
      cases K with
      | zero => rw [runTo_zero] at h; exact absurd h hw
      | succ K' => exact ⟨K', rfl, runTo_succ _ _ _ hw⟩
    obtain ⟨K, _, hK⟩ := hstep _ _ (by simp) hreach5
    rw [hK] at heq1 hreach5
    have hfin (K : Nat) (w : Plain) (hwpc : w.regs.pc = 0xB15D) (hws : w.ram = impedeRam (uram 0) uram)
        (hwprg : w.prg = uprg) (hwbad : w.bad = false) (hwp : (w.regs.p &&& 4 == 0) = false) (hwsp : w.regs.s = 0xF7)
        (hr : ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.regs.pc = 0xAF01) :
        (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.ram ∧
          (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.ram) ∧
          ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.bad = false) ∨
          ∃ k v, v.regs.pc = 0xB1B8 ∧ ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2 =
            ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2 := by
      obtain ⟨⟨wpc, wa, wx, wy, ws, wp⟩, wram, wprg, wcyc, wbad⟩ := w
      simp only at hwpc hws hwprg hwbad hwp hwsp
      subst wpc wram wprg wbad ws
      have hmore6 := runTo_more 0xAF01 K 20 _ hr
      obtain ⟨j6, p6, heq6, hp6⟩ := ctrlAttr_call 0xAF01 stopAttr' K wa wx wy 0xF7 wp _ uprg wcyc false hattr hwp
      rw [hmore6] at heq6
      have hpc6 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
      have hsp6 : ctrlAttr_s 0xF7 = 0xF7 := by delta ctrlAttr_s; rfl
      rw [hpc6, hsp6, ctrlAttr_bad_eq] at heq6
      rw [heq6] at hr ⊢
      refine post_from ram b hb epost hepost (Or.inr rfl) hcov _ hX ?_ hkeepW hzeroW rfl rfl hp6 rfl (code_of_prg hcu _ _ _ _) _ hr
      exact hL
    rcases hst.2.2 with hsF5 | ⟨hsF3, h4, h5⟩
    · subst hsF5
      have h1 := rts_foot a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h1
      obtain ⟨e1, e2, e3, _, _, _, e7, e8, e9⟩ := h1
      rw [heq1]
      exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ (hfin K _ e1 e7 e8 e9 (by rw [e3]; exact hp5) e2 hreach5)
    · subst hsF3
      have h1 := rts_side1 a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans h4) ((hRs _ (by simp)).trans h5) hI5
      rw [runTo_one 0xDE02 _ (by simp)] at h1
      generalize hw1 : (CPU.step.run (⟨⟨0xDF8A, a5, x5, y5, 0xF3, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩ : Plain)).2 = w1 at h1 hreach5 heq1
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h1
      obtain ⟨K2, _, hK2⟩ := hstep _ _ (by rw [f1]; simp) hreach5
      rw [hK2] at hreach5 heq1
      obtain ⟨⟨w1pc, w1a, w1x, w1y, w1s, w1p⟩, w1ram, w1prg, w1cyc, w1bad⟩ := w1
      simp only at f1 f2 f3 f4 f5 f6 f7 f8 f9
      subst w1pc w1s w1p w1a w1x w1y w1ram w1prg w1bad
      have h2 := rts_side2 a5 x5 y5 p5 _ uprg w1cyc hr2 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h2
      obtain ⟨e1, e2, e3, _, _, _, e7, e8, e9⟩ := h2
      rw [heq1]
      exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ (hfin K2 _ e1 e7 e8 e9 (by rw [e3]; exact hp5) e2 hreach5)
  · -- Back at `$B15D`: the attribute update, then the second region.
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu
    subst hu
    obtain ⟨b, hbm, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    obtain ⟨hbs, epost, hepost, hcov⟩ := facts.2.2.2.2.2.1 b hbm
    have hsp : us = 0xF7 := hb.sp.trans hbs
    subst hsp
    have hmore3 := runTo_more 0xAF01 k 20 _ hreach3
    obtain ⟨j4, p4, heq4, hp4⟩ := ctrlAttr_call 0xAF01 stopAttr' k ua ux uy 0xF7 up uram uprg
      ucyc false (codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode) hI'
    rw [hmore3] at heq4
    have hpc4 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
    have hsp4 : ctrlAttr_s 0xF7 = 0xF7 := by delta ctrlAttr_s; rfl
    rw [hpc4, hsp4, ctrlAttr_bad_eq] at heq4
    rw [heq4] at heq1
    have hX : XStep ram (ctrlAttr_ram uram) :=
      attr_step ram uram (finish_stage ram (bg1 ram) uram hC (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1)
    have hL : Far ram → LStep ram (ctrlAttr_ram uram) := fun hf =>
      attr_stepL ram uram (finish_stageL ram (bg1 ram) uram hC (hCL hf) (upSpeed_bound hinv)
        (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1 k705)
    have hkeepW (i : UInt16) (hw : attrWritten i = false) : ctrlAttr_ram uram i = uram i := by
      simp only [attrWritten, beq_eq_false_iff_ne, ne_eq] at hw
      exact attr_keep _ _ hw
    have hzeroW (i : UInt16) (hz : zeroed i = true) : ctrlAttr_ram uram i = 0 ∨ ctrlAttr_ram uram i = uram i := by
      simp only [zeroed, beq_iff_eq] at hz
      subst hz
      exact Or.inr (attr_keep _ _ (by decide))
    have hr : ((CPU.runTo (σ := Plain) 0xAF01 (j4 + k)).run
        ⟨⟨0xB179, ctrlAttr_a uram, ctrlAttr_x ux, ctrlAttr_y uy, 0xF7, p4⟩, ctrlAttr_ram uram, uprg,
          ctrlAttr_cyc uram ucyc, false⟩).2.regs.pc = 0xAF01 := by rw [← heq1]; exact hreach
    rw [heq1]
    have hpf := post_from ram b hb epost hepost (Or.inl rfl) hcov _ hX ?_ hkeepW hzeroW rfl rfl hp4 rfl (code_of_prg hcu _ _ _ _) _ hr
    · exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ hpf
    · exact hL
  · exact Or.inr ⟨k, u, Or.inl hu, heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inl hu), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inl hu)), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inr (Or.inl hu))), heq1⟩

set_option maxHeartbeats 8000000 in
/-- **The same for a falling frame** (`$1D` = 2). -/
theorem block2 (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hcells : ∀ e ∈ conf.entries, ∀ c ∈ e.cells, c.2.mem (bg2 ram c.1) = true)
    (hglob : ∀ i, (gAt conf.globals i).mem (bg2 ram i) = true)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xAF01) :
    (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∧
      (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram) ∧
      ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.bad = false) ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88 ∨ u.regs.pc = 0xB1B8) ∧
        ((CPU.runTo (σ := Plain) 0xAF01 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  generalize hs0 : (⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩ : Plain) = s0 at hreach ⊢
  generalize ht0 : ((CPU.runTo (σ := Plain) 0xAF01 n).run s0).2 = t at hreach ⊢
  -- More fuel, then movement and scrolling up to `PlayerBGCollision`.
  have hmore := runTo_more 0xAF01 n 1600 s0 (by rw [ht0]; exact hreach)
  rw [ht0] at hmore
  subst hs0
  obtain ⟨j1, p1, c1, heq1, hp1⟩ := ctrlA2_call 0xAF01 stopA' (n + 100) a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  rw [show n + 100 + 1500 = n + 1600 by omega, hmore] at heq1
  have hpc1 : ctrlA2_pc = 45402 := by delta ctrlA2_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨j2, p2, heq2, hp2⟩ := ctrlJ_call 0xAF01 stopJ' (j1 + (n + 100) - 4)
    ctrlA2_a ctrlA2_x ctrlA2_y (ctrlA2_s 0xF7) p1 (ctrlA2_ram 0xF7 ram romFn) romFn c1 ctrlA2_bad rom_ctrlJsrBgCode hp1
  rw [show j1 + (n + 100) - 4 + 4 = j1 + (n + 100) by omega] at heq2
  rw [heq2] at heq1
  have hpc2 : ctrlJ_pc = 0xDC64 := by delta ctrlJ_pc; rfl
  have hsp2 : ctrlJ_s (ctrlA2_s 0xF7) = 0xF5 := by delta ctrlJ_s ctrlA2_s ctrlAux_s ctrlMid_s; rfl
  have hbad2 : ctrlJ_bad ctrlA2_bad = false := by
    delta ctrlJ_bad ctrlA2_bad; simp only [ctrlAux_bad_eq, ctrlMid_bad_eq]
  rw [hpc2, hsp2, hbad2] at heq1
  -- The collision region.
  generalize hs2 : (⟨⟨0xDC64, ctrlJ_a ctrlA2_a, ctrlJ_x ctrlA2_x, ctrlJ_y ctrlA2_y, 0xF5, p2⟩, bg2 ram, romFn,
    ctrlJ_cyc c1, false⟩ : Plain) = s2 at heq1
  have hreach2 : ((CPU.runTo (σ := Plain) 0xAF01 (j2 + (j1 + (n + 100) - 4))).run s2).2.regs.pc = 0xAF01 := by
    rw [← heq1]; exact hreach
  obtain ⟨e, he⟩ : ∃ e, e ∈ conf.entries := by
    have := entry_eq
    cases h : conf.entries with
    | nil => rw [h] at this; cases this
    | cons e _ => exact ⟨e, List.mem_cons_self⟩
  obtain ⟨epc, es, ea, ex, ey, ep⟩ := entry_fields e he
  have hcode2 : Code (romOf Smb.prg) s2 := by subst hs2; exact code_romFn _ _ _ _ _ _ _ _ _
  have hh2 : Holds conf.protFn conf.globals s2.ram e s2 := by
    subst hs2
    exact { pc := epc.symm, sp := es.symm, a := by rw [ea]; rfl, x := by rw [ex]; rfl, y := by rw [ey]; rfl,
            p := ep _ hp2, i := by simpa using hp2, bad := rfl, cells := hcells e he, glob := hglob,
            frame := fun _ _ => rfl }
  obtain ⟨k, u, hex, hcu, hiu, heq3⟩ := collision_through_af01 s2 hcode2 e he hh2 _ hreach2
  rw [heq3] at heq1
  -- The scroll stage's output at the region's entry, and what the region keeps.
  have hC : ScrollOut ram (bg2 ram) :=
    ctrlJ_out (ctrlA2_s 0xF7) ram _ (ctrlA2_out 0xF7 ram romFn hinv ht hs hz hjs)
  have hCL : Far ram → ScrollL ram (bg2 ram) := fun hf =>
    ctrlJ_outL (ctrlA2_s 0xF7) ram _ (ctrlA2_outL 0xF7 ram romFn hinv hf ht hs hz hjs)
  have hk := kept hiu
  have k705 := kept705 hiu
  have hs2ram : s2.ram = bg2 ram := by subst hs2; rfl
  rw [hs2ram] at hk k705
  obtain ⟨k57, k86, k6d, k400, k71a, k71b, k71c, k71d, k3a1, _, _⟩ := hk
  have hreach3 : ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2.regs.pc = 0xAF01 := by rw [← heq1]; exact hreach
  rcases exit_cases _ hex with hu | hu | hu | hu | hu | hu
  · -- `ImpedePlayerMove`, back to `$B15D`, the attribute update, then the second region.
    have hst := impede_stack hiu hu
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu hst
    subst hu
    obtain ⟨b, hbm, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    obtain ⟨epost, hepost, hcov⟩ := facts.2.2.2.2.2.2 b hbm
    have hmore3 := runTo_more 0xAF01 k 40 _ hreach3
    obtain ⟨j5, p5, a5, x5, y5, c5, heq5, hp5⟩ := impede_call 0xAF01 stopImp' k ua ux uy us up uram uprg ucyc false
      (codeAt_of_code hcu _ _ impede_len rom_impedeCode) hI'
    rw [hmore3] at heq5
    rw [heq5] at heq1
    have hr1 : uprg 0x5F8A = 0x60 := (code_low hcu 0x5F8A (by decide)).trans rom_rts1
    have hr2 : uprg 0x5E02 = 0x60 := (code_low hcu 0x5E02 (by decide)).trans rom_rts2
    have hattr : CodeAt uprg 0x315D ctrlAttrCode := codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode
    have hI5 : p5 &&& 4 ≠ 0 := by simpa using hp5
    have hRs (i : UInt16) (hi : i = 0x1F4 ∨ i = 0x1F5 ∨ i = 0x1F6 ∨ i = 0x1F7) : impedeRam (uram 0) uram i = uram i := by
      rcases hi with rfl | rfl | rfl | rfl <;> (unfold impedeRam; cases impedeInto (uram 0) uram <;> rfl)
    have hX : XStep ram (ctrlAttr_ram (impedeRam (uram 0) uram)) :=
      attr_step ram _ (finish_stage ram (bg2 ram) _ hC (bgX_of_kept (bg2 ram) uram _ k400 k86 k6d k57 (impede_bgX uram))
        ((impede_keeps _ _ _ (by simp)).trans k71a) ((impede_keeps _ _ _ (by simp)).trans k71b)
        ((impede_keeps _ _ _ (by simp)).trans k71c) ((impede_keeps _ _ _ (by simp)).trans k71d)
        ((impede_keeps _ _ _ (by simp)).trans k3a1))
    have hL : Far ram → LStep ram (ctrlAttr_ram (impedeRam (uram 0) uram)) := fun hf =>
      attr_stepL ram _ (finish_stageL ram (bg2 ram) _ hC (hCL hf) (upSpeed_bound hinv)
        (bgX_of_kept (bg2 ram) uram _ k400 k86 k6d k57 (impede_bgX uram))
        ((impede_keeps _ _ _ (by simp)).trans k71a) ((impede_keeps _ _ _ (by simp)).trans k71b)
        ((impede_keeps _ _ _ (by simp)).trans k71c) ((impede_keeps _ _ _ (by simp)).trans k71d)
        ((impede_keeps _ _ _ (by simp)).trans k3a1)
        ((impede_keep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans k705))
    have hkeepW (i : UInt16) (hw : impAttrWritten i = false) :
        ctrlAttr_ram (impedeRam (uram 0) uram) i = uram i := by
      simp only [impAttrWritten, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hw
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hw
      rw [attr_keep _ _ h1]
      exact impede_keep _ _ _ h2 h3 h4 h5 h6 h7
    have hzeroW (i : UInt16) (hz : zeroed i = true) :
        ctrlAttr_ram (impedeRam (uram 0) uram) i = 0 ∨ ctrlAttr_ram (impedeRam (uram 0) uram) i = uram i := by
      simp only [zeroed, beq_iff_eq] at hz
      subst hz
      rw [attr_keep _ _ (by decide)]
      exact impede_57 _ _
    have hreach5 : ((CPU.runTo (σ := Plain) 0xAF01 (j5 + k)).run
        ⟨⟨0xDF8A, a5, x5, y5, us, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩).2.regs.pc = 0xAF01 := by
      rw [← heq1]; exact hreach
    have hstep (K : Nat) (w : Plain) (hw : w.regs.pc ≠ 0xAF01)
        (h : ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.regs.pc = 0xAF01) :
        ∃ K', K = K' + 1 ∧ ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2 =
          ((CPU.runTo (σ := Plain) 0xAF01 K').run (CPU.step.run w).2).2 := by
      cases K with
      | zero => rw [runTo_zero] at h; exact absurd h hw
      | succ K' => exact ⟨K', rfl, runTo_succ _ _ _ hw⟩
    obtain ⟨K, _, hK⟩ := hstep _ _ (by simp) hreach5
    rw [hK] at heq1 hreach5
    have hfin (K : Nat) (w : Plain) (hwpc : w.regs.pc = 0xB15D) (hws : w.ram = impedeRam (uram 0) uram)
        (hwprg : w.prg = uprg) (hwbad : w.bad = false) (hwp : (w.regs.p &&& 4 == 0) = false) (hwsp : w.regs.s = 0xF7)
        (hr : ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.regs.pc = 0xAF01) :
        (XStep ram ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.ram ∧
          (Far ram → LStep ram ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.ram) ∧
          ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2.bad = false) ∨
          ∃ k v, v.regs.pc = 0xB1B8 ∧ ((CPU.runTo (σ := Plain) 0xAF01 K).run w).2 =
            ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2 := by
      obtain ⟨⟨wpc, wa, wx, wy, ws, wp⟩, wram, wprg, wcyc, wbad⟩ := w
      simp only at hwpc hws hwprg hwbad hwp hwsp
      subst wpc wram wprg wbad ws
      have hmore6 := runTo_more 0xAF01 K 20 _ hr
      obtain ⟨j6, p6, heq6, hp6⟩ := ctrlAttr_call 0xAF01 stopAttr' K wa wx wy 0xF7 wp _ uprg wcyc false hattr hwp
      rw [hmore6] at heq6
      have hpc6 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
      have hsp6 : ctrlAttr_s 0xF7 = 0xF7 := by delta ctrlAttr_s; rfl
      rw [hpc6, hsp6, ctrlAttr_bad_eq] at heq6
      rw [heq6] at hr ⊢
      refine post_from ram b hb epost hepost (Or.inr rfl) hcov _ hX ?_ hkeepW hzeroW rfl rfl hp6 rfl (code_of_prg hcu _ _ _ _) _ hr
      exact hL
    rcases hst.2.2 with hsF5 | ⟨hsF3, h4, h5⟩
    · subst hsF5
      have h1 := rts_foot a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h1
      obtain ⟨e1, e2, e3, _, _, _, e7, e8, e9⟩ := h1
      rw [heq1]
      exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ (hfin K _ e1 e7 e8 e9 (by rw [e3]; exact hp5) e2 hreach5)
    · subst hsF3
      have h1 := rts_side1 a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans h4) ((hRs _ (by simp)).trans h5) hI5
      rw [runTo_one 0xDE02 _ (by simp)] at h1
      generalize hw1 : (CPU.step.run (⟨⟨0xDF8A, a5, x5, y5, 0xF3, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩ : Plain)).2 = w1 at h1 hreach5 heq1
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h1
      obtain ⟨K2, _, hK2⟩ := hstep _ _ (by rw [f1]; simp) hreach5
      rw [hK2] at hreach5 heq1
      obtain ⟨⟨w1pc, w1a, w1x, w1y, w1s, w1p⟩, w1ram, w1prg, w1cyc, w1bad⟩ := w1
      simp only at f1 f2 f3 f4 f5 f6 f7 f8 f9
      subst w1pc w1s w1p w1a w1x w1y w1ram w1prg w1bad
      have h2 := rts_side2 a5 x5 y5 p5 _ uprg w1cyc hr2 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h2
      obtain ⟨e1, e2, e3, _, _, _, e7, e8, e9⟩ := h2
      rw [heq1]
      exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ (hfin K2 _ e1 e7 e8 e9 (by rw [e3]; exact hp5) e2 hreach5)
  · -- Back at `$B15D`: the attribute update, then the second region.
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu
    subst hu
    obtain ⟨b, hbm, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    obtain ⟨hbs, epost, hepost, hcov⟩ := facts.2.2.2.2.2.1 b hbm
    have hsp : us = 0xF7 := hb.sp.trans hbs
    subst hsp
    have hmore3 := runTo_more 0xAF01 k 20 _ hreach3
    obtain ⟨j4, p4, heq4, hp4⟩ := ctrlAttr_call 0xAF01 stopAttr' k ua ux uy 0xF7 up uram uprg
      ucyc false (codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode) hI'
    rw [hmore3] at heq4
    have hpc4 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
    have hsp4 : ctrlAttr_s 0xF7 = 0xF7 := by delta ctrlAttr_s; rfl
    rw [hpc4, hsp4, ctrlAttr_bad_eq] at heq4
    rw [heq4] at heq1
    have hX : XStep ram (ctrlAttr_ram uram) :=
      attr_step ram uram (finish_stage ram (bg2 ram) uram hC (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1)
    have hL : Far ram → LStep ram (ctrlAttr_ram uram) := fun hf =>
      attr_stepL ram uram (finish_stageL ram (bg2 ram) uram hC (hCL hf) (upSpeed_bound hinv)
        (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1 k705)
    have hkeepW (i : UInt16) (hw : attrWritten i = false) : ctrlAttr_ram uram i = uram i := by
      simp only [attrWritten, beq_eq_false_iff_ne, ne_eq] at hw
      exact attr_keep _ _ hw
    have hzeroW (i : UInt16) (hz : zeroed i = true) : ctrlAttr_ram uram i = 0 ∨ ctrlAttr_ram uram i = uram i := by
      simp only [zeroed, beq_iff_eq] at hz
      subst hz
      exact Or.inr (attr_keep _ _ (by decide))
    have hr : ((CPU.runTo (σ := Plain) 0xAF01 (j4 + k)).run
        ⟨⟨0xB179, ctrlAttr_a uram, ctrlAttr_x ux, ctrlAttr_y uy, 0xF7, p4⟩, ctrlAttr_ram uram, uprg,
          ctrlAttr_cyc uram ucyc, false⟩).2.regs.pc = 0xAF01 := by rw [← heq1]; exact hreach
    rw [heq1]
    have hpf := post_from ram b hb epost hepost (Or.inl rfl) hcov _ hX ?_ hkeepW hzeroW rfl rfl hp4 rfl (code_of_prg hcu _ _ _ _) _ hr
    · exact lift _ (fun k v => ((CPU.runTo (σ := Plain) 0xAF01 k).run v).2) _ hpf
    · exact hL
  · exact Or.inr ⟨k, u, Or.inl hu, heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inl hu), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inl hu)), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inr (Or.inl hu))), heq1⟩

end Smb.Routine.PlayerBlock
