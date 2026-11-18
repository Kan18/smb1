import Smb.Routine.Collision
import Smb.Routine.FrameSteps
import Smb.Routine.PlayLinks

/-!
# The 2.5-pixel limit through any collision path

`HorizontalLimit`'s frame theorems cover `PlayerCtrlRoutine` (`$B0E9`–`$B179`) on the collision paths its summaries
have: no head hit, no coin, no hidden block, and so on. Here the collision code is the checked region of
`Collision` instead, which covers every path, and the only summaries are the ones on either side of it: movement and
scrolling up to `PlayerBGCollision`, `ImpedePlayerMove`, and the attribute update after it.

`frame0_any`, `frame1_any`, `frame2_any`: a frame on the ground, jumping or falling (`$1D` = 0, 1, 2) from `$B0E9`
that reaches `PlayerHole` either keeps the speed limit and moves Mario at most 2.5 pixels (`XStep`), or passed through
one of the region's exits that end normal play: a pipe entry, the side pipe, the flag grab or climbing. The run needn't reach `$B179`: one that doesn't (a lag frame cut
short) says nothing, and the frame contract already asks for no lag. The region's entry conditions at
`PlayerBGCollision` are hypotheses on the RAM there: the shared global bounds and the entry box's cells.
-/
namespace Smb.Routine.FrameCollision
open Smb Smb.Abs Smb.Routine Smb.Routine.HorizontalLimit Smb.Abs.Collision Smb.Routine.Collision

/-- The RAM at `PlayerBGCollision`'s entry, on a ground-state frame. -/
noncomputable abbrev bg0 (ram : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA0_s 0xF7) (ctrlA0_ram 0xF7 ram romFn)

/-- The RAM at `PlayerBGCollision`'s entry, on a frame in state 1. -/
noncomputable abbrev bg1 (ram : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA1_s 0xF7) (ctrlA1_ram 0xF7 ram romFn)

/-- The RAM at `PlayerBGCollision`'s entry, on a frame in state 2. -/
noncomputable abbrev bg2 (ram : UInt16 → UInt8) : UInt16 → UInt8 := ctrlJ_ram (ctrlA2_s 0xF7) (ctrlA2_ram 0xF7 ram romFn)

theorem entry_eq : conf.entries.length = 1 := by native_decide

theorem entry_fields : ∀ e ∈ conf.entries, e.pc = 0xDC64 ∧ e.s = 0xF5 ∧ e.a = .top ∧ e.x = .top ∧ e.y = .top ∧
    (∀ v : UInt8, (v &&& 4 == 0) = false → e.p.mem v = true) := by
  have h : conf.entries.all (fun e => e.pc == 0xDC64 && e.s == 0xF5 && topB e.a && topB e.x && topB e.y &&
      (List.range 256).all fun n => (UInt8.ofNat n &&& 4 == 0) || e.p.mem (UInt8.ofNat n)) = true := by native_decide
  intro e he
  have := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at this
  obtain ⟨⟨⟨⟨⟨hpc, hs⟩, ha⟩, hx⟩, hy⟩, hp⟩ := this
  refine ⟨hpc, hs, eq_top_of_topB ha, eq_top_of_topB hx, eq_top_of_topB hy, fun v hv => ?_⟩
  rcases hp v.toNat v.toNat_lt with h1 | h1
  · simp only [UInt8.ofNat_toNat] at h1; rw [h1] at hv; cases hv
  · simpa using h1

theorem impede_keeps (side : UInt8) (ram : UInt16 → UInt8) (i : UInt16)
    (hi : i = 0x71A ∨ i = 0x71B ∨ i = 0x71C ∨ i = 0x71D ∨ i = 0x3A1) : impedeRam side ram i = ram i := by
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> (unfold impedeRam; cases impedeInto side ram <;> rfl)


theorem stopA : ∀ a : UInt16, (0x8E04 ≤ a && a ≤ 0x8E18 || 0xAF93 ≤ a && a ≤ 0xB049 || 0xB0E9 ≤ a && a ≤ 0xB15A ||
      0xB329 ≤ a && a ≤ 0xC046 || 0xE29C ≤ a && a ≤ 0xE2DD || 0xF12A ≤ a && a ≤ 0xF281) = true → a ≠ 0xB179 := by
  intro a h; revert h; bv_decide (config := { enums := false })
theorem stopJ : ∀ a : UInt16, (0xB15A ≤ a && a ≤ 0xB15C || a == 0xDC64) = true → a ≠ 0xB179 := by
  intro a h; revert h; bv_decide (config := { enums := false })
theorem stopAttr : ∀ a : UInt16, (0xB15D ≤ a && a ≤ 0xB178) = true → a ≠ 0xB179 := by
  intro a h; revert h; bv_decide (config := { enums := false })
theorem stopImp : ∀ a : UInt16, (0xDF4B ≤ a && a ≤ 0xDF8A) = true → a ≠ 0xB179 := by
  intro a h; revert h; bv_decide (config := { enums := false })

theorem code_romFn (a x y s p : UInt8) (pc : UInt16) (ram : UInt16 → UInt8) (cyc : UInt64) (bad : Bool) :
    Code (romOf Smb.prg) ⟨⟨pc, a, x, y, s, p⟩, ram, romFn, cyc, bad⟩ := by
  intro a _
  show Smb.prg.get! ((a &&& 0x7FFF) &&& 0x7FFF).toNat = Smb.prg.get! (a &&& 0x7FFF).toNat
  rw [and_idem]

theorem attr_len : (0x315D : UInt16).toNat + ctrlAttrCode.length ≤ 0x8000 := by decide
theorem impede_len : (0x5F4B : UInt16).toNat + impedeCode.length ≤ 0x8000 := by decide

set_option maxHeartbeats 8000000 in
/-- **A ground-state frame keeps the 2.5-pixel limit, whatever the collision code does**, unless it ends normal
play: a frame from `$B0E9` that reaches `PlayerHole` has `XStep` from its entry RAM to its end, or passed a pipe
entry, the side pipe, the flag grab or climbing. -/
theorem frame0_any (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hcells : ∀ e ∈ conf.entries, ∀ c ∈ e.cells, c.2.mem (bg0 ram c.1) = true)
    (hglob : ∀ i, (gAt conf.globals i).mem (bg0 ram i) = true)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xB179) :
    XStep ram ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88) ∧
        ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xB179 k).run u).2 := by
  generalize hs0 : (⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩ : Plain) = s0 at hreach ⊢
  generalize ht0 : ((CPU.runTo (σ := Plain) 0xB179 n).run s0).2 = t at hreach ⊢
  -- More fuel, then movement and scrolling up to `PlayerBGCollision`.
  have hmore := runTo_more 0xB179 n 1600 s0 (by rw [ht0]; exact hreach)
  rw [ht0] at hmore
  subst hs0
  obtain ⟨j1, p1, c1, heq1, hp1⟩ := ctrlA0_call 0xB179 stopA (n + 100) a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  rw [show n + 100 + 1500 = n + 1600 by omega, hmore] at heq1
  have hpc1 : ctrlA0_pc = 45402 := by delta ctrlA0_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨j2, p2, heq2, hp2⟩ := ctrlJ_call 0xB179 stopJ (j1 + (n + 100) - 4)
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
  have hreach2 : ((CPU.runTo (σ := Plain) 0xB179 (j2 + (j1 + (n + 100) - 4))).run s2).2.regs.pc = 0xB179 := by
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
  obtain ⟨k, u, hex, hcu, hiu, heq3⟩ := collision_through s2 hcode2 e he hh2 _ hreach2
  rw [heq3] at heq1
  -- The scroll stage's output at the region's entry, and what the region keeps.
  have hC : ScrollOut ram (bg0 ram) :=
    ctrlJ_out (ctrlA0_s 0xF7) ram _ (ctrlA0_out 0xF7 ram romFn hinv ht hs hz hjs)
  have hk := kept hiu
  have hs2ram : s2.ram = bg0 ram := by subst hs2; rfl
  rw [hs2ram] at hk
  obtain ⟨k57, k86, k6d, k400, k71a, k71b, k71c, k71d, k3a1, _, _⟩ := hk
  have hreach3 : ((CPU.runTo (σ := Plain) 0xB179 k).run u).2.regs.pc = 0xB179 := by rw [← heq1]; exact hreach
  rcases exit_cases _ hex with hu | hu | hu | hu | hu | hu
  · -- `ImpedePlayerMove`, then back to `$B15D`.
    left
    have hst := impede_stack hiu hu
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu hst
    subst hu
    obtain ⟨b, _, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    have hmore3 := runTo_more 0xB179 k 40 _ hreach3
    obtain ⟨j5, p5, a5, x5, y5, c5, heq5, hp5⟩ := impede_call 0xB179 stopImp k ua ux uy us up uram uprg ucyc false
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
    have hreach5 : ((CPU.runTo (σ := Plain) 0xB179 (j5 + k)).run
        ⟨⟨0xDF8A, a5, x5, y5, us, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩).2.regs.pc = 0xB179 := by
      rw [← heq1]; exact hreach
    -- One RTS or two, then the attribute update.
    have hstep (K : Nat) (w : Plain) (hw : w.regs.pc ≠ 0xB179)
        (h : ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.regs.pc = 0xB179) :
        ∃ K', K = K' + 1 ∧ ((CPU.runTo (σ := Plain) 0xB179 K).run w).2 =
          ((CPU.runTo (σ := Plain) 0xB179 K').run (CPU.step.run w).2).2 := by
      cases K with
      | zero => rw [runTo_zero] at h; exact absurd h hw
      | succ K' => exact ⟨K', rfl, runTo_succ _ _ _ hw⟩
    obtain ⟨K, _, hK⟩ := hstep _ _ (by simp) hreach5
    rw [hK] at heq1 hreach5
    have hfin (K : Nat) (w : Plain) (hwpc : w.regs.pc = 0xB15D) (hws : w.ram = impedeRam (uram 0) uram)
        (hwprg : w.prg = uprg) (hwbad : w.bad = false) (hwp : (w.regs.p &&& 4 == 0) = false)
        (hr : ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.regs.pc = 0xB179) :
        XStep ram ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.ram := by
      obtain ⟨⟨wpc, wa, wx, wy, ws, wp⟩, wram, wprg, wcyc, wbad⟩ := w
      simp only at hwpc hws hwprg hwbad hwp
      subst wpc wram wprg wbad
      have hmore6 := runTo_more 0xB179 K 20 _ hr
      obtain ⟨j6, p6, heq6, _⟩ := ctrlAttr_call 0xB179 stopAttr K wa wx wy ws wp _ uprg wcyc false hattr hwp
      rw [hmore6] at heq6
      have hpc6 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
      rw [hpc6] at heq6
      rw [runTo_at 0xB179 (j6 + K) _ rfl] at heq6
      rw [heq6]
      exact hX
    rw [heq1]
    rcases hst.2.2 with hsF5 | ⟨hsF3, h4, h5⟩
    · subst hsF5
      have h1 := rts_foot a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h1
      obtain ⟨e1, _, e3, _, _, _, e7, e8, e9⟩ := h1
      exact hfin K _ e1 e7 e8 e9 (by rw [e3]; exact hp5) hreach5
    · subst hsF3
      have h1 := rts_side1 a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans h4) ((hRs _ (by simp)).trans h5) hI5
      rw [runTo_one 0xDE02 _ (by simp)] at h1
      generalize hw1 : (CPU.step.run (⟨⟨0xDF8A, a5, x5, y5, 0xF3, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩ : Plain)).2 = w1 at h1 hreach5 ⊢
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h1
      obtain ⟨K2, _, hK2⟩ := hstep _ _ (by rw [f1]; simp) hreach5
      rw [hK2] at hreach5 ⊢
      obtain ⟨⟨w1pc, w1a, w1x, w1y, w1s, w1p⟩, w1ram, w1prg, w1cyc, w1bad⟩ := w1
      simp only at f1 f2 f3 f4 f5 f6 f7 f8 f9
      subst w1pc w1s w1p w1a w1x w1y w1ram w1prg w1bad
      have h2 := rts_side2 a5 x5 y5 p5 _ uprg w1cyc hr2 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h2
      obtain ⟨e1, _, e3, _, _, _, e7, e8, e9⟩ := h2
      exact hfin K2 _ e1 e7 e8 e9 (by rw [e3]; exact hp5) hreach5
  · -- Straight back at `$B15D`.
    left
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu
    subst hu
    obtain ⟨b, _, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    have hmore3 := runTo_more 0xB179 k 20 _ hreach3
    obtain ⟨j4, p4, heq4, _⟩ := ctrlAttr_call 0xB179 stopAttr k ua ux uy us up uram uprg
      ucyc false (codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode) hI'
    rw [show k + 20 = k + 20 from rfl, hmore3] at heq4
    have hpc4 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
    rw [hpc4] at heq4
    rw [runTo_at 0xB179 (j4 + k) _ rfl] at heq4
    rw [heq1, heq4]
    simp only
    exact attr_step ram uram (finish_stage ram (bg0 ram) uram hC (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1)
  · exact Or.inr ⟨k, u, Or.inl hu, heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inl hu), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inl hu)), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inr hu)), heq1⟩

set_option maxHeartbeats 8000000 in
/-- **The same for a jumping frame** (`$1D` = 1): a frame from `$B0E9` that reaches `PlayerHole` has `XStep` from its entry RAM to its end, or passed a pipe
entry, the side pipe, the flag grab or climbing. -/
theorem frame1_any (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hcells : ∀ e ∈ conf.entries, ∀ c ∈ e.cells, c.2.mem (bg1 ram c.1) = true)
    (hglob : ∀ i, (gAt conf.globals i).mem (bg1 ram i) = true)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xB179) :
    XStep ram ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88) ∧
        ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xB179 k).run u).2 := by
  generalize hs0 : (⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩ : Plain) = s0 at hreach ⊢
  generalize ht0 : ((CPU.runTo (σ := Plain) 0xB179 n).run s0).2 = t at hreach ⊢
  -- More fuel, then movement and scrolling up to `PlayerBGCollision`.
  have hmore := runTo_more 0xB179 n 1600 s0 (by rw [ht0]; exact hreach)
  rw [ht0] at hmore
  subst hs0
  obtain ⟨j1, p1, c1, heq1, hp1⟩ := ctrlA1_call 0xB179 stopA (n + 100) a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  rw [show n + 100 + 1500 = n + 1600 by omega, hmore] at heq1
  have hpc1 : ctrlA1_pc = 45402 := by delta ctrlA1_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨j2, p2, heq2, hp2⟩ := ctrlJ_call 0xB179 stopJ (j1 + (n + 100) - 4)
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
  have hreach2 : ((CPU.runTo (σ := Plain) 0xB179 (j2 + (j1 + (n + 100) - 4))).run s2).2.regs.pc = 0xB179 := by
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
  obtain ⟨k, u, hex, hcu, hiu, heq3⟩ := collision_through s2 hcode2 e he hh2 _ hreach2
  rw [heq3] at heq1
  -- The scroll stage's output at the region's entry, and what the region keeps.
  have hC : ScrollOut ram (bg1 ram) :=
    ctrlJ_out (ctrlA1_s 0xF7) ram _ (ctrlA1_out 0xF7 ram romFn hinv ht hs hz hjs)
  have hk := kept hiu
  have hs2ram : s2.ram = bg1 ram := by subst hs2; rfl
  rw [hs2ram] at hk
  obtain ⟨k57, k86, k6d, k400, k71a, k71b, k71c, k71d, k3a1, _, _⟩ := hk
  have hreach3 : ((CPU.runTo (σ := Plain) 0xB179 k).run u).2.regs.pc = 0xB179 := by rw [← heq1]; exact hreach
  rcases exit_cases _ hex with hu | hu | hu | hu | hu | hu
  · -- `ImpedePlayerMove`, then back to `$B15D`.
    left
    have hst := impede_stack hiu hu
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu hst
    subst hu
    obtain ⟨b, _, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    have hmore3 := runTo_more 0xB179 k 40 _ hreach3
    obtain ⟨j5, p5, a5, x5, y5, c5, heq5, hp5⟩ := impede_call 0xB179 stopImp k ua ux uy us up uram uprg ucyc false
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
    have hreach5 : ((CPU.runTo (σ := Plain) 0xB179 (j5 + k)).run
        ⟨⟨0xDF8A, a5, x5, y5, us, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩).2.regs.pc = 0xB179 := by
      rw [← heq1]; exact hreach
    -- One RTS or two, then the attribute update.
    have hstep (K : Nat) (w : Plain) (hw : w.regs.pc ≠ 0xB179)
        (h : ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.regs.pc = 0xB179) :
        ∃ K', K = K' + 1 ∧ ((CPU.runTo (σ := Plain) 0xB179 K).run w).2 =
          ((CPU.runTo (σ := Plain) 0xB179 K').run (CPU.step.run w).2).2 := by
      cases K with
      | zero => rw [runTo_zero] at h; exact absurd h hw
      | succ K' => exact ⟨K', rfl, runTo_succ _ _ _ hw⟩
    obtain ⟨K, _, hK⟩ := hstep _ _ (by simp) hreach5
    rw [hK] at heq1 hreach5
    have hfin (K : Nat) (w : Plain) (hwpc : w.regs.pc = 0xB15D) (hws : w.ram = impedeRam (uram 0) uram)
        (hwprg : w.prg = uprg) (hwbad : w.bad = false) (hwp : (w.regs.p &&& 4 == 0) = false)
        (hr : ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.regs.pc = 0xB179) :
        XStep ram ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.ram := by
      obtain ⟨⟨wpc, wa, wx, wy, ws, wp⟩, wram, wprg, wcyc, wbad⟩ := w
      simp only at hwpc hws hwprg hwbad hwp
      subst wpc wram wprg wbad
      have hmore6 := runTo_more 0xB179 K 20 _ hr
      obtain ⟨j6, p6, heq6, _⟩ := ctrlAttr_call 0xB179 stopAttr K wa wx wy ws wp _ uprg wcyc false hattr hwp
      rw [hmore6] at heq6
      have hpc6 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
      rw [hpc6] at heq6
      rw [runTo_at 0xB179 (j6 + K) _ rfl] at heq6
      rw [heq6]
      exact hX
    rw [heq1]
    rcases hst.2.2 with hsF5 | ⟨hsF3, h4, h5⟩
    · subst hsF5
      have h1 := rts_foot a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h1
      obtain ⟨e1, _, e3, _, _, _, e7, e8, e9⟩ := h1
      exact hfin K _ e1 e7 e8 e9 (by rw [e3]; exact hp5) hreach5
    · subst hsF3
      have h1 := rts_side1 a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans h4) ((hRs _ (by simp)).trans h5) hI5
      rw [runTo_one 0xDE02 _ (by simp)] at h1
      generalize hw1 : (CPU.step.run (⟨⟨0xDF8A, a5, x5, y5, 0xF3, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩ : Plain)).2 = w1 at h1 hreach5 ⊢
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h1
      obtain ⟨K2, _, hK2⟩ := hstep _ _ (by rw [f1]; simp) hreach5
      rw [hK2] at hreach5 ⊢
      obtain ⟨⟨w1pc, w1a, w1x, w1y, w1s, w1p⟩, w1ram, w1prg, w1cyc, w1bad⟩ := w1
      simp only at f1 f2 f3 f4 f5 f6 f7 f8 f9
      subst w1pc w1s w1p w1a w1x w1y w1ram w1prg w1bad
      have h2 := rts_side2 a5 x5 y5 p5 _ uprg w1cyc hr2 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h2
      obtain ⟨e1, _, e3, _, _, _, e7, e8, e9⟩ := h2
      exact hfin K2 _ e1 e7 e8 e9 (by rw [e3]; exact hp5) hreach5
  · -- Straight back at `$B15D`.
    left
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu
    subst hu
    obtain ⟨b, _, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    have hmore3 := runTo_more 0xB179 k 20 _ hreach3
    obtain ⟨j4, p4, heq4, _⟩ := ctrlAttr_call 0xB179 stopAttr k ua ux uy us up uram uprg
      ucyc false (codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode) hI'
    rw [show k + 20 = k + 20 from rfl, hmore3] at heq4
    have hpc4 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
    rw [hpc4] at heq4
    rw [runTo_at 0xB179 (j4 + k) _ rfl] at heq4
    rw [heq1, heq4]
    simp only
    exact attr_step ram uram (finish_stage ram (bg1 ram) uram hC (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1)
  · exact Or.inr ⟨k, u, Or.inl hu, heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inl hu), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inl hu)), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inr hu)), heq1⟩

set_option maxHeartbeats 8000000 in
/-- **The same for a falling frame** (`$1D` = 2): a frame from `$B0E9` that reaches `PlayerHole` has `XStep` from its entry RAM to its end, or passed a pipe
entry, the side pipe, the flag grab or climbing. -/
theorem frame2_any (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hcells : ∀ e ∈ conf.entries, ∀ c ∈ e.cells, c.2.mem (bg2 ram c.1) = true)
    (hglob : ∀ i, (gAt conf.globals i).mem (bg2 ram i) = true)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xB179) :
    XStep ram ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88) ∧
        ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xB179 k).run u).2 := by
  generalize hs0 : (⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩ : Plain) = s0 at hreach ⊢
  generalize ht0 : ((CPU.runTo (σ := Plain) 0xB179 n).run s0).2 = t at hreach ⊢
  -- More fuel, then movement and scrolling up to `PlayerBGCollision`.
  have hmore := runTo_more 0xB179 n 1600 s0 (by rw [ht0]; exact hreach)
  rw [ht0] at hmore
  subst hs0
  obtain ⟨j1, p1, c1, heq1, hp1⟩ := ctrlA2_call 0xB179 stopA (n + 100) a x y 0xF7 p ram romFn cyc
    rom_ctrlPreCode rom_ctrlJsrCode rom_ctrlMidCode rom_ctrlAuxCode rom_movementSubsCode rom_jumpEngineCode
    rom_physicsCode rom_jumpStartCode rom_animSpeedCode rom_imposeFrictionCode rom_movePlayerHorizontallyCode
    rom_movePlayerVerticallyCode rom_imposeGravityCode rom_scrollCode rom_xOffscreenBitsData rom_getXOffscreenBitsCode
    rom_dividePDiffCode rom_getPlayerOffscreenBitsCode rom_getOffScreenBitsSetCode rom_yOffscreenBitsData
    rom_getYOffscreenBitsCode rom_relativePlayerPositionCode rom_relWOfsCode rom_getObjRelativePositionCode
    rom_boundingBoxCoreCode hI ht hz hs hjs hspd
  rw [show n + 100 + 1500 = n + 1600 by omega, hmore] at heq1
  have hpc1 : ctrlA2_pc = 45402 := by delta ctrlA2_pc; rfl
  rw [hpc1] at heq1
  obtain ⟨j2, p2, heq2, hp2⟩ := ctrlJ_call 0xB179 stopJ (j1 + (n + 100) - 4)
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
  have hreach2 : ((CPU.runTo (σ := Plain) 0xB179 (j2 + (j1 + (n + 100) - 4))).run s2).2.regs.pc = 0xB179 := by
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
  obtain ⟨k, u, hex, hcu, hiu, heq3⟩ := collision_through s2 hcode2 e he hh2 _ hreach2
  rw [heq3] at heq1
  -- The scroll stage's output at the region's entry, and what the region keeps.
  have hC : ScrollOut ram (bg2 ram) :=
    ctrlJ_out (ctrlA2_s 0xF7) ram _ (ctrlA2_out 0xF7 ram romFn hinv ht hs hz hjs)
  have hk := kept hiu
  have hs2ram : s2.ram = bg2 ram := by subst hs2; rfl
  rw [hs2ram] at hk
  obtain ⟨k57, k86, k6d, k400, k71a, k71b, k71c, k71d, k3a1, _, _⟩ := hk
  have hreach3 : ((CPU.runTo (σ := Plain) 0xB179 k).run u).2.regs.pc = 0xB179 := by rw [← heq1]; exact hreach
  rcases exit_cases _ hex with hu | hu | hu | hu | hu | hu
  · -- `ImpedePlayerMove`, then back to `$B15D`.
    left
    have hst := impede_stack hiu hu
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu hst
    subst hu
    obtain ⟨b, _, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    have hmore3 := runTo_more 0xB179 k 40 _ hreach3
    obtain ⟨j5, p5, a5, x5, y5, c5, heq5, hp5⟩ := impede_call 0xB179 stopImp k ua ux uy us up uram uprg ucyc false
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
    have hreach5 : ((CPU.runTo (σ := Plain) 0xB179 (j5 + k)).run
        ⟨⟨0xDF8A, a5, x5, y5, us, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩).2.regs.pc = 0xB179 := by
      rw [← heq1]; exact hreach
    -- One RTS or two, then the attribute update.
    have hstep (K : Nat) (w : Plain) (hw : w.regs.pc ≠ 0xB179)
        (h : ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.regs.pc = 0xB179) :
        ∃ K', K = K' + 1 ∧ ((CPU.runTo (σ := Plain) 0xB179 K).run w).2 =
          ((CPU.runTo (σ := Plain) 0xB179 K').run (CPU.step.run w).2).2 := by
      cases K with
      | zero => rw [runTo_zero] at h; exact absurd h hw
      | succ K' => exact ⟨K', rfl, runTo_succ _ _ _ hw⟩
    obtain ⟨K, _, hK⟩ := hstep _ _ (by simp) hreach5
    rw [hK] at heq1 hreach5
    have hfin (K : Nat) (w : Plain) (hwpc : w.regs.pc = 0xB15D) (hws : w.ram = impedeRam (uram 0) uram)
        (hwprg : w.prg = uprg) (hwbad : w.bad = false) (hwp : (w.regs.p &&& 4 == 0) = false)
        (hr : ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.regs.pc = 0xB179) :
        XStep ram ((CPU.runTo (σ := Plain) 0xB179 K).run w).2.ram := by
      obtain ⟨⟨wpc, wa, wx, wy, ws, wp⟩, wram, wprg, wcyc, wbad⟩ := w
      simp only at hwpc hws hwprg hwbad hwp
      subst wpc wram wprg wbad
      have hmore6 := runTo_more 0xB179 K 20 _ hr
      obtain ⟨j6, p6, heq6, _⟩ := ctrlAttr_call 0xB179 stopAttr K wa wx wy ws wp _ uprg wcyc false hattr hwp
      rw [hmore6] at heq6
      have hpc6 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
      rw [hpc6] at heq6
      rw [runTo_at 0xB179 (j6 + K) _ rfl] at heq6
      rw [heq6]
      exact hX
    rw [heq1]
    rcases hst.2.2 with hsF5 | ⟨hsF3, h4, h5⟩
    · subst hsF5
      have h1 := rts_foot a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h1
      obtain ⟨e1, _, e3, _, _, _, e7, e8, e9⟩ := h1
      exact hfin K _ e1 e7 e8 e9 (by rw [e3]; exact hp5) hreach5
    · subst hsF3
      have h1 := rts_side1 a5 x5 y5 p5 _ uprg c5 hr1 ((hRs _ (by simp)).trans h4) ((hRs _ (by simp)).trans h5) hI5
      rw [runTo_one 0xDE02 _ (by simp)] at h1
      generalize hw1 : (CPU.step.run (⟨⟨0xDF8A, a5, x5, y5, 0xF3, p5⟩, impedeRam (uram 0) uram, uprg, c5, false⟩ : Plain)).2 = w1 at h1 hreach5 ⊢
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h1
      obtain ⟨K2, _, hK2⟩ := hstep _ _ (by rw [f1]; simp) hreach5
      rw [hK2] at hreach5 ⊢
      obtain ⟨⟨w1pc, w1a, w1x, w1y, w1s, w1p⟩, w1ram, w1prg, w1cyc, w1bad⟩ := w1
      simp only at f1 f2 f3 f4 f5 f6 f7 f8 f9
      subst w1pc w1s w1p w1a w1x w1y w1ram w1prg w1bad
      have h2 := rts_side2 a5 x5 y5 p5 _ uprg w1cyc hr2 ((hRs _ (by simp)).trans hst.1) ((hRs _ (by simp)).trans hst.2.1) hI5
      rw [runTo_one 0xB15D _ (by simp)] at h2
      obtain ⟨e1, _, e3, _, _, _, e7, e8, e9⟩ := h2
      exact hfin K2 _ e1 e7 e8 e9 (by rw [e3]; exact hp5) hreach5
  · -- Straight back at `$B15D`.
    left
    obtain ⟨⟨upc, ua, ux, uy, us, up⟩, uram, uprg, ucyc, ubad⟩ := u
    simp only at hu
    subst hu
    obtain ⟨b, _, hb⟩ := hiu
    have hI' : (up &&& 4 == 0) = false := by simpa using hb.i
    have hbad : ubad = false := hb.bad
    subst hbad
    have hmore3 := runTo_more 0xB179 k 20 _ hreach3
    obtain ⟨j4, p4, heq4, _⟩ := ctrlAttr_call 0xB179 stopAttr k ua ux uy us up uram uprg
      ucyc false (codeAt_of_code hcu _ _ attr_len rom_ctrlAttrCode) hI'
    rw [show k + 20 = k + 20 from rfl, hmore3] at heq4
    have hpc4 : ctrlAttr_pc = 0xB179 := by delta ctrlAttr_pc; rfl
    rw [hpc4] at heq4
    rw [runTo_at 0xB179 (j4 + k) _ rfl] at heq4
    rw [heq1, heq4]
    simp only
    exact attr_step ram uram (finish_stage ram (bg2 ram) uram hC (bgX_refl _ _ k400 k86 k6d k57) k71a k71b k71c k71d k3a1)
  · exact Or.inr ⟨k, u, Or.inl hu, heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inl hu), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inl hu)), heq1⟩
  · exact Or.inr ⟨k, u, Or.inr (Or.inr (Or.inr hu)), heq1⟩

/-! ## The entry conditions from the cycle's player region -/

/-- If some plain state with RAM `r` lies in a box of the normal-play cycle's player region at `PlayerBGCollision`,
then `r` meets the collision region's entry conditions: by `PlayLinks`, under the cycle's shared bounds, which are
inside the region's own. -/
theorem entry_of_cycle (r : UInt16 → UInt8)
    (hb : ∃ b ∈ (PlayFrame.P.tableWith PlayFrame.G Smb.prg).at 0xDC64, ∃ (t : Plain) (ram0 : UInt16 → UInt8)
      (prot : UInt16 → Bool), t.ram = r ∧ Holds prot PlayFrame.G ram0 b t) :
    (∀ e ∈ conf.entries, ∀ c ∈ e.cells, c.2.mem (r c.1) = true) ∧ (∀ i, (gAt conf.globals i).mem (r i) = true) := by
  obtain ⟨b, hbm, t, ram0, prot, htr, hh⟩ := hb
  have hl := PlayLinks.links_true
  simp only [PlayLinks.linksOk, Bool.and_eq_true, List.all_eq_true] at hl
  obtain ⟨e', he', hle⟩ := List.any_eq_true.mp (hl.1 b hbm)
  have hh' := holds_of_le hle hh
  subst htr
  refine ⟨fun e he c hc => ?_, fun i => PlayLinks.widen PlayLinks.within_collision PlayLinks.size_collision i _ (hh.glob i)⟩
  have hee : e = e' := by
    have := entry_eq
    match h : conf.entries, he, he' with
    | [x], he, he' =>
      simp only [List.mem_singleton] at he he'
      rw [he, he']
    | [], he, _ => simp at he
    | _ :: _ :: _, _, _ => rw [h] at this; simp at this
  subst hee
  exact hh'.cells c hc

/-- `frame0_any` with its entry conditions from the cycle's player region at `PlayerBGCollision`. -/
theorem frame0_cycle (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 0) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hb : ∃ b ∈ (PlayFrame.P.tableWith PlayFrame.G Smb.prg).at 0xDC64, ∃ (t : Plain) (ram0 : UInt16 → UInt8)
      (prot : UInt16 → Bool), t.ram = bg0 ram ∧ Holds prot PlayFrame.G ram0 b t)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xB179) :
    XStep ram ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88) ∧
        ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xB179 k).run u).2 :=
  let h := entry_of_cycle _ hb
  frame0_any a x y p ram cyc hinv ht hs hz hjs hspd hI h.1 h.2 n hreach

/-- `frame1_any` with its entry conditions from the cycle's player region at `PlayerBGCollision`. -/
theorem frame1_cycle (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 1) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hb : ∃ b ∈ (PlayFrame.P.tableWith PlayFrame.G Smb.prg).at 0xDC64, ∃ (t : Plain) (ram0 : UInt16 → UInt8)
      (prot : UInt16 → Bool), t.ram = bg1 ram ∧ Holds prot PlayFrame.G ram0 b t)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xB179) :
    XStep ram ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88) ∧
        ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xB179 k).run u).2 :=
  let h := entry_of_cycle _ hb
  frame1_any a x y p ram cyc hinv ht hs hz hjs hspd hI h.1 h.2 n hreach

/-- `frame2_any` with its entry conditions from the cycle's player region at `PlayerBGCollision`. -/
theorem frame2_cycle (a x y p : UInt8) (ram : UInt16 → UInt8) (cyc : UInt64)
    (hinv : XInv ram) (ht : ram 0x1D = 2) (hs : ram 0x704 = 0) (hz : ram 0x70B = 0) (hjs : ram 0x70E = 0)
    (hspd : ram 0x9F + 0x40 < 0x80) (hI : (p &&& 4 == 0) = false)
    (hb : ∃ b ∈ (PlayFrame.P.tableWith PlayFrame.G Smb.prg).at 0xDC64, ∃ (t : Plain) (ram0 : UInt16 → UInt8)
      (prot : UInt16 → Bool), t.ram = bg2 ram ∧ Holds prot PlayFrame.G ram0 b t)
    (n : Nat) (hreach : ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.regs.pc = 0xB179) :
    XStep ram ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2.ram ∨
      ∃ k u, (u.regs.pc = 0xDEFA ∨ u.regs.pc = 0xDDFC ∨ u.regs.pc = 0xDE75 ∨ u.regs.pc = 0xDE88) ∧
        ((CPU.runTo (σ := Plain) 0xB179 n).run ⟨⟨0xB0E9, a, x, y, 0xF7, p⟩, ram, romFn, cyc, false⟩).2 =
          ((CPU.runTo (σ := Plain) 0xB179 k).run u).2 :=
  let h := entry_of_cycle _ hb
  frame2_any a x y p ram cyc hinv ht hs hz hjs hspd hI h.1 h.2 n hreach

end Smb.Routine.FrameCollision
