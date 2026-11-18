import Smb.Buffer.Renderer.RowCompose
import Smb.Buffer.Renderer.RendererAddressClass
import Smb.Buffer.Renderer.AttributePreserve
import Smb.Buffer.Renderer.BranchPreserve
import Lean.Elab.Tactic.Omega

/-!
The final row of a conditional `$d6` graphics render and the actual
second tile-store instruction. The tile value is the accumulator loaded
by the ROM; fixing that byte for a particular game state is separate.
-/
namespace Smb.Buffer.Renderer.ExactMoveStore

open Smb Smb.Routine Smb.Symbolic
open Smb.Buffer.Renderer.RowCompose

theorem reaches_final_row_from_d6 (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hoff : s.ram 0 = 0xd6) :
    let t := rows 12 s
    t.bad = false ∧ t.regs.pc = 0x88d0 ∧
      t.regs.x = 12 ∧ t.ram 0 = 0xee ∧
      t.regs.p &&& 4 ≠ 0 ∧ t.prg = s.prg ∧
      RowCode t.prg := by
  have hprefix : ∀ k, k < 12 → advanceX k s.regs.x < 12 := by
    intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
        k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨
        k = 9 ∨ k = 10 ∨ k = 11 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hx, advanceX]
  have h := rows_spec 12 s hc hpc hbad hI hprefix
  dsimp only at h
  obtain ⟨hb, hp, hx', ho, hi, hprg, hc'⟩ := h
  have heX : advanceX 12 (0 : UInt8) = 12 := by decide
  have heOff : advanceOffset 12 (0xd6 : UInt8) = 0xee := by decide
  rw [hx, heX] at hx'
  rw [hoff, heOff] at ho
  exact ⟨hb, hp, hx', ho, hi, hprg, hc'⟩

/- The ROM tile pair's second indexed store has the value that the
indirect graphics-table load placed in A, at the address selected by the
saved offset. This includes both actual tile loads and both stores. -/
set_option maxHeartbeats 5000000 in
theorem tile_pair_right_value (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08f9 Smb.Buffer.Renderer.TilePair.code)
    (hI : p &&& 4 ≠ 0)
    (hptr : ram 7 = 0x8b ∨ ram 7 = 0x8c) :
    let s : Plain := ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8906 8).run s).2
    t.bad = false ∧ t.regs.pc = 0x8906 ∧
      t.regs.x = ram 0 ∧
      t.ram (0x345 + (ram 0).toUInt16) = t.regs.a := by
  dsimp only
  rcases hptr with hptr | hptr
  all_goals
    simp only [CodeAt, Smb.Buffer.Renderer.TilePair.code,
      UInt16.reduceAdd] at hc
    generalize hr : ((CPU.runTo (σ := Plain) 0x8906 8).run
      ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
    have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
    sym_run hr [hc, hi, hptr] until 0x8906
    all_goals
      intros
      clear hc hi
      subst hr
      rw [runTo_snd_stop _ 0x8906 _ rfl]
      simp_all (config := { maxSteps := 1000000 })
      bv_decide


/- The first store in the same ROM tile pair. -/
set_option maxHeartbeats 5000000 in
theorem tile_pair_left_value (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08f9 Smb.Buffer.Renderer.TilePair.code)
    (hI : p &&& 4 ≠ 0)
    (hptr : ram 7 = 0x8b ∨ ram 7 = 0x8c) :
    let s : Plain := ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8900 3).run s).2
    t.bad = false ∧ t.regs.pc = 0x8900 ∧
      t.regs.x = ram 0 ∧
      t.ram (0x344 + (ram 0).toUInt16) = t.regs.a := by
  dsimp only
  rcases hptr with hptr | hptr
  all_goals
    simp only [CodeAt, Smb.Buffer.Renderer.TilePair.code,
      UInt16.reduceAdd] at hc
    generalize hr : ((CPU.runTo (σ := Plain) 0x8900 3).run
      ⟨⟨0x88f9, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2 = t
    have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
    sym_run hr [hc, hi, hptr] until 0x8900
    all_goals
      intros
      clear hc hi
      subst hr
      simp only [runTo_run_zero]
      bv_decide


/-- The row prelude followed through both tile stores, with the exact
bounded ROM fragments used by `RowCompose.rowBody`. -/
def rowTile (s : Plain) : Plain :=
  let s := ((CPU.runTo (σ := Plain) 0x88e2 14).run s).2
  let s := ((CPU.runTo (σ := Plain) 0x88e7 3).run s).2
  let s := ((CPU.runTo (σ := Plain) 0x88f9 11).run s).2
  ((CPU.runTo (σ := Plain) 0x8906 8).run s).2

def rowTileLeft (s : Plain) : Plain :=
  let s := ((CPU.runTo (σ := Plain) 0x88e2 14).run s).2
  let s := ((CPU.runTo (σ := Plain) 0x88e7 3).run s).2
  let s := ((CPU.runTo (σ := Plain) 0x88f9 11).run s).2
  ((CPU.runTo (σ := Plain) 0x8900 3).run s).2

/-- For any row entry, the ROM's right tile instruction stores its loaded
byte at `$0345 +` the saved byte offset. -/
theorem one_row_right_store (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : RowCode prg) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let tile := rowTile s
    tile.bad = false ∧ tile.regs.pc = 0x8906 ∧
      tile.regs.x = ram 0 ∧
      tile.ram (0x345 + (ram 0).toUInt16) = tile.regs.a := by
  dsimp only [rowTile]
  have hpre := prelude_to_tile_pair a x y sp p ram prg cyc
    hc.pre hc.high hc.table hc.rest hI
  rcases preEq : ((CPU.runTo (σ := Plain) 0x88f9 11).run
    ((CPU.runTo (σ := Plain) 0x88e7 3).run
      ((CPU.runTo (σ := Plain) 0x88e2 14).run
        ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2).2).2 with
    ⟨⟨pc1, a1, x1, y1, sp1, p1⟩, ram1, prg1, cyc1, bad1⟩
  dsimp only at hpre
  rw [preEq] at hpre
  dsimp only at hpre
  obtain ⟨hb1, hpc1, h01, _, hptr, hi1, hprg1⟩ := hpre
  subst bad1 pc1 prg1
  have ht := tile_pair_right_value a1 x1 y1 sp1 p1 ram1 prg cyc1
    hc.tile hi1 hptr
  dsimp only at ht
  obtain ⟨hb2, hpc2, hx2, hwrite⟩ := ht
  rw [h01] at hwrite
  simpa only [preEq] using
    (show _ from ⟨hb2, hpc2, hx2.trans h01, hwrite⟩)


/-- The same row entry reaches the first tile store at `$0344 +` the
saved byte offset. -/
theorem one_row_left_store (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : RowCode prg) (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let tile := rowTileLeft s
    tile.bad = false ∧ tile.regs.pc = 0x8900 ∧
      tile.regs.x = ram 0 ∧
      tile.ram (0x344 + (ram 0).toUInt16) = tile.regs.a := by
  dsimp only [rowTileLeft]
  have hpre := prelude_to_tile_pair a x y sp p ram prg cyc
    hc.pre hc.high hc.table hc.rest hI
  rcases preEq : ((CPU.runTo (σ := Plain) 0x88f9 11).run
    ((CPU.runTo (σ := Plain) 0x88e7 3).run
      ((CPU.runTo (σ := Plain) 0x88e2 14).run
        ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2).2).2 with
    ⟨⟨pc1, a1, x1, y1, sp1, p1⟩, ram1, prg1, cyc1, bad1⟩
  dsimp only at hpre
  rw [preEq] at hpre
  dsimp only at hpre
  obtain ⟨hb1, hpc1, h01, _, hptr, hi1, hprg1⟩ := hpre
  subst bad1 pc1 prg1
  have ht := tile_pair_left_value a1 x1 y1 sp1 p1 ram1 prg cyc1
    hc.tile hi1 hptr
  dsimp only at ht
  obtain ⟨hb2, hpc2, hx2, hwrite⟩ := ht
  rw [h01] at hwrite
  simpa only [preEq] using
    (show _ from ⟨hb2, hpc2, hx2.trans h01, hwrite⟩)


/-- Every eligible row in a composed render performs the same actual
right tile store, at the address given by the offset recurrence. -/
theorem row_n_right_store (n : Nat) (s : Plain)
    (hc : RowCode s.prg) (hpc : s.regs.pc = 0x88d0)
    (hbad : s.bad = false) (hI : s.regs.p &&& 4 ≠ 0)
    (hprefix : ∀ k, k < n → advanceX k s.regs.x < 12) :
    let tile := rowTile (rows n s)
    tile.bad = false ∧ tile.regs.pc = 0x8906 ∧
      tile.regs.x = advanceOffset n (s.ram 0) ∧
      tile.ram (0x345 + (advanceOffset n (s.ram 0)).toUInt16) =
        tile.regs.a := by
  have hn := rows_spec n s hc hpc hbad hI hprefix
  dsimp only at hn
  rcases midEq : rows n s with
    ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩
  rw [midEq] at hn
  dsimp only at hn
  obtain ⟨hb, hp, _, ho, hi, _, hcMid⟩ := hn
  subst bad pc
  have ht := one_row_right_store a x y sp p ram prg cyc hcMid hi
  dsimp only at ht
  rw [ho] at ht
  simpa only [rowTile, midEq] using ht


theorem row_n_left_store (n : Nat) (s : Plain)
    (hc : RowCode s.prg) (hpc : s.regs.pc = 0x88d0)
    (hbad : s.bad = false) (hI : s.regs.p &&& 4 ≠ 0)
    (hprefix : ∀ k, k < n → advanceX k s.regs.x < 12) :
    let tile := rowTileLeft (rows n s)
    tile.bad = false ∧ tile.regs.pc = 0x8900 ∧
      tile.regs.x = advanceOffset n (s.ram 0) ∧
      tile.ram (0x344 + (advanceOffset n (s.ram 0)).toUInt16) =
        tile.regs.a := by
  have hn := rows_spec n s hc hpc hbad hI hprefix
  dsimp only at hn
  rcases midEq : rows n s with
    ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩
  rw [midEq] at hn
  dsimp only at hn
  obtain ⟨hb, hp, _, ho, hi, _, hcMid⟩ := hn
  subst bad pc
  have ht := one_row_left_store a x y sp p ram prg cyc hcMid hi
  dsimp only at ht
  rw [ho] at ht
  simpa only [rowTileLeft, midEq] using ht


private theorem prefix_from_row_zero (n : Nat) (s : Plain)
    (hx : s.regs.x = 0) (hn : n < 13) :
    ∀ k, k < n → advanceX k s.regs.x < 12 := by
  intro k hk
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨
      k = 9 ∨ k = 10 ∨ k = 11 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hx, advanceX]

/-- For each of the 13 rows, this is the actual left tile store. -/
theorem every_row_left_store (n : Nat) (s : Plain)
    (hc : RowCode s.prg) (hpc : s.regs.pc = 0x88d0)
    (hbad : s.bad = false) (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hn : n < 13) :
    let tile := rowTileLeft (rows n s)
    tile.bad = false ∧ tile.regs.pc = 0x8900 ∧
      tile.regs.x = advanceOffset n (s.ram 0) ∧
      tile.ram (0x344 + (advanceOffset n (s.ram 0)).toUInt16) =
        tile.regs.a :=
  row_n_left_store n s hc hpc hbad hI (prefix_from_row_zero n s hx hn)

/-- For each of the 13 rows, this is the actual right tile store. -/
theorem every_row_right_store (n : Nat) (s : Plain)
    (hc : RowCode s.prg) (hpc : s.regs.pc = 0x88d0)
    (hbad : s.bad = false) (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hn : n < 13) :
    let tile := rowTile (rows n s)
    tile.bad = false ∧ tile.regs.pc = 0x8906 ∧
      tile.regs.x = advanceOffset n (s.ram 0) ∧
      tile.ram (0x345 + (advanceOffset n (s.ram 0)).toUInt16) =
        tile.regs.a :=
  row_n_right_store n s hc hpc hbad hI (prefix_from_row_zero n s hx hn)


/-- The last row's right tile store writes its ROM-loaded tile value to
Mario's `$0433` byte when the saved row offset is `$ee`. This theorem
stops at `$8906`, before the attribute store and row-exit branch. -/
theorem final_row_right_store (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : RowCode prg) (hI : p &&& 4 ≠ 0)
    (hoff : ram 0 = 0xee) :
    let pre := ((CPU.runTo (σ := Plain) 0x88f9 11).run
      ((CPU.runTo (σ := Plain) 0x88e7 3).run
        ((CPU.runTo (σ := Plain) 0x88e2 14).run
          ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2).2).2
    let tile := ((CPU.runTo (σ := Plain) 0x8906 8).run pre).2
    tile.bad = false ∧ tile.regs.pc = 0x8906 ∧
      tile.regs.x = 0xee ∧ tile.ram 0x433 = tile.regs.a ∧
      tile.regs.p &&& 4 ≠ 0 ∧ RowCode tile.prg := by
  dsimp only
  have hpre := prelude_to_tile_pair a x y sp p ram prg cyc
    hc.pre hc.high hc.table hc.rest hI
  rcases preEq : ((CPU.runTo (σ := Plain) 0x88f9 11).run
    ((CPU.runTo (σ := Plain) 0x88e7 3).run
      ((CPU.runTo (σ := Plain) 0x88e2 14).run
        ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2).2).2 with
    ⟨⟨pc1, a1, x1, y1, sp1, p1⟩, ram1, prg1, cyc1, bad1⟩
  dsimp only at hpre
  rw [preEq] at hpre
  dsimp only at hpre
  obtain ⟨hb1, hpc1, h01, _, hptr, hi1, hprg1⟩ := hpre
  subst bad1 pc1 prg1
  have ht := tile_pair_right_value a1 x1 y1 sp1 p1 ram1 prg cyc1
    hc.tile hi1 hptr
  have htI := Smb.Buffer.Renderer.TilePair.two_tile_writes_keep_I
    a1 x1 y1 sp1 p1 ram1 prg cyc1 hc.tile hi1 hptr
  have htP := Smb.Buffer.Renderer.TilePair.two_tile_writes_keep_prg
    a1 x1 y1 sp1 p1 ram1 prg cyc1 hc.tile hi1 hptr
  dsimp only at ht
  obtain ⟨hb2, hpc2, hx2, hwrite⟩ := ht
  have haddr : (0x345 + (ram1 0).toUInt16 : UInt16) = 0x433 := by
    rw [h01, hoff]
    decide
  rw [haddr] at hwrite
  simpa only [preEq] using
    (show _ from ⟨hb2, hpc2, (hx2.trans h01).trans hoff, hwrite,
      htI, (by simpa only [htP] using hc)⟩)


/-- From the conditional `$d6` start at row zero, the composed first
twelve rows and the last row's actual tile instructions write the
ROM-loaded accumulator byte to Mario's `$0433` field. -/
theorem d6_final_row_writes_433 (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hoff : s.ram 0 = 0xd6) :
    let t := rowTile (rows 12 s)
    t.bad = false ∧ t.regs.pc = 0x8906 ∧
      t.regs.x = 0xee ∧ t.ram 0x433 = t.regs.a ∧
      t.regs.p &&& 4 ≠ 0 ∧ RowCode t.prg := by
  have h12 := reaches_final_row_from_d6 s hc hpc hbad hI hx hoff
  dsimp only at h12
  rcases midEq : rows 12 s with
    ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩
  rw [midEq] at h12
  dsimp only at h12
  obtain ⟨hb12, hp12, hx12, hoff12, hi12, _, hc12⟩ := h12
  subst bad pc
  have h := final_row_right_store a x y sp p ram prg cyc hc12 hi12 hoff12
  simpa only [rowTile, midEq] using h


/-- The final row's attribute store preserves the tile value at `$0433`
unless its index from `$04` is `$3a`, the one aliasing value. -/
theorem d6_final_attribute_keeps_433 (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hoff : s.ram 0 = 0xd6)
    (h4 : (rowTile (rows 12 s)).ram 4 ≠ 0x3a) :
    let tile := rowTile (rows 12 s)
    let out := ((CPU.runTo (σ := Plain) 0x893c 26).run tile).2
    out.bad = false ∧ out.regs.pc = 0x893c ∧
      out.ram 0x433 = tile.regs.a := by
  have ht := d6_final_row_writes_433 s hc hpc hbad hI hx hoff
  dsimp only at ht
  rcases tileEq : rowTile (rows 12 s) with
    ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩
  rw [tileEq] at ht h4
  dsimp only at ht h4
  obtain ⟨hb, hp, _, hwrite, hi, hcTile⟩ := ht
  subst bad pc
  have ha := Smb.Buffer.Renderer.AttributePreserve.keeps_433
    a x y sp p ram prg cyc hcTile.attr hi h4
  dsimp only at ha
  obtain ⟨haBad, haPc, haRam⟩ := ha
  simpa only [tileEq] using
    (show _ from ⟨haBad, haPc, haRam.trans hwrite⟩)


/-- The composed final row also supplies the state needed to take the
non-looping branch after the attribute phase. -/
theorem d6_final_attribute_state (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hoff : s.ram 0 = 0xd6) :
    let tile := rowTile (rows 12 s)
    let out := ((CPU.runTo (σ := Plain) 0x893c 26).run tile).2
    out.ram 1 = 12 ∧ out.regs.p &&& 4 ≠ 0 ∧ RowCode out.prg := by
  have h12 := reaches_final_row_from_d6 s hc hpc hbad hI hx hoff
  dsimp only at h12
  rcases midEq : rows 12 s with
    ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩
  rw [midEq] at h12
  dsimp only at h12
  obtain ⟨hb12, hp12, hx12, _, hi12, _, hc12⟩ := h12
  subst bad pc
  have h := one_row_reaches_branch a x y sp p ram prg cyc
    hc12.pre hc12.high hc12.table hc12.rest hc12.tile hc12.attr hi12
  dsimp only at h
  obtain ⟨_, _, _, h1, _, hiOut, hprg⟩ := h
  simpa only [rowTile, midEq] using
    (show _ from ⟨h1.trans hx12, hiOut, (by simpa only [hprg] using hc12)⟩)


/-- Under the sole attribute-index nonalias condition, the actual
13-row renderer leaves the final right-tile value in `$0433` when its
last branch exits at `$8943`. -/
theorem d6_final_exit_keeps_433 (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hoff : s.ram 0 = 0xd6)
    (h4 : (rowTile (rows 12 s)).ram 4 ≠ 0x3a) :
    let tile := rowTile (rows 12 s)
    let attr := ((CPU.runTo (σ := Plain) 0x893c 26).run tile).2
    let out := ((CPU.runTo (σ := Plain) 0x8943 5).run attr).2
    out.bad = false ∧ out.regs.pc = 0x8943 ∧
      out.ram 0x433 = tile.regs.a := by
  have ha := d6_final_attribute_keeps_433 s hc hpc hbad hI hx hoff h4
  have hs := d6_final_attribute_state s hc hpc hbad hI hx hoff
  dsimp only at ha hs
  rcases attrEq : ((CPU.runTo (σ := Plain) 0x893c 26).run
    (rowTile (rows 12 s))).2 with
    ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩
  rw [attrEq] at ha hs
  dsimp only at ha hs
  obtain ⟨haBad, haPc, haRam⟩ := ha
  obtain ⟨hrow, hi, hcAttr⟩ := hs
  subst bad pc
  have hb := Smb.Buffer.Renderer.BranchPreserve.keeps_433
    a x y sp p ram prg cyc hcAttr.branch hi hrow
  dsimp only at hb
  obtain ⟨hbBad, hbPc, hbRam⟩ := hb
  simpa only [attrEq] using
    (show _ from ⟨hbBad, hbPc, hbRam.trans haRam⟩)


end Smb.Buffer.Renderer.ExactMoveStore
