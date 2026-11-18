import Smb.Buffer.Renderer.PointerIndex
import Smb.Buffer.Renderer.RestPrelude
import Smb.Buffer.Renderer.TilePair
import Smb.Buffer.Renderer.AttributeTail
import Smb.Buffer.Renderer.RendererLoopBranch
import Lean.Elab.Tactic.Omega

/-!
Composition of the already checked renderer segments into a complete row.
No new ROM execution is intended here: each seam uses a local machine theorem.
-/
namespace Smb.Buffer.Renderer.RowCompose
open Smb Smb.Routine

set_option maxHeartbeats 3000000 in
theorem prelude_to_tile_pair (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 Smb.Buffer.Renderer.PointerIndex.code)
    (hh : CodeAt prg 0x08e2 Smb.Buffer.Renderer.PointerIndex.highLoadCode)
    (ht : CodeAt prg 0x0b0c Smb.Buffer.Renderer.PointerIndex.highTable)
    (hr : CodeAt prg 0x08e7 Smb.Buffer.Renderer.RestPrelude.code)
    (hI : p &&& 4 ≠ 0) :
    let mid := ((CPU.runTo (σ := Plain) 0x88e7 3).run
      ((CPU.runTo (σ := Plain) 0x88e2 14).run
        ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2).2
    let out := ((CPU.runTo (σ := Plain) 0x88f9 11).run mid).2
    out.bad = false ∧ out.regs.pc = 0x88f9 ∧
      out.ram 0 = ram 0 ∧ out.ram 1 = x ∧
      (out.ram 7 = 0x8b ∨ out.ram 7 = 0x8c) ∧
      out.regs.p &&& 4 ≠ 0 ∧ out.prg = prg := by
  dsimp only
  have hm := Smb.Buffer.Renderer.PointerIndex.high_pointer_from_row_entry
    a x y sp p ram prg cyc hc hh ht hI
  rcases midEq : ((CPU.runTo (σ := Plain) 0x88e7 3).run
    ((CPU.runTo (σ := Plain) 0x88e2 14).run
      ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2).2 with
    ⟨⟨pc', a', x', y', sp', p'⟩, ram', prg', cyc', bad'⟩
  dsimp only at hm
  rw [midEq] at hm
  dsimp only at hm
  obtain ⟨hbad, hpc, hptr, h0, h1, hi, hp⟩ := hm
  subst bad' pc' prg'
  have hrest := Smb.Buffer.Renderer.RestPrelude.reaches_tile_pair
    a' x' y' sp' p' ram' prg cyc' hr hi
  have hrestI := Smb.Buffer.Renderer.RestPrelude.reaches_tile_pair_keeps_I
    a' x' y' sp' p' ram' prg cyc' hr hi
  have hrestP := Smb.Buffer.Renderer.RestPrelude.reaches_tile_pair_keeps_prg
    a' x' y' sp' p' ram' prg cyc' hr hi
  dsimp only at hrest hrestI hrestP
  obtain ⟨hb3, hpc3, h03, h13, h73⟩ := hrest
  simpa only [midEq] using
    (show _ from ⟨hb3, hpc3, h03.trans h0, h13.trans h1,
      h73 ▸ hptr, hrestI, hrestP⟩)

set_option maxHeartbeats 3000000 in
theorem one_row_reaches_branch (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 Smb.Buffer.Renderer.PointerIndex.code)
    (hh : CodeAt prg 0x08e2 Smb.Buffer.Renderer.PointerIndex.highLoadCode)
    (ht : CodeAt prg 0x0b0c Smb.Buffer.Renderer.PointerIndex.highTable)
    (hr : CodeAt prg 0x08e7 Smb.Buffer.Renderer.RestPrelude.code)
    (hp : CodeAt prg 0x08f9 Smb.Buffer.Renderer.TilePair.code)
    (ha : CodeAt prg 0x0906 Smb.Buffer.Renderer.AttributeTail.code)
    (hI : p &&& 4 ≠ 0) :
    let pre := ((CPU.runTo (σ := Plain) 0x88f9 11).run
      ((CPU.runTo (σ := Plain) 0x88e7 3).run
        ((CPU.runTo (σ := Plain) 0x88e2 14).run
          ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2).2).2
    let tile := ((CPU.runTo (σ := Plain) 0x8906 8).run pre).2
    let out := ((CPU.runTo (σ := Plain) 0x893c 26).run tile).2
    out.bad = false ∧ out.regs.pc = 0x893c ∧
      out.ram 0 = ram 0 + 2 ∧ out.ram 1 = x ∧
      tile.regs.x = ram 0 ∧ out.regs.p &&& 4 ≠ 0 ∧ out.prg = prg := by
  dsimp only
  have hpre := prelude_to_tile_pair a x y sp p ram prg cyc hc hh ht hr hI
  rcases preEq : ((CPU.runTo (σ := Plain) 0x88f9 11).run
    ((CPU.runTo (σ := Plain) 0x88e7 3).run
      ((CPU.runTo (σ := Plain) 0x88e2 14).run
        ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩).2).2).2 with
    ⟨⟨pc1, a1, x1, y1, sp1, p1⟩, ram1, prg1, cyc1, bad1⟩
  dsimp only at hpre
  rw [preEq] at hpre
  dsimp only at hpre
  obtain ⟨hbad1, hpc1, h01, h11, hptr, hi1, hprg1⟩ := hpre
  subst bad1 pc1 prg1
  have ht1 := Smb.Buffer.Renderer.TilePair.two_tile_writes_keep_offset
    a1 x1 y1 sp1 p1 ram1 prg cyc1 hp hi1 hptr
  have htI := Smb.Buffer.Renderer.TilePair.two_tile_writes_keep_I
    a1 x1 y1 sp1 p1 ram1 prg cyc1 hp hi1 hptr
  have htP := Smb.Buffer.Renderer.TilePair.two_tile_writes_keep_prg
    a1 x1 y1 sp1 p1 ram1 prg cyc1 hp hi1 hptr
  rcases tileEq : ((CPU.runTo (σ := Plain) 0x8906 8).run
    ⟨⟨0x88f9, a1, x1, y1, sp1, p1⟩, ram1, prg, cyc1, false⟩).2 with
    ⟨⟨pc2, a2, x2, y2, sp2, p2⟩, ram2, prg2, cyc2, bad2⟩
  dsimp only at ht1 htI htP
  rw [tileEq] at ht1 htI htP
  dsimp only at ht1 htI htP
  obtain ⟨hbad2, hpc2, hx2, h02, h12⟩ := ht1
  subst bad2 pc2 prg2
  have ha1 := Smb.Buffer.Renderer.AttributeTail.joins_and_advances
    a2 x2 y2 sp2 p2 ram2 prg cyc2 ha htI
  have haI := Smb.Buffer.Renderer.AttributeTail.joins_keeps_I
    a2 x2 y2 sp2 p2 ram2 prg cyc2 ha htI
  have haP := Smb.Buffer.Renderer.AttributeTail.joins_keeps_prg
    a2 x2 y2 sp2 p2 ram2 prg cyc2 ha htI
  dsimp only at ha1 haI haP
  obtain ⟨hbad3, hpc3, h03, h13⟩ := ha1
  simpa only [preEq, tileEq] using
    (show _ from ⟨hbad3, hpc3, (by calc
        ((CPU.runTo (σ := Plain) 0x893c 26).run
          ⟨⟨0x8906, a2, x2, y2, sp2, p2⟩, ram2, prg, cyc2, false⟩).2.ram 0
          = ram2 0 + 2 := h03
        _ = ram 0 + 2 := by rw [h02, h01]),
      h13.trans (h12.trans h11), hx2.trans h01, haI, haP⟩)

/-- One renderer row, split at the five checked ROM segments. -/
def rowBody (s : Plain) : Plain :=
  let s := ((CPU.runTo (σ := Plain) 0x88e2 14).run s).2
  let s := ((CPU.runTo (σ := Plain) 0x88e7 3).run s).2
  let s := ((CPU.runTo (σ := Plain) 0x88f9 11).run s).2
  let s := ((CPU.runTo (σ := Plain) 0x8906 8).run s).2
  ((CPU.runTo (σ := Plain) 0x893c 26).run s).2

theorem row_body_spec (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 Smb.Buffer.Renderer.PointerIndex.code)
    (hh : CodeAt prg 0x08e2 Smb.Buffer.Renderer.PointerIndex.highLoadCode)
    (ht : CodeAt prg 0x0b0c Smb.Buffer.Renderer.PointerIndex.highTable)
    (hr : CodeAt prg 0x08e7 Smb.Buffer.Renderer.RestPrelude.code)
    (hp : CodeAt prg 0x08f9 Smb.Buffer.Renderer.TilePair.code)
    (ha : CodeAt prg 0x0906 Smb.Buffer.Renderer.AttributeTail.code)
    (hI : p &&& 4 ≠ 0) :
    let s : Plain := ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let out := rowBody s
    out.bad = false ∧ out.regs.pc = 0x893c ∧
      out.ram 0 = ram 0 + 2 ∧ out.ram 1 = x ∧
      out.regs.p &&& 4 ≠ 0 ∧ out.prg = prg := by
  have h := one_row_reaches_branch a x y sp p ram prg cyc hc hh ht hr hp ha hI
  dsimp only at h
  obtain ⟨hbad, hpc, h0, h1, _, hi, hprg⟩ := h
  simpa only [rowBody] using
    (show _ from ⟨hbad, hpc, h0, h1, hi, hprg⟩)

/-- For rows 0–11, add the ROM's branch back to the next row. -/
def rowNext (s : Plain) : Plain :=
  ((CPU.runTo (σ := Plain) 0x88d0 5).run (rowBody s)).2

def rowExit (s : Plain) : Plain :=
  ((CPU.runTo (σ := Plain) 0x8943 5).run (rowBody s)).2

set_option maxHeartbeats 3000000 in
theorem row_next_spec (a x y sp p : UInt8)
    (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x08d0 Smb.Buffer.Renderer.PointerIndex.code)
    (hh : CodeAt prg 0x08e2 Smb.Buffer.Renderer.PointerIndex.highLoadCode)
    (ht : CodeAt prg 0x0b0c Smb.Buffer.Renderer.PointerIndex.highTable)
    (hr : CodeAt prg 0x08e7 Smb.Buffer.Renderer.RestPrelude.code)
    (hp : CodeAt prg 0x08f9 Smb.Buffer.Renderer.TilePair.code)
    (ha : CodeAt prg 0x0906 Smb.Buffer.Renderer.AttributeTail.code)
    (hb : CodeAt prg 0x093c Smb.Buffer.Renderer.RendererLoopBranch.code)
    (hI : p &&& 4 ≠ 0) (hx : x < 12) :
    let s : Plain := ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := rowNext s
    t.bad = false ∧ t.regs.pc = 0x88d0 ∧
      t.regs.x = x + 1 ∧ t.ram 0 = ram 0 + 2 ∧
      t.ram 1 = x ∧ t.regs.p &&& 4 ≠ 0 ∧ t.prg = prg := by
  dsimp only [rowNext]
  have hbody := row_body_spec a x y sp p ram prg cyc hc hh ht hr hp ha hI
  dsimp only at hbody
  rcases midEq : rowBody ⟨⟨0x88d0, a, x, y, sp, p⟩, ram, prg, cyc, false⟩ with
    ⟨⟨pc', a', x', y', sp', p'⟩, ram', prg', cyc', bad'⟩
  rw [midEq] at hbody
  dsimp only at hbody
  obtain ⟨hbad, hpc, h0, h1, hi, hprg⟩ := hbody
  subst bad' pc' prg'
  have hrow : ram' 1 < 12 := h1 ▸ hx
  have hbranch := Smb.Buffer.Renderer.RendererLoopBranch.loops_before_last_row
    a' x' y' sp' p' ram' prg cyc' hb hi hrow
  have hseam := Smb.Buffer.Renderer.RendererLoopBranch.loop_seam
    a' x' y' sp' p' ram' prg cyc' hb hi hrow
  have hbranchI := Smb.Buffer.Renderer.RendererLoopBranch.loop_keeps_I
    a' x' y' sp' p' ram' prg cyc' hb hi hrow
  have hbranchP := Smb.Buffer.Renderer.RendererLoopBranch.loop_keeps_prg
    a' x' y' sp' p' ram' prg cyc' hb hi hrow
  dsimp only at hbranch hseam hbranchI hbranchP
  obtain ⟨hb2, hpc2, hx2⟩ := hbranch
  obtain ⟨h02, h12⟩ := hseam
  simpa only [midEq] using
    (show _ from ⟨hb2, hpc2, hx2.trans (congrArg (fun z => z + 1) h1),
      h02.trans h0, h12.trans h1, hbranchI, hbranchP⟩)

structure RowCode (prg : UInt16 → UInt8) : Prop where
  pre : CodeAt prg 0x08d0 Smb.Buffer.Renderer.PointerIndex.code
  high : CodeAt prg 0x08e2 Smb.Buffer.Renderer.PointerIndex.highLoadCode
  table : CodeAt prg 0x0b0c Smb.Buffer.Renderer.PointerIndex.highTable
  rest : CodeAt prg 0x08e7 Smb.Buffer.Renderer.RestPrelude.code
  tile : CodeAt prg 0x08f9 Smb.Buffer.Renderer.TilePair.code
  attr : CodeAt prg 0x0906 Smb.Buffer.Renderer.AttributeTail.code
  branch : CodeAt prg 0x093c Smb.Buffer.Renderer.RendererLoopBranch.code

def rom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

theorem row_code_in_rom : RowCode rom := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Smb.Buffer.Renderer.PointerIndex.code_in_rom
  · exact Smb.Buffer.Renderer.PointerIndex.highLoad_in_rom
  · exact Smb.Buffer.Renderer.PointerIndex.highTable_in_rom
  · exact Smb.Buffer.Renderer.RestPrelude.code_in_rom
  · exact Smb.Buffer.Renderer.TilePair.code_in_rom
  · exact Smb.Buffer.Renderer.AttributeTail.code_in_rom
  · exact Smb.Buffer.Renderer.RendererLoopBranch.code_in_rom

theorem row_next_state (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0) (hx : s.regs.x < 12) :
    let t := rowNext s
    t.bad = false ∧ t.regs.pc = 0x88d0 ∧
      t.regs.x = s.regs.x + 1 ∧ t.ram 0 = s.ram 0 + 2 ∧
      t.ram 1 = s.regs.x ∧ t.regs.p &&& 4 ≠ 0 ∧
      t.prg = s.prg ∧ RowCode t.prg := by
  rcases s with ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩
  dsimp only at hpc hbad hI hx hc
  subst pc bad
  have h := row_next_spec a x y sp p ram prg cyc
    hc.pre hc.high hc.table hc.rest hc.tile hc.attr hc.branch hI hx
  dsimp only at h
  obtain ⟨hb, hpc', hx', h0, h1, hi, hp⟩ := h
  refine ⟨hb, hpc', hx', h0, h1, hi, hp, ?_⟩
  simpa only [hp] using hc

/-- Repeated row transitions; each call follows the checked ROM fragments. -/
def rows : Nat → Plain → Plain
  | 0, s => s
  | n + 1, s => rows n (rowNext s)

def advanceX : Nat → UInt8 → UInt8
  | 0, x => x
  | n + 1, x => advanceX n (x + 1)

def advanceOffset : Nat → UInt8 → UInt8
  | 0, off => off
  | n + 1, off => advanceOffset n (off + 2)

theorem rows_spec (n : Nat) (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0)
    (hprefix : ∀ k, k < n → advanceX k s.regs.x < 12) :
    let t := rows n s
    t.bad = false ∧ t.regs.pc = 0x88d0 ∧
      t.regs.x = advanceX n s.regs.x ∧
      t.ram 0 = advanceOffset n (s.ram 0) ∧
      t.regs.p &&& 4 ≠ 0 ∧ t.prg = s.prg ∧ RowCode t.prg := by
  induction n generalizing s with
  | zero =>
      simpa only [rows, advanceX, advanceOffset] using
        (show s.bad = false ∧ s.regs.pc = 0x88d0 ∧
          s.regs.x = s.regs.x ∧ s.ram 0 = s.ram 0 ∧
          s.regs.p &&& 4 ≠ 0 ∧ s.prg = s.prg ∧ RowCode s.prg from
          ⟨hbad, hpc, rfl, rfl, hI, rfl, hc⟩)
  | succ n ih =>
      have hx : s.regs.x < 12 := by
        simpa only [advanceX] using hprefix 0 (Nat.zero_lt_succ n)
      have hs := row_next_state s hc hpc hbad hI hx
      dsimp only at hs
      obtain ⟨hb1, hpc1, hx1, h01, _, hi1, hp1, hc1⟩ := hs
      have hprefix1 : ∀ k, k < n → advanceX k (rowNext s).regs.x < 12 := by
        intro k hk
        have h := hprefix (k + 1) (Nat.succ_lt_succ hk)
        simpa only [advanceX, hx1] using h
      have hn := ih (rowNext s) hc1 hpc1 hb1 hi1 hprefix1
      dsimp only at hn
      obtain ⟨hbn, hpcn, hxn, hon, hin, hpn, hcn⟩ := hn
      change (rows n (rowNext s)).bad = false ∧
        (rows n (rowNext s)).regs.pc = 0x88d0 ∧
        (rows n (rowNext s)).regs.x = advanceX (n + 1) s.regs.x ∧
        (rows n (rowNext s)).ram 0 = advanceOffset (n + 1) (s.ram 0) ∧
        (rows n (rowNext s)).regs.p &&& 4 ≠ 0 ∧
        (rows n (rowNext s)).prg = s.prg ∧
        RowCode (rows n (rowNext s)).prg
      refine ⟨hbn, hpcn, ?_, ?_, hin, hpn.trans hp1, hcn⟩
      · simpa only [advanceX, hx1] using hxn
      · simpa only [advanceOffset, h01] using hon

theorem seven_rows_from_9c (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hoff : s.ram 0 = 0x9c) :
    let t := rows 7 s
    t.bad = false ∧ t.regs.pc = 0x88d0 ∧
      t.regs.x = 7 ∧ t.ram 0 = 0xaa ∧
      t.regs.p &&& 4 ≠ 0 ∧ t.prg = s.prg ∧ RowCode t.prg := by
  have hprefix : ∀ k, k < 7 → advanceX k s.regs.x < 12 := by
    intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
        k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hx, advanceX]
  have h := rows_spec 7 s hc hpc hbad hI hprefix
  dsimp only at h
  obtain ⟨hb, hpc', hx', hoff', hi, hp, hc'⟩ := h
  have heX : advanceX 7 (0 : UInt8) = 7 := by decide
  have heOff : advanceOffset 7 (0x9c : UInt8) = 0xaa := by decide
  rw [hx, heX] at hx'
  rw [hoff, heOff] at hoff'
  exact ⟨hb, hpc', hx', hoff', hi, hp, hc'⟩


theorem row_exit_state (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0) (hx : s.regs.x = 12) :
    let t := rowExit s
    t.bad = false ∧ t.regs.pc = 0x8943 ∧
      t.regs.x = 13 ∧ t.ram 0 = s.ram 0 + 2 ∧
      t.ram 1 = 12 := by
  rcases s with ⟨⟨pc, a, x, y, sp, p⟩, ram, prg, cyc, bad⟩
  dsimp only at hpc hbad hI hx hc
  subst pc bad x
  have hbody := row_body_spec a 12 y sp p ram prg cyc
    hc.pre hc.high hc.table hc.rest hc.tile hc.attr hI
  dsimp only at hbody
  rcases midEq : rowBody ⟨⟨0x88d0, a, 12, y, sp, p⟩, ram, prg, cyc, false⟩ with
    ⟨⟨pc', a', x', y', sp', p'⟩, ram', prg', cyc', bad'⟩
  rw [midEq] at hbody
  dsimp only at hbody
  obtain ⟨hb1, hpc1, h01, h11, hi1, hp1⟩ := hbody
  subst bad' pc' prg'
  have hexit := Smb.Buffer.Renderer.RendererLoopBranch.exits_after_last_row
    a' x' y' sp' p' ram' prg cyc' hc.branch hi1 h11
  have hseam := Smb.Buffer.Renderer.RendererLoopBranch.exit_seam
    a' x' y' sp' p' ram' prg cyc' hc.branch hi1 h11
  dsimp only at hexit hseam
  obtain ⟨hb2, hpc2, hx2⟩ := hexit
  obtain ⟨h02, h12⟩ := hseam
  simpa only [rowExit, midEq] using
    (show _ from ⟨hb2, hpc2, hx2, h02.trans h01, h12.trans h11⟩)


/-- The thirteen renderer rows, starting at row zero. The first twelve
    branches return to the loop; the last branch exits at `$8943`. -/
theorem thirteen_rows (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0) (hx : s.regs.x = 0) :
    let t := rowExit (rows 12 s)
    t.bad = false ∧ t.regs.pc = 0x8943 ∧
      t.regs.x = 13 ∧
      t.ram 0 = advanceOffset 12 (s.ram 0) + 2 ∧
      t.ram 1 = 12 := by
  have hprefix : ∀ k, k < 12 → advanceX k s.regs.x < 12 := by
    intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
        k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨
        k = 9 ∨ k = 10 ∨ k = 11 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hx, advanceX]
  have hrows := rows_spec 12 s hc hpc hbad hI hprefix
  dsimp only at hrows
  obtain ⟨hb, hpc', hx', hoff', hi, _, hc'⟩ := hrows
  have heX : advanceX 12 (0 : UInt8) = 12 := by decide
  rw [hx, heX] at hx'
  have hexit := row_exit_state (rows 12 s) hc' hpc' hb hi hx'
  dsimp only at hexit
  obtain ⟨heBad, hePc, heX', heOff, heSaved⟩ := hexit
  exact ⟨heBad, hePc, heX', heOff.trans (congrArg (fun x => x + 2) hoff'), heSaved⟩

theorem thirteen_rows_from_9c (s : Plain) (hc : RowCode s.prg)
    (hpc : s.regs.pc = 0x88d0) (hbad : s.bad = false)
    (hI : s.regs.p &&& 4 ≠ 0)
    (hx : s.regs.x = 0) (hoff : s.ram 0 = 0x9c) :
    let t := rowExit (rows 12 s)
    t.bad = false ∧ t.regs.pc = 0x8943 ∧
      t.regs.x = 13 ∧ t.ram 0 = 0xb6 ∧ t.ram 1 = 12 := by
  have h := thirteen_rows s hc hpc hbad hI hx
  dsimp only at h
  obtain ⟨hb, hp, hx', ho, hs⟩ := h
  have hoff' : advanceOffset 12 (0x9c : UInt8) + 2 = 0xb6 := by decide
  rw [hoff, hoff'] at ho
  exact ⟨hb, hp, hx', ho, hs⟩


end Smb.Buffer.Renderer.RowCompose
