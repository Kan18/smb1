import Smb.Routine.RunThrough
import Smb.Routine.PlayerFrameNes

/-!
# Small steps for splicing a checked region into a frame's run

* `runTo_more`: once a run has stopped, more fuel changes nothing, so a theorem about a run that reaches its stop can
  pick its own fuel.
* `codeAt_of_code`: a state the checker's `Code` describes has the ROM's bytes, so the summaries' `CodeAt` hypotheses
  hold for it.
* `rts_foot`, `rts_side1`, `rts_side2`: from `ImpedePlayerMove`'s RTS (`$DF8A`) back to `PlayerCtrlRoutine`
  (`$B15D`), one RTS at a time, with the stack the foot check's `jmp` or the side check's `jsr` left.
-/
namespace Smb.Abs
open Smb Smb.Routine

theorem runTo_more (B : UInt16) : ∀ (n k : Nat) (s : Plain), ((CPU.runTo (σ := Plain) B n).run s).2.regs.pc = B →
    ((CPU.runTo (σ := Plain) B (n + k)).run s).2 = ((CPU.runTo (σ := Plain) B n).run s).2 := by
  intro n
  induction n with
  | zero =>
    intro k s h
    rw [runTo_zero] at h ⊢
    simpa using runTo_at B k s h
  | succ n ih =>
    intro k s h
    by_cases hs : s.regs.pc = B
    · rw [runTo_at B _ s hs, runTo_at B _ s hs]
    · rw [runTo_succ B n s hs] at h ⊢
      rw [show n + 1 + k = (n + k) + 1 by omega, runTo_succ B (n + k) s hs]
      exact ih k _ h

theorem low_facts (a : UInt16) (ha : a < 0x8000) :
    0x8000 ≤ a + 0x8000 ∧ (a + 0x8000) &&& 0x7FFF = a ∧ a &&& 0x7FFF = a := by
  revert ha; bv_decide (config := { enums := false })

/-- The ROM as the plain machine reads it. -/
theorem code_low {u : Plain} (hc : Code (romOf Smb.prg) u) (a : UInt16) (ha : a.toNat < 0x8000) :
    u.prg a = romFn a := by
  have ha' : a < 0x8000 := UInt16.lt_iff_toNat_lt.mpr ha
  obtain ⟨e0, e1, e2⟩ := low_facts a ha'
  have h := hc (a + 0x8000) e0
  rw [e1] at h
  rw [h]
  show Smb.prg.get! ((a + 0x8000) &&& 0x7FFF).toNat = Smb.prg.get! (a &&& 0x7FFF).toNat
  rw [e1, e2]

theorem codeAt_of_code {u : Plain} (hc : Code (romOf Smb.prg) u) :
    ∀ (l : List UInt8) (start : UInt16), start.toNat + l.length ≤ 0x8000 → CodeAt romFn start l → CodeAt u.prg start l
  | [], _, _, _ => trivial
  | b :: bs, start, hl, ⟨h1, h2⟩ => by
    simp only [List.length_cons] at hl
    refine ⟨(code_low hc start (by omega)).trans h1, codeAt_of_code hc bs (start + 1) ?_ h2⟩
    have : (start + 1).toNat = start.toNat + 1 := by
      rw [UInt16.toNat_add]; simp only [UInt16.toNat_one]; omega
    omega

/-- A run with fuel 1 to a stop other than where it is: one step. -/
theorem runTo_one (B : UInt16) (s : Plain) (h : s.regs.pc ≠ B) :
    ((CPU.runTo (σ := Plain) B 1).run s).2 = (CPU.step.run s).2 := by
  rw [runTo_succ B 0 s h, runTo_zero]

theorem rom_rts1 : romFn 0x5F8A = 0x60 := by native_decide
theorem rom_rts2 : romFn 0x5E02 = 0x60 := by native_decide

set_option maxHeartbeats 4000000 in
/-- The foot check's impede: `ImpedePlayerMove`'s RTS returns from `PlayerBGCollision` to `$B15D`. -/
theorem rts_foot (a x y p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (hc : prg 0x5F8A = 0x60)
    (h0 : ram 0x1F6 = 0x5C) (h1 : ram 0x1F7 = 0xB1) (hI : p &&& 4 ≠ 0) :
    let t := ((CPU.runTo (σ := Plain) 0xB15D 1).run ⟨⟨0xDF8A, a, x, y, 0xF5, p⟩, ram, prg, cyc, false⟩).2
    t.regs.pc = 0xB15D ∧ t.regs.s = 0xF7 ∧ t.regs.p = p ∧ t.regs.a = a ∧ t.regs.x = x ∧ t.regs.y = y ∧
      t.ram = ram ∧ t.prg = prg ∧ t.bad = false := by
  dsimp only
  generalize hr : ((CPU.runTo (σ := Plain) 0xB15D 1).run ⟨⟨0xDF8A, a, x, y, 0xF5, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi, h0, h1] until 45405
  all_goals
    intros
    subst hr
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- The side check's impede: `ImpedePlayerMove`'s RTS returns to `StopPlayerMove`'s RTS (`$DE02`). -/
theorem rts_side1 (a x y p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (hc : prg 0x5F8A = 0x60)
    (h0 : ram 0x1F4 = 0x01) (h1 : ram 0x1F5 = 0xDE) (hI : p &&& 4 ≠ 0) :
    let t := ((CPU.runTo (σ := Plain) 0xDE02 1).run ⟨⟨0xDF8A, a, x, y, 0xF3, p⟩, ram, prg, cyc, false⟩).2
    t.regs.pc = 0xDE02 ∧ t.regs.s = 0xF5 ∧ t.regs.p = p ∧ t.regs.a = a ∧ t.regs.x = x ∧ t.regs.y = y ∧
      t.ram = ram ∧ t.prg = prg ∧ t.bad = false := by
  dsimp only
  generalize hr : ((CPU.runTo (σ := Plain) 0xDE02 1).run ⟨⟨0xDF8A, a, x, y, 0xF3, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi, h0, h1] until 56834
  all_goals
    intros
    subst hr
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- `StopPlayerMove`'s RTS (`$DE02`) returns from `PlayerBGCollision` to `$B15D`. -/
theorem rts_side2 (a x y p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64) (hc : prg 0x5E02 = 0x60)
    (h0 : ram 0x1F6 = 0x5C) (h1 : ram 0x1F7 = 0xB1) (hI : p &&& 4 ≠ 0) :
    let t := ((CPU.runTo (σ := Plain) 0xB15D 1).run ⟨⟨0xDE02, a, x, y, 0xF5, p⟩, ram, prg, cyc, false⟩).2
    t.regs.pc = 0xB15D ∧ t.regs.s = 0xF7 ∧ t.regs.p = p ∧ t.regs.a = a ∧ t.regs.x = x ∧ t.regs.y = y ∧
      t.ram = ram ∧ t.prg = prg ∧ t.bad = false := by
  dsimp only
  generalize hr : ((CPU.runTo (σ := Plain) 0xB15D 1).run ⟨⟨0xDE02, a, x, y, 0xF5, p⟩, ram, prg, cyc, false⟩).2 = t
  have hi : (p &&& 4 == 0) = false := beq_false_of_ne hI
  sym_run hr [hc, hi, h0, h1] until 45405
  all_goals
    intros
    subst hr
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Smb.Abs
