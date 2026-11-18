import Smb.Game
import Smb.Routine.AbsCheck
import Smb.Routine.RunThrough
import Smb.Routine.CollisionX
import Smb.CollisionData

/-!
# Mario's horizontal state through `PlayerBGCollision`, every path

From `PlayerBGCollision`'s entry (`$DC64`, called from `PlayerCtrlRoutine` at `$B15A`) to its return at `$B15D`:
head hits, coins, landing, the foot and side checks, invisible and hidden blocks, jumpsprings. Every bounded prefix
keeps Mario's X speed, position and sub-pixel, the screen edges, `Platform_X_Scroll`, last frame's on-screen X and
the side-collision timer exactly as they were, until `ImpedePlayerMove` (`$DF4B`), the one thing here that moves him.
The other exits end the stretch of normal play: a pipe entry, the side pipe, the flag grab and climbing.

So a run from the entry that reaches `PlayerHole` (`$B179`) leaves the region through one of its exits
(`collision_through`), from a state with the horizontal bytes as they were at the entry; and at `ImpedePlayerMove`,
the stack holds one of two return chains (`impede_stack`), both of which lead back to `$B15D`.

The entry conditions are hypotheses: `Holds` at the entry box, which asks for the player region's global bounds (the
normal-play cycle's), the call chain's stack, and the buffer offsets `NoOverflow` allows at that point.
-/
namespace Smb.Routine.Collision
open Smb.Abs Smb.Abs.Collision

theorem acceptedAll_true : acceptedAll Smb.prg = true := by native_decide

theorem facts : check (romOf Smb.prg) conf.exitFn conf.protFn conf.globals (conf.table Smb.prg) = true ∧
    (∀ e ∈ conf.entries, entryIn conf.globals (conf.table Smb.prg) e = true) ∧
    (conf.table Smb.prg).at 0xB179 = [] ∧ (conf.table Smb.prg).at 0xAF01 = [] ∧
    (∀ b ∈ (conf.table Smb.prg).at 0xDF4B, impedeStack b = true) ∧
    (∀ b ∈ (conf.table Smb.prg).at 0xB15D, b.s = 0xF7 ∧ ∃ e ∈ PlayerPost.conf.entries, coverAfter conf.globals b e attrWritten = true) ∧
    (∀ b ∈ (conf.table Smb.prg).at 0xDF4B, ∃ e ∈ PlayerPost.conf.entries, coverAfter conf.globals b e impAttrWritten = true) := by
  have h := acceptedAll_true
  simp only [acceptedAll, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩ := h
  exact ⟨hA, hB, hC, hD, hE, hF, hG⟩

theorem globals_topB : topB (gAt conf.globals 0x300) = true := by native_decide
theorem globals_top : gAt conf.globals 0x300 = .top := eq_top_of_topB globals_topB
theorem globals_topB2 : topB (gAt conf.globals 0x340) = true := by native_decide
theorem globals_top2 : gAt conf.globals 0x340 = .top := eq_top_of_topB globals_topB2

theorem exit_eq : conf.exit = [0xDE88, 0xDE75, 0xDDFC, 0xB15D, 0xDF4B] := by native_decide

theorem exit_cases (a : UInt16) (h : conf.exitFn a = true) :
    a = 0xDF4B ∨ a = 0xB15D ∨ a = 0xDEFA ∨ a = 0xDDFC ∨ a = 0xDE75 ∨ a = 0xDE88 := by
  simp only [Config.C.exitFn, exit_eq, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h with h | h | h | h | h <;> subst h <;> simp

theorem p57 : conf.protFn 0x57 = true := by native_decide
theorem p86 : conf.protFn 0x86 = true := by native_decide
theorem p6d : conf.protFn 0x6D = true := by native_decide
theorem p400 : conf.protFn 0x400 = true := by native_decide
theorem p71a : conf.protFn 0x71A = true := by native_decide
theorem p71b : conf.protFn 0x71B = true := by native_decide
theorem p71c : conf.protFn 0x71C = true := by native_decide
theorem p71d : conf.protFn 0x71D = true := by native_decide
theorem p3a1 : conf.protFn 0x3A1 = true := by native_decide
theorem p755 : conf.protFn 0x755 = true := by native_decide
theorem p785 : conf.protFn 0x785 = true := by native_decide
theorem p705 : conf.protFn 0x705 = true := by native_decide

theorem cellIs_sound {prot : UInt16 → Bool} {g : Global} {ram0 : UInt16 → UInt8} {b : Box} {s : Plain}
    (h : Holds prot g ram0 b s) {a : UInt16} {v : UInt8} (hc : cellIs b a v = true) : s.ram a = v := by
  simp only [cellIs, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨i, w⟩, hm, hi, hw⟩ := hc
  have hmem := h.cells _ hm
  simp only at hi hmem hw
  subst hi
  cases w with
  | top => simp at hw
  | set l =>
    match l, hw, hmem with
    | [u], hw, hmem =>
      simp only [VS.mem, List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hmem hw
      rw [hmem, hw]
    | [], hw, _ => simp at hw
    | _ :: _ :: _, hw, _ => simp at hw

/-- **Through the collision code.** A run from a state the entry allows that reaches `PlayerHole` passes an exit,
from a state inside the region's invariant whose horizontal bytes are the entry's. -/
theorem collision_through (s : Plain) (hc : Code (romOf Smb.prg) s) (e : Box) (he : e ∈ conf.entries)
    (hh : Holds conf.protFn conf.globals s.ram e s) (n : Nat)
    (hp : ((CPU.runTo (σ := Plain) 0xB179 n).run s).2.regs.pc = 0xB179) :
    ∃ k u, conf.exitFn u.regs.pc = true ∧ Code (romOf Smb.prg) u ∧ Inv conf.protFn conf.globals s.ram (conf.table Smb.prg) u ∧
      ((CPU.runTo (σ := Plain) 0xB179 n).run s).2 = ((CPU.runTo (σ := Plain) 0xB179 k).run u).2 := by
  obtain ⟨hchk, hin, hB, _⟩ := facts
  exact runTo_through_exit hchk globals_top globals_top2 0xB179 hB n s hc (inv_of_entry (hin e he) hh) hp

/-- The same for a run to the player region's return into the engine (`$AF01`). -/
theorem collision_through_af01 (s : Plain) (hc : Code (romOf Smb.prg) s) (e : Box) (he : e ∈ conf.entries)
    (hh : Holds conf.protFn conf.globals s.ram e s) (n : Nat)
    (hp : ((CPU.runTo (σ := Plain) 0xAF01 n).run s).2.regs.pc = 0xAF01) :
    ∃ k u, conf.exitFn u.regs.pc = true ∧ Code (romOf Smb.prg) u ∧ Inv conf.protFn conf.globals s.ram (conf.table Smb.prg) u ∧
      ((CPU.runTo (σ := Plain) 0xAF01 n).run s).2 = ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  obtain ⟨hchk, hin, _, hB, _⟩ := facts
  exact runTo_through_exit hchk globals_top globals_top2 0xAF01 hB n s hc (inv_of_entry (hin e he) hh) hp

/-- At `ImpedePlayerMove`, the stack is one of the two the code builds. -/
theorem impede_stack {u : Plain} {ram0 : UInt16 → UInt8} (h : Inv conf.protFn conf.globals ram0 (conf.table Smb.prg) u)
    (hpc : u.regs.pc = 0xDF4B) :
    u.ram 0x1F6 = 0x5C ∧ u.ram 0x1F7 = 0xB1 ∧
      (u.regs.s = 0xF5 ∨ (u.regs.s = 0xF3 ∧ u.ram 0x1F4 = 0x01 ∧ u.ram 0x1F5 = 0xDE)) := by
  obtain ⟨b, hb, hh⟩ := h
  rw [hpc] at hb
  have hs := facts.2.2.2.2.1 b hb
  simp only [impedeStack, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨h6, h7⟩, hrest⟩ := hs
  refine ⟨cellIs_sound hh h6, cellIs_sound hh h7, ?_⟩
  rcases hrest with hs | ⟨⟨⟨hs, h4⟩, h5⟩⟩
  · exact Or.inl (hh.sp.trans hs)
  · exact Or.inr ⟨hh.sp.trans hs, cellIs_sound hh h4, cellIs_sound hh h5⟩

/-- The horizontal bytes at any state of the invariant are the entry's. -/
theorem kept {u : Plain} {ram0 : UInt16 → UInt8} (h : Inv conf.protFn conf.globals ram0 (conf.table Smb.prg) u) :
    u.ram 0x57 = ram0 0x57 ∧ u.ram 0x86 = ram0 0x86 ∧ u.ram 0x6D = ram0 0x6D ∧ u.ram 0x400 = ram0 0x400 ∧
      u.ram 0x71A = ram0 0x71A ∧ u.ram 0x71B = ram0 0x71B ∧ u.ram 0x71C = ram0 0x71C ∧ u.ram 0x71D = ram0 0x71D ∧
      u.ram 0x3A1 = ram0 0x3A1 ∧ u.ram 0x755 = ram0 0x755 ∧ u.ram 0x785 = ram0 0x785 := by
  obtain ⟨_, _, hh⟩ := h
  exact ⟨hh.frame _ p57, hh.frame _ p86, hh.frame _ p6d, hh.frame _ p400, hh.frame _ p71a, hh.frame _ p71b,
    hh.frame _ p71c, hh.frame _ p71d, hh.frame _ p3a1, hh.frame _ p755, hh.frame _ p785⟩

/-- `X_MoveForce`, the X speed's fraction, is kept too. -/
theorem kept705 {u : Plain} {ram0 : UInt16 → UInt8} (h : Inv conf.protFn conf.globals ram0 (conf.table Smb.prg) u) :
    u.ram 0x705 = ram0 0x705 := by
  obtain ⟨_, _, hh⟩ := h
  exact hh.frame _ p705

end Smb.Routine.Collision
