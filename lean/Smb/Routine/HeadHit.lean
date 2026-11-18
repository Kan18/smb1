import Smb.Game
import Smb.Routine.AbsCheck
import Smb.Routine.HorizontalLimit
import Smb.HeadHitData

/-!
# A head hit cannot disturb Mario's horizontal state

`PlayerHeadCollision` (`$BCED`), called from `HeadChk` when Mario's head bumps a block, to its return at `$DCE7`: the
block object's setup, the block-buffer and metatile writes, a brick's shatter and score, a coin block's coin and
score, a power-up or vine coming out. Every bounded prefix of that run keeps Mario's X speed, position and sub-pixel,
the screen edges, `Platform_X_Scroll`, last frame's on-screen X and the side-collision timer exactly as they were, and
stays on the plain machine. That's the first case of `HorizontalLimit.BgX`, so a head hit is one more way through the
collision code that keeps the 2.5-pixel limit.

The entry conditions are hypotheses: `Holds` at an entry box, which asks for the player region's global bounds (the
normal-play cycle's), the call chain's stack, the block-buffer pointer `BlockBufferColli_Head` leaves, and the buffer
offsets `NoOverflow` allows at that point. It does not assert that `$DCE7` is reached.
-/
namespace Smb.Routine.HeadHit
open Smb.Abs Smb.Abs.HeadHit

theorem accepted_true : accepted Smb.prg = true := by native_decide

theorem globals_topB : topB (gAt conf.globals 0x300) = true := by native_decide
theorem globals_top : gAt conf.globals 0x300 = .top := eq_top_of_topB globals_topB
theorem globals_topB2 : topB (gAt conf.globals 0x340) = true := by native_decide
theorem globals_top2 : gAt conf.globals 0x340 = .top := eq_top_of_topB globals_topB2

theorem exit_eq : conf.exit = [0xDCE7] := by native_decide

theorem exit_only (a : UInt16) (h : conf.exitFn a = true) : a = 0xDCE7 := by
  simp only [Config.C.exitFn, exit_eq, List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at h
  exact h

/-- The cells it keeps: the horizontal bytes `HorizontalLimit` reads. -/
theorem prot_cells : [0x57, 0x86, 0x6D, 0x400, 0x71A, 0x71B, 0x71C, 0x71D, 0x3A1, 0x755, 0x785].all
    (fun i : UInt16 => conf.protFn i) = true := by native_decide

/-- The head hit on the plain machine: every bounded prefix keeps the protected cells and the region's bounds. -/
theorem head_plain (s : Plain) (hc : Code (romOf Smb.prg) s) (e : Box) (he : e ∈ conf.entries)
    (hh : Holds conf.protFn conf.globals s.ram e s) (n : Nat) :
    let t := ((CPU.runTo (σ := Plain) 0xDCE7 n).run s).2
    t.bad = false ∧ (∀ i, conf.protFn i = true → t.ram i = s.ram i) ∧ (∀ i, (gAt conf.globals i).mem (t.ram i) = true) := by
  have hacc := accepted_true
  simp only [accepted, Bool.and_eq_true, List.all_eq_true] at hacc
  obtain ⟨hchk, hin⟩ := hacc
  have hinv := inv_of_entry (hin e he) hh
  have hrun := inv_runTo hchk globals_top globals_top2 0xDCE7 exit_only n s hc hinv
  obtain ⟨_, b, _, hb⟩ := hrun
  exact ⟨hb.bad, hb.frame, hb.glob⟩

/-- So a head hit is `BgX`'s first case: no horizontal move, the speed kept. -/
theorem head_bgX (s : Plain) (hc : Code (romOf Smb.prg) s) (e : Box) (he : e ∈ conf.entries)
    (hh : Holds conf.protFn conf.globals s.ram e s) (n : Nat) :
    HorizontalLimit.BgX s.ram ((CPU.runTo (σ := Plain) 0xDCE7 n).run s).2.ram := by
  obtain ⟨_, hk, _⟩ := head_plain s hc e he hh n
  have hp := prot_cells
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hp
  obtain ⟨h57, h86, h6d, h400, _⟩ := hp
  refine ⟨hk _ h400, Or.inl ⟨?_, hk _ h57⟩⟩
  simp only [HorizontalLimit.pixelP, hk _ h86, hk _ h6d]

end Smb.Routine.HeadHit
