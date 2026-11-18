import Smb.Game
import Smb.Routine.AbsCheck
import Smb.Routine.RunThrough
import Smb.PlayerPreData
import Smb.PlayerPostData

/-!
# The player region around `PlayerCtrlRoutine` keeps Mario's horizontal state

The normal-play cycle's player region runs from the game logic's call (`$8175`) to its return into the engine
(`$AF01`), with `PlayerCtrlRoutine` (`$B0E9`–`$B179`) inside it. Its bounds don't relate one frame's position to the
last. These two checked plain-machine regions, built from its bounds and directives, show that nothing in it outside
the routine moves Mario: every bounded prefix keeps his X speed, position and sub-pixel, the screen edges,
`Platform_X_Scroll`, last frame's on-screen X and the side-collision timer.

* `pre_plain`: from the region's entry to `PlayerCtrlRoutine`.
* `post_plain`: from `PlayerHole` (`$B179`) to the return into the engine, unless Mario dies in a pit first (`$B1B8`).

So on a frame of normal play, the horizontal state changes only inside the routine, which `FrameCollision` bounds.
The entry conditions are hypotheses, as for the other regions: the shared bounds and the entry boxes' cells.
-/
namespace Smb.Routine.PlayerSplit
open Smb.Abs

theorem pre_accepted : PlayerPre.accepted Smb.prg = true := by native_decide
theorem post_accepted : PlayerPost.accepted Smb.prg = true := by native_decide

theorem pre_top : gAt PlayerPre.conf.globals 0x300 = .top := eq_top_of_topB (by native_decide)
theorem pre_top2 : gAt PlayerPre.conf.globals 0x340 = .top := eq_top_of_topB (by native_decide)
theorem post_top : gAt PlayerPost.conf.globals 0x300 = .top := eq_top_of_topB (by native_decide)
theorem post_top2 : gAt PlayerPost.conf.globals 0x340 = .top := eq_top_of_topB (by native_decide)

theorem pre_exit_eq : PlayerPre.conf.exit = [0xB1E5, 0xB0E9] := by native_decide
theorem post_exit_eq : PlayerPost.conf.exit = [0xB1B8, 0xAF01] := by native_decide

/-- Before the routine: every bounded prefix of the run to `$B0E9` stays in the invariant, which keeps the protected
cells, or it reached `VerticalPipeEntry` (`$B1E5`) first, where a frame after a pipe entry dispatches. -/
theorem pre_plain (s : Plain) (hc : Code (romOf Smb.prg) s) (e : Box) (he : e ∈ PlayerPre.conf.entries)
    (hh : Holds PlayerPre.conf.protFn PlayerPre.conf.globals s.ram e s) (n : Nat) :
    (Code (romOf Smb.prg) ((CPU.runTo (σ := Plain) 0xB0E9 n).run s).2 ∧
      Inv PlayerPre.conf.protFn PlayerPre.conf.globals s.ram (PlayerPre.conf.table Smb.prg)
        ((CPU.runTo (σ := Plain) 0xB0E9 n).run s).2) ∨
      ∃ k u, u.regs.pc = 0xB1E5 ∧ Code (romOf Smb.prg) u ∧
        Inv PlayerPre.conf.protFn PlayerPre.conf.globals s.ram (PlayerPre.conf.table Smb.prg) u ∧
        ((CPU.runTo (σ := Plain) 0xB0E9 n).run s).2 = ((CPU.runTo (σ := Plain) 0xB0E9 k).run u).2 := by
  have hacc := pre_accepted
  simp only [PlayerPre.accepted, Bool.and_eq_true, List.all_eq_true] at hacc
  obtain ⟨hchk, hin⟩ := hacc
  have hexit : ∀ a, PlayerPre.conf.exitFn a = true → a = 0xB0E9 ∨ a = 0xB1E5 := by
    intro a h
    simp only [Config.C.exitFn, pre_exit_eq, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
      beq_iff_eq] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  exact runTo_two_exits hchk pre_top pre_top2 0xB0E9 0xB1E5 hexit n s hc (inv_of_entry (hin e he) hh)

/-- After the routine: the run to `$AF01` stays in the invariant, or it reached a death in a pit first. -/
theorem post_plain (s : Plain) (hc : Code (romOf Smb.prg) s) (e : Box) (he : e ∈ PlayerPost.conf.entries)
    (hh : Holds PlayerPost.conf.protFn PlayerPost.conf.globals s.ram e s) (n : Nat) :
    Inv PlayerPost.conf.protFn PlayerPost.conf.globals s.ram (PlayerPost.conf.table Smb.prg)
        ((CPU.runTo (σ := Plain) 0xAF01 n).run s).2 ∨
      ∃ k u, u.regs.pc = 0xB1B8 ∧ ((CPU.runTo (σ := Plain) 0xAF01 n).run s).2 = ((CPU.runTo (σ := Plain) 0xAF01 k).run u).2 := by
  have hacc := post_accepted
  simp only [PlayerPost.accepted, Bool.and_eq_true, List.all_eq_true] at hacc
  obtain ⟨hchk, hin⟩ := hacc
  have hexit : ∀ a, PlayerPost.conf.exitFn a = true → a = 0xAF01 ∨ a = 0xB1B8 := by
    intro a h
    simp only [Config.C.exitFn, post_exit_eq, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
      beq_iff_eq] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases runTo_two_exits hchk post_top post_top2 0xAF01 0xB1B8 hexit n s hc (inv_of_entry (hin e he) hh) with h | ⟨k, u, hu, _, _, heq⟩
  · exact Or.inl h.2
  · exact Or.inr ⟨k, u, hu, heq⟩

end Smb.Routine.PlayerSplit
