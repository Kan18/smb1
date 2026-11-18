import Smb.Vertical
import Smb.Routine.FloorClip

/-!
# No floor clip on land without vines (in the abstract vertical model)

`Smb.Vertical` over-approximates the ways Mario's vertical state can evolve on land without
vines, once he has jumped (see its module doc): its reachable set starts from jumps, so falls at the area entry's gravity `$28` before the
first jump are outside it (seen in both movies; speed stays below 5 there, by `gravityVel_withinMax`, as an argument). Here: every state it can reach is in the computed set
`reachable`, which has no *skip* (a falling frame entering a metatile row at offset ≥ 5,
the condition of `floor_skip_iff`). The set is checked once by running it
(`native_decide`): it contains the jump starts, is closed under every move, and has no skip.

What is proved from the ROM so far for the moves: gravity (`gravity_eq`, from
`imposeGravity`), the gravity switch and position update (`jumpSwimSub_reach`), jump start
(`jumpPart_call`), the landing window (`chkFootMTile_reach`), landing (`landPlyr_reach`),
the three stomp paths (`stomp_reach`, `shellStomp_reach`, `demoteStomp_reach`), the `NYSpd` head bump (`headChk_reach`, which excludes
land frames with no block bouncing, even for a solid block; `footCheck_call` has no such gap),
the pieces of walking off (`groundFrame_reach` keeps the vertical state without a jump,
`bgPrologue_reach` switches to falling without touching it), the jumpspring's per-frame
effect (`jumpspring_reach`: ±2 px, the bounce speed). Still assumed from the disassembly:
the `BumpBlock`/`BrickShatter` head bumps, lifts, and that nothing else writes Mario's vertical state on land (a static
audit by name and a dynamic one over two movies support this; see NOTES).
-/
namespace Smb.Vertical

/-- The abstract gravity step is the proved routine's (`A = 0`, maximum 4). -/
theorem gravity_eq (down : UInt8) (v : UInt16) : gravity down v = Smb.Routine.gravityVel 0 down 0 4 v := by
  simp [gravity, Smb.Routine.gravityVel]

inductive Reach : Abs → Prop
  | start {s} : s ∈ jumps → Reach s
  | step {s t} : Reach s → t ∈ succs s → Reach t

theorem reachable_certified : certifies reachable = true := by native_decide

theorem mem_of_reach {s : Abs} (h : Reach s) : s ∈ reachable := by
  have hc := reachable_certified
  simp only [certifies, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hj, hall⟩ := hc
  induction h with
  | start hs => exact Std.HashSet.mem_iff_contains.mpr (hj _ hs)
  | step _ ht ih =>
    have := hall _ (Std.HashSet.mem_toList.mpr ih)
    simp only [Bool.not_eq_true'] at this
    exact Std.HashSet.mem_iff_contains.mpr (this.2 _ ht)

/-- **No skip.** In the abstract land model, no reachable row entry has row offset ≥ 5. This is not "Mario lands":
`succs` keeps a non-landing successor where `mayLand` holds, so Mario may fall on; and on the real machine a foot coin can return
before the landing test (TAS frame 6786). -/
theorem no_skip {s : Abs} (h : Reach s) : skipsWith s = false := by
  have hc := reachable_certified
  simp only [certifies, Bool.and_eq_true, List.all_eq_true] at hc
  have := hc.2 _ (Std.HashSet.mem_toList.mpr (mem_of_reach h))
  simp only [Bool.not_eq_true'] at this
  exact this.1

end Smb.Vertical
