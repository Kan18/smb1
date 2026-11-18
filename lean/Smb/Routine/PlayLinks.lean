import Smb.Game
import Smb.Routine.AbsBridge
import Smb.PlayFrameData
import Smb.CollisionData
import Smb.PlayerPostData

/-!
# From the player region to the regions inside it

The normal-play cycle's player region (`PlayFrame.P`) covers `PlayerCtrlRoutine` with bounds only. The collision
region (`Collision`) and the region after the routine (`PlayerPost`) give the relational facts there. These links
say that wherever the player region's invariant holds at their entries, theirs does too: every box of the player
region's table at `PlayerBGCollision` (`$DC64`) is inside the collision region's entry box, and every box at
`PlayerHole` (`$B179`) is inside the second region's, under the shared bounds, which are inside both regions' own.
-/
namespace Smb.Routine.PlayLinks
open Smb.Abs

/-- Both links, from one computation of the player region's table. -/
def linksOk (prg : ByteArray) : Bool :=
  let T := PlayFrame.P.tableWith PlayFrame.G prg
  (T.at 0xDC64).all (fun b => Collision.conf.entries.any (Box.le PlayFrame.G b)) &&
    (T.at 0xB179).all (fun b => PlayerPost.conf.entries.any (Box.le PlayFrame.G b))

theorem links_true : linksOk Smb.prg = true := by native_decide

/-- The shared bounds are inside `g'`'s at every cell. -/
def within (g' : Global) : Bool :=
  (List.range 0x800).all fun i => (List.range 256).all fun v =>
    !(gAt PlayFrame.G (UInt16.ofNat i)).mem (UInt8.ofNat v) || (gAt g' (UInt16.ofNat i)).mem (UInt8.ofNat v)

theorem within_collision : within Collision.conf.globals = true := by native_decide
theorem within_post : within PlayerPost.conf.globals = true := by native_decide
theorem size_collision : Collision.conf.globals.size = 0x800 := by native_decide
theorem size_post : PlayerPost.conf.globals.size = 0x800 := by native_decide

theorem widen {g' : Global} (hw : within g' = true) (hs : g'.size = 0x800) (i : UInt16) (v : UInt8)
    (h : (gAt PlayFrame.G i).mem v = true) : (gAt g' i).mem v = true := by
  by_cases hi : i.toNat < 0x800
  · have h1 := List.all_eq_true.mp hw i.toNat (List.mem_range.mpr hi)
    have h2 := List.all_eq_true.mp h1 v.toNat (List.mem_range.mpr v.toNat_lt)
    simp only [UInt16.ofNat_toNat, UInt8.ofNat_toNat, h, Bool.not_true, Bool.false_or] at h2
    exact h2
  · unfold gAt Array.getD
    rw [dif_neg (by omega)]
    rfl

end Smb.Routine.PlayLinks
