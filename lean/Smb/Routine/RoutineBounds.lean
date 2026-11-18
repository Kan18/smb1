import Smb.Routine.PlayerCtrlLink
import Smb.CollisionBoundsData

/-!
# Every prefix of the player block's run, in a checked region

`block0` says what a run of the player block that *reaches* `$AF01` does. Relating it to the full NES needs more:
that every prefix of the plain run is not `bad`, so that `Sim` applies at whatever instant the NES gets there. Three
checked plain regions cover the block, linked end to end: `PlayerCtrl` (`$B0E9` to `$DC64`), `CollisionBounds`
(`$DC64` through the impede and the attribute update to `PlayerHole`, `$B179`, or a phase exit) and `PlayerPost`
(`$B179` to `$AF01` or a pit death).
-/
namespace Smb.Routine.RoutineBounds
open Smb Smb.Abs Smb.Routine

theorem bounds_accepted : CollisionBounds.accepted Smb.prg = true := by native_decide

/-- The links: the first region's boxes at `$DC64` inside the second's entry, the second's at `$B179` inside the
third's, each under bounds inside the next region's. -/
def links (prg : ByteArray) : Bool :=
  ((PlayerCtrl.conf.table prg).at 0xDC64).all
    (fun b => CollisionBounds.conf.entries.any (Box.le PlayerCtrl.conf.globals b)) &&
  ((CollisionBounds.conf.table prg).at 0xB179).all
    (fun b => PlayerPost.conf.entries.any (Box.le CollisionBounds.conf.globals b))

theorem links_true : links Smb.prg = true := by native_decide

end Smb.Routine.RoutineBounds
