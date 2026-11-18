import Smb.Routine.Common

/-! The climbable-metatile test, shared by the foot check (`Landing`) and the side check
(`SideCheck`). -/
namespace Smb.Routine

/-- `ClimbMTileUpperExt` (`$DF96`): per palette (bits 7–6 of the metatile), the first metatile
that counts as climbable (or not solid): `$24`, `$6D`, `$8A`, `$C6`. -/
def climbExt (t : UInt8) : UInt8 :=
  bif t < 0x40 then 0x24 else bif t < 0x80 then 0x6D else bif t < 0xC0 then 0x8A else 0xC6

/-- Metatiles from the climbable ones of their group upward (`CheckForClimbMTiles`). -/
def climbable (t : UInt8) : Bool := decide (climbExt t ≤ t)

end Smb.Routine
