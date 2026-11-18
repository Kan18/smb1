import Smb.Game
import Smb.PlayParserData

/-! The cell groups `PlayWriters` checks, and the check, kept light so the per-region modules build early. -/
namespace Smb.Routine.PlayWriters
open Smb Smb.Abs Smb.Abs.Config

/-- A group of cells and the instructions allowed to write them. -/
structure Group where
  cells : UInt16 → Bool
  writers : List UInt16

def addrCtrl : Group := ⟨fun i => i == 0x773, [0x80DB, 0x89BF, 0x8A5D]⟩
def parserTask : Group := ⟨fun i => i == 0x71F, [0x92B7, 0x92BF]⟩
def floateyTimers : Group := ⟨fun i => 0x12C ≤ i && i ≤ 0x131, [0x84DB, 0xDA16]⟩
def gameTimerCtrl : Group := ⟨fun i => i == 0x787, [0x8113, 0xB788]⟩
/-- `FrameCounter`: the handler's `inc` (`NoDecTimers`). -/
def frameCounter : Group := ⟨fun i => i == 0x09, [0x8119]⟩
/-- `Player_Pos_ForScroll`: `RenderPlayerSub`'s copy. -/
def scrollPos : Group := ⟨fun i => i == 0x755, [0xEFC3]⟩
/-- `SideCollisionTimer`: the frame timers' countdown and `ImpedePlayerMove`. -/
def sideTimer : Group := ⟨fun i => i == 0x785, [0x8113, 0xDF68]⟩

def groups : List Group := [addrCtrl, parserTask, floateyTimers, gameTimerCtrl, frameCounter, scrollPos, sideTimer]

/-- A region's table with the group's cells protected and its writers as exits. -/
def groupOk (exit prot : UInt16 → Bool) (T : Table) (k : Group) : Bool :=
  checkF (romOf Smb.prg) (fun pc => exit pc || k.writers.contains pc) (fun i => prot i || k.cells i) PlayParser.G T

/-- Every group, on one computation of the region's table. -/
def writersOk (c : Config.C) : Bool :=
  let T := c.tableWith PlayParser.G Smb.prg
  groups.all (groupOk c.exitFn c.protFn T)

end Smb.Routine.PlayWriters
