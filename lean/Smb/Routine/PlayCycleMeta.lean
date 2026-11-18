import Smb.Routine.PlaySavedHandoffs

/-! Finite wiring metadata for the normal-play region cycle. Open exits remain
explicit stop addresses; their unreachability is not asserted. -/
namespace Smb.Routine.PlayCycle
open Smb Smb.Abs PlaySavedHandoffs

def openExits : List UInt16 := [0xD958, 0x91BA, 0x9277, 0xB0D5, 0xB1B8, 0xB27A, 0xB8AA, 0xD948, 0xDDFC, 0xDE75, 0xDE86, 0xFAEF, 0x8031, 0x82CB, 0x82F2, 0x8483, 0x91E5, 0x9260, 0x927E, 0xDE15, 0x82CE, 0x82FD, 0x845D, 0x8475, 0x874E, 0x905D, 0x90C8, 0x91E0, 0x9233, 0x925A, 0x9279, 0xB218, 0xD009, 0xDE10, 0xB79A, 0xB1E5]
def stop (pc : UInt16) : Bool := openExits.contains pc

def directEdges : List (Config.C × List (UInt16 × Config.C)) :=
  [(PlayFrame.H, [(0x8178, PlayFrame.Z), (0x8175, PlayFrame.P)]),
   (PlayFrame.P, [(0xAF01, PlayEnemy.Front)]),
   (PlayEnemy.Front, [(0xAF05, PlayEnemy.E0)]),
   (PlayEnemy.E0, [(0xAF0B, PlayEnemy.M0)]),
   (PlayEnemy.M0, [(0xAF05, PlayEnemy.E1)]),
   (PlayEnemy.E1, [(0xAF0B, PlayEnemy.M1)]),
   (PlayEnemy.M1, [(0xAF05, PlayEnemy.E2)]),
   (PlayEnemy.E2, [(0xAF0B, PlayEnemy.M2)]),
   (PlayEnemy.M2, [(0xAF05, PlayEnemy.E3)]),
   (PlayEnemy.E3, [(0xAF0B, PlayEnemy.M3)]),
   (PlayEnemy.M3, [(0xAF05, PlayEnemy.E4)]),
   (PlayEnemy.E4, [(0xAF0B, PlayEnemy.M4)]),
   (PlayEnemy.M4, [(0xAF05, PlayEnemy.E5)]),
   (PlayEnemy.E5, [(0xAF0B, PlayEnemy.M5)]),
   (PlayEnemy.M5, [(0xAF10, PlayFrame.T)]),
   (PlayFrame.Z, [(0x808F, PlayFrame.H)])]

/-- Each direct edge enters a normal phase at a non-exit address. -/
theorem direct_wiring : directEdges.all (fun (c, es) =>
    c.exit.all (fun pc => stop pc || es.any (fun (q, d) => pc == q && !d.exitFn pc))) = true := by
  native_decide

/-- The two saved-tuple transitions are the only non-direct normal handoffs. -/
theorem tail_wiring : PlayFrame.T.exit.all (fun pc => stop pc || pc == 0xAF67) = true := by
  native_decide

theorem parser_wiring : PlayParser.chunks.all (fun c =>
    c.exit.all (fun pc => stop pc || pc == 0x8178)) = true := by native_decide

theorem idle_go : (normalConfigs ++ PlayParser.chunks).all (fun c =>
    !c.exitFn idlePC) = true := by native_decide

theorem parser_go : PlayParser.chunks.all (fun c => !c.exitFn 0xAF67) = true := by
  native_decide

theorem closing_go : PlayFrame.Z.exitFn 0x8178 = false := by native_decide

theorem closing_entries : PlayFrame.Z.entries.all (fun e => e.pc == 0x8178) = true := by
  native_decide

theorem closing_exit : PlayFrame.Z.exitFn 0x808F = true := by native_decide

end Smb.Routine.PlayCycle
