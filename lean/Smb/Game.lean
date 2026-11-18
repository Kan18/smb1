import Smb.Nes
import Smb.Hex
import Smb.Data.Rom

/-!
Super Mario Bros. on the NES model: the cartridge, the initial state, and what it means
for the game to be beaten.
-/
namespace Smb

def rom : ByteArray := ofHex Data.romHex
def prg : ByteArray := rom.extract 0 0x8000
def chr : ByteArray := rom.extract 0x8000 0xA000

/-- Power-on followed by a soft reset before frame 0 (the convention of the TAS movie). -/
def initial : NES := (NES.power prg chr).reset

/-- `OperMode` ($0770); value 2 is the victory sequence for any castle. -/
def operMode (s : NES) : UInt8 := s.ram.get! 0x770

/-- Final-castle victory, rather than the victory sequence in an earlier world.
World and level numbers in RAM are zero-indexed. This is the project's finish convention;
it does not yet characterize every possible glitch-induced ending. -/
def finalVictory (s : NES) : Bool :=
  operMode s == 2 && s.ram.get! 0x75f == 7 && s.ram.get! 0x75c == 3

/-- Running `inputs` (one controller-1 byte per frame, controller 2 idle) from the fixed
initial state ends in final-castle victory without firing an implemented support guard. -/
def beatenBy (inputs : List UInt8) : Prop :=
  let s := NES.runFrames inputs initial
  finalVictory s = true ∧ s.unmodelled = false

/-- A prospective lower bound must exclude unsupported executions as well as victories.
An unsupported execution is unresolved, never evidence that an input cannot win.
This statement concerns this model; hardware equivalence is a separate obligation. -/
def LowerBound (frames : Nat) : Prop :=
  ∀ inputs : List UInt8, inputs.length < frames →
    let s := NES.runFrames inputs initial
    finalVictory s = false ∧ s.unmodelled = false

end Smb
