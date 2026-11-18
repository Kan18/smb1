import Smb.Cpu

namespace Smb.CPU
variable {σ : Type} [Bus σ]

/-- Execute instructions until `pc = stop`, without executing the instruction there.
Stops after `fuel` instructions regardless. -/
def runTo (stop : UInt16) : Nat → StateM σ Unit
  | 0 => pure ()
  | n + 1 => do
    if (← getRegs).pc = stop then pure ()
    else do step; runTo stop n

end Smb.CPU
