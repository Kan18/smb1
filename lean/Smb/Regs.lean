/-!
The 6502 registers and flag bits, on their own so that the natively compiled checker in `Smb.Abs`
can use them without depending on the machine model.
-/
namespace Smb

structure Regs where
  pc : UInt16
  a : UInt8
  x : UInt8
  y : UInt8
  s : UInt8
  p : UInt8
deriving Repr, DecidableEq, Inhabited

namespace CPU

def FC : UInt8 := 1
def FZ : UInt8 := 2
def FI : UInt8 := 4
def FD : UInt8 := 8
def FB : UInt8 := 16
def FU : UInt8 := 32
def FV : UInt8 := 64
def FN : UInt8 := 128

end CPU
end Smb
