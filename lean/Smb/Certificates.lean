import Smb.Game
import Smb.Tas

/-!
# Checks run on the model for routine-level certificates

Each replays a movie once. Not compiled (library `SmbMovies`): the loops here are interpreted,
but each step is a call to `NES.frame`, which runs natively from `Smb`.
-/
namespace Smb.Certificates

/-- In 8-3 the TAS spawns Hammer Bros (ID 5) at frames 13979, 14064, 14179, 14229 into slots
0, 1, 1, 2 whose `HammerBroJumpTimer` (`$3C+x`) already holds 161, 125, 54, 119. -/
def hammerCert : Bool := Id.run do
  let want : List (Nat × Nat × UInt8) := [(13979, 0, 161), (14064, 1, 125), (14179, 1, 54), (14229, 2, 119)]
  let mut s := initial
  let mut ok := true
  for k in [0:14230] do
    let s' := NES.frame (tasInputs.getD k 0) 0 s
    for (k', x, t) in want do
      if k == k' then
        let hb (n : NES) := n.ram.get! (0x0F + x) != 0 && n.ram.get! (0x16 + x) == 5
        ok := ok && !hb s && hb s' && s.ram.get! (0x3C + x) == t && s'.ram.get! (0x3C + x) == t &&
          s'.ram.get! 0x75F == 7 && s'.ram.get! 0x75C == 2
    s := s'
  return ok

end Smb.Certificates
