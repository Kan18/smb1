import Smb.Game
import Smb.Data.Tas

/-!
HappyLee's TAS (TASVideos publication #1715) as model inputs. Kept out of `Smb.Game`, in the
`SmbMovies` library, so that regenerating movie data does not rebuild the routine proofs.
-/
namespace Smb

/-- The original movie bytes, retained for provenance. -/
def movieInputs : List UInt8 := (ofHex Data.tasHex).toList

/-- Hardware-model witness: remove the movie's first idle frame to align startup.
No gameplay input changes. This is a clock-origin conversion, not a speedup. -/
def tasInputs : List UInt8 := movieInputs.drop 1

end Smb
