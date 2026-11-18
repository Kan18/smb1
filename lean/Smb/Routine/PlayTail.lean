import Smb.Game
import Smb.PlayTailData

/-! A tail-region check, conditional on a separately carried parser tuple. -/
namespace Smb.Routine.PlayTail

theorem accepted : Smb.Abs.PlayTail.accepted Smb.prg = true := by native_decide

end Smb.Routine.PlayTail
