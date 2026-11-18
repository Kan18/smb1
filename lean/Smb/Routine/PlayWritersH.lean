import Smb.Routine.PlayWritersDefs
import Smb.PlayFrameData

namespace Smb.Routine.PlayWriters

theorem okH : writersOk Smb.Abs.PlayFrame.H = true := by native_decide

end Smb.Routine.PlayWriters
