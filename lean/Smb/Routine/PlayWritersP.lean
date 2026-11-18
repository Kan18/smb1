import Smb.Routine.PlayWritersDefs
import Smb.PlayFrameData

namespace Smb.Routine.PlayWriters

theorem okP : writersOk Smb.Abs.PlayFrame.P = true := by native_decide

end Smb.Routine.PlayWriters
