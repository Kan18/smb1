import Smb.Routine.PlayWritersDefs
import Smb.PlayFrameData

namespace Smb.Routine.PlayWriters

theorem okZ : writersOk Smb.Abs.PlayFrame.Z = true := by native_decide

end Smb.Routine.PlayWriters
