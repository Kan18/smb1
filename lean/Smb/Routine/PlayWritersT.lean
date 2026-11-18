import Smb.Routine.PlayWritersDefs
import Smb.PlayFrameData

namespace Smb.Routine.PlayWriters

theorem okT : writersOk Smb.Abs.PlayFrame.T = true := by native_decide

end Smb.Routine.PlayWriters
