import Smb.LocalBound.Range0

/-!
Second part of the optional local certificate: first bytes 86..171, every second
byte 0..255. Importing Range0 prevents these native checks from building in parallel.
-/
namespace Smb.LocalBound

theorem range86 : rangeCertificate entry 86 172 = true := by native_decide

end Smb.LocalBound
