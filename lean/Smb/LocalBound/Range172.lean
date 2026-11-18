import Smb.LocalBound.Range86

/-!
Final part of the optional local certificate: first bytes 172..255, every second
byte 0..255. The import chain keeps all three native checks sequential.
-/
namespace Smb.LocalBound

theorem range172 : rangeCertificate entry 172 256 = true := by native_decide

end Smb.LocalBound
