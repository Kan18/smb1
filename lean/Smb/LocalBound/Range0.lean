import Smb.LocalBound.Check
import Smb.LocalBound.Entry

/-!
First part of the optional local certificate: first bytes 0..85, every second
byte 0..255. `native_decide` uses the project's existing compiler trust policy.
The later range modules import this one to keep their expensive checks sequential.
-/
namespace Smb.LocalBound

theorem range0 : rangeCertificate entry 0 86 = true := by native_decide

end Smb.LocalBound
