namespace Smb

@[inline] def hexNibble (c : UInt8) : UInt8 :=
  if c ≤ 57 then c - 48 else c - 87  -- '0'..'9', 'a'..'f'

/-- Decode a lowercase hex string into bytes. -/
def ofHex (str : String) : ByteArray := Id.run do
  let b := str.toUTF8
  let mut out := ByteArray.empty
  for i in [0:b.size / 2] do
    out := out.push ((hexNibble (b.get! (2 * i)) <<< 4) ||| hexNibble (b.get! (2 * i + 1)))
  return out

end Smb
