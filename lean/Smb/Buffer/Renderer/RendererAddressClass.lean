import Smb.Buffer.Renderer.RowCompose

/-!
Address classes for the 13 left/right tile pairs. These use the checked
`advanceOffset` recurrence from `RowCompose`; they classify indexed store
addresses, not tile values or legal input reachability.
-/
namespace Smb.Buffer.Renderer.RendererAddressClass

open Smb.Buffer.Renderer.RowCompose

def firstAddress (start : UInt8) (row : Nat) : UInt16 :=
  0x344 + (advanceOffset row start).toUInt16

def secondAddress (start : UInt8) (row : Nat) : UInt16 :=
  0x345 + (advanceOffset row start).toUInt16

def tileAddresses (start : UInt8) (address : UInt16) : Bool :=
  (List.range 13).any fun row =>
    (firstAddress start row == address) ||
      (secondAddress start row == address)

/-- A `$d6` start reaches Mario's vertical movement accumulator in the
right tile store of the final (twelfth) row. -/
theorem d6_final_right :
    secondAddress 0xd6 12 = 0x433 := by decide

/-- All byte starts whose 13 tile pairs address `$0433`. -/
theorem vertical_force_starts :
    ∀ start : Fin 256,
      tileAddresses (UInt8.ofNat start.val) 0x433 = true ↔
        (0xd6 ≤ start.val ∧ start.val ≤ 0xef) := by
  native_decide

/-- The corresponding class for Mario's fractional Y-position field. -/
theorem y_fraction_starts :
    ∀ start : Fin 256,
      tileAddresses (UInt8.ofNat start.val) 0x416 = true ↔
        (0xb9 ≤ start.val ∧ start.val ≤ 0xd2) := by
  native_decide

/-- The corresponding class for Mario's X subpixel field. -/
theorem x_fraction_starts :
    ∀ start : Fin 256,
      tileAddresses (UInt8.ofNat start.val) 0x400 = true ↔
        (0xa3 ≤ start.val ∧ start.val ≤ 0xbc) := by
  native_decide

/-- The corresponding class for the offscreen sprite-data control byte. -/
theorem sprite_control_starts :
    ∀ start : Fin 256,
      tileAddresses (UInt8.ofNat start.val) 0x3ee = true ↔
        (0x91 ≤ start.val ∧ start.val ≤ 0xaa) := by
  native_decide


end Smb.Buffer.Renderer.RendererAddressClass
