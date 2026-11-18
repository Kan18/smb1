import Smb.Buffer.Renderer.RendererAddressClass

/-!
Exact indexed address families of the two area-renderer paths in the
validated SMB1 ROM. `graphics` covers three command-header stores, thirteen
tile pairs, and the terminator. `attributes` covers seven four-byte entries
and its terminator. The saved byte index increments modulo 256, while each
absolute indexed store adds that byte to its own base address.

These address predicates classify stores conditional on reaching the ordinary
ROM loop. They do not assert a legal controller source for `$0340` or that a
later gameplay routine reads the changed byte.
-/
namespace Smb.Buffer.Renderer.GeneralAddressClasses

def graphicsHits (start address : Nat) : Bool :=
  address == 0x341 + start ||
  address == 0x342 + start ||
  address == 0x343 + start ||
  ((List.range 13).any fun row =>
    let index := (start + 2 * row) % 256
    address == 0x344 + index || address == 0x345 + index) ||
  address == 0x341 + ((start + 29) % 256)

def attributesHits (start address : Nat) : Bool :=
  ((List.range 7).any fun row =>
    let index := (start + 4 * row) % 256
    address == 0x341 + index || address == 0x342 + index ||
    address == 0x343 + index || address == 0x344 + index) ||
  address == 0x341 + ((start + 28) % 256)

def graphicsAddresses (start : Nat) : List Nat :=
  [0x341 + start, 0x342 + start, 0x343 + start] ++
  ((List.range 13).flatMap fun row =>
    let index := (start + 2 * row) % 256
    [0x344 + index, 0x345 + index]) ++
  [0x341 + ((start + 29) % 256)]

def attributeAddresses (start : Nat) : List Nat :=
  ((List.range 7).flatMap fun row =>
    let index := (start + 4 * row) % 256
    [0x341 + index, 0x342 + index, 0x343 + index, 0x344 + index]) ++
  [0x341 + ((start + 28) % 256)]

/- A target in this band receives at most one indexed store during one
ordinary renderer call, so the field's ROM value is unambiguous. -/
theorem graphics_unique_in_band : ∀ address : Fin 0xdd,
    ∀ start : Fin 256,
      ((graphicsAddresses start.val).filter
        (· == 0x360 + address.val)).length ≤ 1 := by native_decide

theorem attributes_unique_in_band : ∀ address : Fin 0xdd,
    ∀ start : Fin 256,
      ((attributeAddresses start.val).filter
        (· == 0x360 + address.val)).length ≤ 1 := by native_decide

/- Exhaustive classification for every byte in the gameplay-state band,
not just selected labels. `0xdd` addresses cover `$0360..$043c`. -/
theorem every_graphics_address_in_band : ∀ address : Fin 0xdd,
    ∀ start : Fin 256,
      graphicsHits start.val (0x360 + address.val) = true ↔
        (0x360 + address.val) - 0x35e ≤ start.val ∧
        start.val ≤ (0x360 + address.val) - 0x341 := by native_decide

theorem every_attribute_address_in_band : ∀ address : Fin 0xdd,
    ∀ start : Fin 256,
      attributesHits start.val (0x360 + address.val) = true ↔
        (0x360 + address.val) - 0x35d ≤ start.val ∧
        start.val ≤ (0x360 + address.val) - 0x341 := by native_decide

theorem bowser_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x363 = true ↔
      0x05 ≤ start.val ∧ start.val ≤ 0x22 := by native_decide
theorem bowser_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x363 = true ↔
      0x06 ≤ start.val ∧ start.val ≤ 0x22 := by native_decide

theorem firebar_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x388 = true ↔
      0x2a ≤ start.val ∧ start.val ≤ 0x47 := by native_decide
theorem firebar_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x388 = true ↔
      0x2b ≤ start.val ∧ start.val ≤ 0x47 := by native_decide

theorem vine_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x399 = true ↔
      0x3b ≤ start.val ∧ start.val ≤ 0x58 := by native_decide
theorem vine_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x399 = true ↔
      0x3c ≤ start.val ∧ start.val ≤ 0x58 := by native_decide

theorem hammer_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x3a2 = true ↔
      0x44 ≤ start.val ∧ start.val ≤ 0x61 := by native_decide
theorem hammer_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x3a2 = true ↔
      0x45 ≤ start.val ∧ start.val ≤ 0x61 := by native_decide

theorem offscreen_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x3d8 = true ↔
      0x7a ≤ start.val ∧ start.val ≤ 0x97 := by native_decide
theorem offscreen_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x3d8 = true ↔
      0x7b ≤ start.val ∧ start.val ≤ 0x97 := by native_decide

theorem block_metatile_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x3e8 = true ↔
      0x8a ≤ start.val ∧ start.val ≤ 0xa7 := by native_decide
theorem block_metatile_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x3e8 = true ↔
      0x8b ≤ start.val ∧ start.val ≤ 0xa7 := by native_decide

theorem sprite_control_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x3ee = true ↔
      0x90 ≤ start.val ∧ start.val ≤ 0xad := by native_decide
theorem sprite_control_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x3ee = true ↔
      0x91 ≤ start.val ∧ start.val ≤ 0xad := by native_decide

theorem x_fraction_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x400 = true ↔
      0xa2 ≤ start.val ∧ start.val ≤ 0xbf := by native_decide
theorem x_fraction_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x400 = true ↔
      0xa3 ≤ start.val ∧ start.val ≤ 0xbf := by native_decide

theorem y_fraction_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x416 = true ↔
      0xb8 ≤ start.val ∧ start.val ≤ 0xd5 := by native_decide
theorem y_fraction_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x416 = true ↔
      0xb9 ≤ start.val ∧ start.val ≤ 0xd5 := by native_decide

theorem y_force_graphics : ∀ start : Fin 256,
    graphicsHits start.val 0x433 = true ↔
      0xd5 ≤ start.val ∧ start.val ≤ 0xf2 := by native_decide
theorem y_force_attributes : ∀ start : Fin 256,
    attributesHits start.val 0x433 = true ↔
      0xd6 ≤ start.val ∧ start.val ≤ 0xf2 := by native_decide

/- The indexed status and block records use buffer-1 data base `$0301`.
At ordinary, nonwrapping offsets, these are the unique first-low alignments. -/
theorem first_block_low_at_340 (start : Nat) :
    0x301 + start + 1 = 0x340 ↔ start = 0x3e := by omega

theorem second_block_low_at_340 (start : Nat) :
    0x301 + start + 6 = 0x340 ↔ start = 0x39 := by omega

theorem status_terminator_at_340 (start : Nat) :
    0x301 + start + 14 = 0x340 ↔ start = 0x31 := by omega

theorem block_terminator_at_340 (start : Nat) :
    0x301 + start + 10 = 0x340 ↔ start = 0x35 := by omega

theorem palette_terminator_at_340 (start : Nat) :
    0x301 + start + 7 = 0x340 ↔ start = 0x38 := by omega

theorem timer_terminator_at_340 (start : Nat) :
    0x301 + start + 6 = 0x340 ↔ start = 0x39 := by omega

theorem start20_graphics_length_hits_bowser :
    0x343 + 0x20 = 0x363 := by decide

theorem start20_attribute_length_hits_bowser :
    0x343 + ((0x20 + 4 * 0) % 256) = 0x363 := by decide

theorem start90_graphics_terminator_hits_sprite_control :
    0x341 + ((0x90 + 29) % 256) = 0x3ee := by decide

theorem startd6_attribute_terminator_hits_mario_force :
    0x341 + ((0xd6 + 28) % 256) = 0x433 := by decide

/- `$030a` is the highest absolute-indexed base in the ordinary,
unguarded block appender; a byte index cannot reach Mario's Y fraction. -/
theorem block_appender_max (index : Fin 256) :
    0x30a + index.val ≤ 0x409 := by omega


end Smb.Buffer.Renderer.GeneralAddressClasses
