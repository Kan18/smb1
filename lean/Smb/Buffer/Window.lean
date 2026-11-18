import Smb.Buffer.StatusUpdate
import Smb.Buffer.BlockRecord
import Smb.Buffer.PaletteRecord
import Smb.Buffer.RenderAttribute
import Smb.Buffer.ColumnEnds
import Smb.Buffer.Digits.DigitInvariant

/-!
# Layer B: what a window of buffer-1 records can do

Layer A gives each record's bytes from the ROM. Given facts about the level (Layer C, taken here as hypotheses on
the RAM a record reads), this shows by computation:

* **Fields.** Every byte of every record that ordinary 1-1 surface play appends is below `$80`: the score/coin
  update with digits below `$80`, the timer, a block on one of the surface's hittable rows, and the player palette with
  its background index below 8. `ColorRotation` appends only below offset `$31` (`crotActive`), so its record,
  `$FF`s included, ends before `$0340`.
* **`$0340`.** A buffer-1 store reaches `$0340` only as one of those fields, so if that's where `$0340` gets its
  value, the value is below `$80`.
* **Relocation.** For a buffer-2 offset below `$80`, every store of a column or attribute record lands in
  `$0341`–`$03DD`: short of the block objects (`$03E4`–`$03F1`), `SprDataOffset_Ctrl` (`$03EE`),
  `AttributeBuffer` and Mario's sub-pixels.
* **Size.** A window's offset is the sum of its records' advances; with Layer C's per-window counts that's at most
  `14 u + 10 b + 6 t + 7 p + 7 c`.

The hypotheses are exactly what Layer C must prove for 1-1, and the rows are the surface's: block-buffer rows 3,
6, 7 and 10, which put `$30`, `$60`, `$70` or `$A0` in the row offset `$02`.
-/
namespace Smb.Buffer

/-- Every byte of a record is below `$80`. -/
def Low (fs : List UInt8) : Prop := ∀ b ∈ fs, b < 0x80

theorem low_cons {b : UInt8} {fs : List UInt8} (hb : b < 0x80) (h : Low fs) : Low (b :: fs) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  · exact h x hx

theorem low_nil : Low [] := fun _ h => absurd h (List.not_mem_nil)

/-- Turn `Low` of a literal list into one goal per byte, and close each from the hypotheses or by computation. -/
macro "low_tac" : tactic => `(tactic| (
  simp only [Low, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals first | assumption | decide | bv_decide))

/-- What a displayed digit needs for its record to stay low: below `$80`. Decimal play keeps digits 0–9, and
`Digits.DigitMath` proves from the ROM that a `DigitsMathRoutine` store is at most `$75` whatever the old digit
and the amount added, which is enough. -/
def Digit (d : UInt8) : Prop := d < 0x80

theorem digit_low {d : UInt8} (h : Digit d) : d < 0x80 := h

/-- The bound `DigitMath` proves for every `DigitsMathRoutine` store, and `DigitInvariant` keeps over a trace of
digit events, is enough for `Digit`. -/
theorem digit_of_le75 {d : UInt8} (h : d ≤ 0x75) : Digit d := by
  unfold Digit; bv_decide

theorem digit_of_good {ds : Digits.DigitInvariant.Digits} (h : Digits.DigitInvariant.Good ds) (i : Fin 36) :
    Digit (ds i) :=
  digit_of_le75 (h i)

/-- The score/coin update's fields are low when its eight digits are digits. -/
theorem upd1Fields_low (ram : UInt16 → UInt8)
    (hd : ∀ a ∈ [0x7ED, 0x7EE, 0x7DD, 0x7DE, 0x7DF, 0x7E0, 0x7E1, 0x7E2], Digit (ram a)) :
    Low (upd1Fields ram) := by
  have h := fun a (ha : a ∈ [(0x7ED : UInt16), 0x7EE, 0x7DD, 0x7DE, 0x7DF, 0x7E0, 0x7E1, 0x7E2]) => digit_low (hd a ha)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [upd1Fields]
  low_tac

theorem upd2Fields_low (ram : UInt16 → UInt8)
    (hd : ∀ a ∈ [0x7F3, 0x7F4, 0x7E3, 0x7E4, 0x7E5, 0x7E6, 0x7E7, 0x7E8], Digit (ram a)) :
    Low (upd2Fields ram) := by
  have h := fun a (ha : a ∈ [(0x7F3 : UInt16), 0x7F4, 0x7E3, 0x7E4, 0x7E5, 0x7E6, 0x7E7, 0x7E8]) => digit_low (hd a ha)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [upd2Fields]
  low_tac

/-- The timer record's fields are low when its three digits are digits. -/
theorem st5Fields_low (ram : UInt16 → UInt8) (hd : ∀ a ∈ [0x7F8, 0x7F9, 0x7FA], Digit (ram a)) :
    Low (st5Fields ram) := by
  have h := fun a (ha : a ∈ [(0x7F8 : UInt16), 0x7F9, 0x7FA]) => digit_low (hd a ha)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  simp only [st5Fields]
  low_tac

/-- The row offsets of 1-1's hittable blocks: block-buffer rows 3, 6, 7 and 10. -/
def SurfaceRow (r2 : UInt8) : Prop := r2 = 0x30 ∨ r2 = 0x60 ∨ r2 = 0x70 ∨ r2 = 0xA0

theorem blockLo_low {r2 : UInt8} (h : SurfaceRow r2) (r6 : UInt8) :
    blockLo r2 r6 < 0x80 ∧ blockLo r2 r6 + 0x20 < 0x80 := by
  rcases h with rfl | rfl | rfl | rfl <;> (unfold blockLo; bv_decide)

theorem blockHi_low (r2 r6 : UInt8) : blockHi r2 r6 < 0x80 := by
  unfold blockHi blockLo; bv_decide

set_option maxHeartbeats 4000000 in
/-- A block record on a surface row has only low fields, whatever its kind. -/
theorem blkFields_low (ram : UInt16 → UInt8) (h : SurfaceRow (ram 2)) :
    Low (blk0Fields ram) ∧ Low (blk1Fields ram) ∧ Low (blk2Fields ram) ∧ Low (blk3Fields ram) := by
  obtain ⟨hl, hl2⟩ := blockLo_low h (ram 6)
  have hh := blockHi_low (ram 2) (ram 6)
  simp only [blk0Fields, blk1Fields, blk2Fields, blk3Fields]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> low_tac

/-- The player palette's fields are low when its background index is below 8 and the ROM's `BackgroundColors` are
low there (`bgColors_low` checks the game's ROM). -/
theorem pcolFields_low (ram prg : UInt16 → UInt8)
    (htab : ∀ i : UInt8, i < 8 → prg ((0x85CF + i.toUInt16) &&& 0x7FFF) < 0x80)
    (hidx : (bif ram 0x744 == 0 then ram 0x74E else ram 0x744) < 8) :
    Low (pcolFields ram prg) := by
  have hb : (bif ram 0x744 == 0 then prg ((0x85CF + (ram 0x74E).toUInt16) &&& 0x7FFF)
      else prg ((0x85CF + (ram 0x744).toUInt16) &&& 0x7FFF)) < 0x80 := by
    cases h : ram 0x744 == 0 <;> simp only [h, Bool.cond_true, Bool.cond_false] at hidx ⊢ <;> exact htab _ hidx
  intro b hb'
  simp only [pcolFields, List.mem_cons, List.not_mem_nil, or_false] at hb'
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · exact hb
  · cases ram 0x756 == 2 <;> cases ram 0x753 == 0 <;> decide
  · decide
  · cases ram 0x756 == 2 <;> cases ram 0x753 == 0 <;> decide
  · decide

/-- The game's ROM as the CPU reads it. -/
def gameRom (a : UInt16) : UInt8 := Smb.prg.get! (a &&& 0x7fff).toNat

/-- `BackgroundColors`, the eight bytes at `$85CF`, are all below `$80` on the game's ROM. -/
theorem bgColors_low : ∀ i : UInt8, i < 8 → gameRom ((0x85CF + i.toUInt16) &&& 0x7FFF) < 0x80 := by
  have h : (List.range 8).all (fun n =>
      decide (gameRom ((0x85CF + (UInt8.ofNat n).toUInt16) &&& 0x7FFF) < 0x80)) = true := by
    native_decide
  intro i hi
  have hn : i.toNat < 8 := by simpa [UInt8.lt_iff_toNat_lt] using hi
  have := List.all_eq_true.mp h i.toNat (List.mem_range.mpr hn)
  simpa only [UInt8.ofNat_toNat, decide_eq_true_eq] using this

/-- On the game's ROM, the player palette's fields are low whenever its background index is below 8. -/
theorem pcolFields_low_rom (ram : UInt16 → UInt8) (hidx : (bif ram 0x744 == 0 then ram 0x74E else ram 0x744) < 8) :
    Low (pcolFields ram gameRom) :=
  pcolFields_low ram gameRom bgColors_low hidx

/-- `ColorRotation` writes only below offset `$31`, and its 8-byte record then ends at `$0338`: it never reaches
`$0340`, whatever its bytes. -/
theorem crot_short (ram : UInt16 → UInt8) (ha : crotActive ram = true) (k : UInt16) (hk : k < 8) :
    0x301 + (ram 0x300).toUInt16 + k < 0x340 := by
  simp only [crotActive, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
  generalize ram 0x300 = o at *
  bv_decide

/-! ## Relocation from a low buffer-2 offset -/

/-- Every store of the column record, for offset `v`: the header and terminator, and both tiles of each row. -/
def columnStores (v : UInt8) : List UInt16 :=
  [0x341 + v.toUInt16, 0x342 + v.toUInt16, 0x343 + v.toUInt16, 0x341 + (v + 29).toUInt16] ++
    (List.range 13).flatMap fun r =>
      [0x344 + (v + (2 * r).toUInt8).toUInt16, 0x345 + (v + (2 * r).toUInt8).toUInt16]

/-- Every store of the attribute record, for offset `v`: four bytes per row and the terminator. -/
def attributeStores (v : UInt8) : List UInt16 :=
  (0x341 + (v + 28).toUInt16) :: (List.range 7).flatMap fun r =>
    [0x341 + (v + (4 * r).toUInt8).toUInt16, 0x342 + (v + (4 * r).toUInt8).toUInt16,
     0x343 + (v + (4 * r).toUInt8).toUInt16, 0x344 + (v + (4 * r).toUInt8).toUInt16]

/-- From an offset below `$80`, both renderers write only in `$0341`–`$03DD`. -/
theorem relocation_reach : ∀ v : UInt8, v < 0x80 →
    (∀ a ∈ columnStores v, 0x341 ≤ a ∧ a ≤ 0x3DD) ∧ (∀ a ∈ attributeStores v, 0x341 ≤ a ∧ a ≤ 0x3DD) := by
  have h : (List.range 0x80).all (fun n =>
      (columnStores (UInt8.ofNat n)).all (fun a => decide (0x341 ≤ a ∧ a ≤ 0x3DD)) &&
      (attributeStores (UInt8.ofNat n)).all (fun a => decide (0x341 ≤ a ∧ a ≤ 0x3DD))) = true := by
    native_decide
  intro v hv
  have hn : v.toNat < 0x80 := by simpa [UInt8.lt_iff_toNat_lt] using hv
  have := List.all_eq_true.mp h v.toNat (List.mem_range.mpr hn)
  simp only [UInt8.ofNat_toNat, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this

/-! ## Size -/

/-- A window's offset after `u` score/coin updates, `b` blocks, `t` timer prints, `p` player palettes and `c` color
rotations, appended from a clear: each record moves the offset by its length. -/
def windowOffset (u b t p c : Nat) : Nat := 14 * u + 10 * b + 6 * t + 7 * p + 7 * c

/-- With the surface's per-window counts (Layer C, `Schedule`): a window is at most 4 updates (`no_four_sixes`), so
each of the 6 floatey slots awards at most once in it (`awards_le_one`), the timer prints at most once
(`cooldown_le_one`), color rotation runs at most once (`rotation_le_one`), and a delayed block replacement can
only open it (`blockUpdater_busy`). With at most `h` = 2 head hits, each a score/coin update and a block, the
flagpole's score and one palette change, the offset stays at 176 or below. -/
theorem surface_window (fl h flag rep t p c : Nat) (hfl : fl ≤ 6) (hh : h ≤ 2) (hf : flag ≤ 1) (hr : rep ≤ 1)
    (ht : t ≤ 1) (hp : p ≤ 1) (hc : c ≤ 1) :
    windowOffset (fl + h + flag) (h + rep) t p c ≤ 176 := by
  unfold windowOffset; omega

/-- So every buffer-1 store of a surface window lands at `$0301 + 176 = $03B1` or below (the last record's
terminator is at the final offset): short of the block objects at `$03E4`. -/
theorem surface_reach : 0x301 + 176 < 0x3E4 := by decide

end Smb.Buffer
