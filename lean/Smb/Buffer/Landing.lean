import Smb.Data.ProofRom
import Smb.Buffer.Window

/-!
# What can land on `$0340`

Buffer 1's records are appended one after another from `$0301`, so the byte a window leaves at `$0340` (offset 63) is
byte `63 − o` of whichever record starts at offset `o ≤ 63` and covers it (its terminator included). If that byte is a
buffer-2 offset from which a relocated column or attribute record reaches `Platform_X_Scroll` (`$03A1`), the camera can
jump. `Window.relocation_reach` already keeps every relocation below `$03DE` for offsets below `$80`; this asks which of
those reach `$03A1` (`dangerous`) and which records can put one there.

The records a surface window can hold are Layer A's: the score/coin update (14), a head hit's block (10), the timer
(6), the player palette (7), color rotation (7, only below offset `$31`), and the delayed block replacement (10, only
into an empty buffer, `blockUpdater_busy`, so only at offset 0). The counts are Layer C's: at most 9 score/coin
updates (6 floatey awards, 2 head hits, the flag), 2 head-hit blocks, and one each of the rest.

**`only_head_hit_blocks`**: in any window with those counts, if a dangerous value lands on `$0340`, it's byte 1, 4, 8
or 9 of a head hit's block record (its address low byte or a tile), starting at offset 62, 59, 55 or 54. Every other
byte that can land there is safe. That uses the digits being 0–9, which the digit invariant (`Good`, below `$76`)
doesn't yet give; with the real modifiers (point values and the timer's −1) it holds.
-/
namespace Smb.Buffer.Landing
open Smb.Buffer

inductive Kind where
  | upd | blk | tim | pal | crot | rep
  deriving DecidableEq, Repr

/-- How far a record moves the offset (its length without the terminator, which the next record overwrites). -/
def len : Kind → Nat
  | .upd => 14 | .blk => 10 | .tim => 6 | .pal => 7 | .crot => 7 | .rep => 10

def digits : List UInt8 := (List.range 10).map UInt8.ofNat

/-- The block records' address bytes on the surface's hittable rows, from `blockHi`/`blockLo`. -/
def rows : List UInt8 := [0x30, 0x60, 0x70, 0xA0]
def blockHis : List UInt8 := rows.flatMap fun r2 => (List.range 256).map fun r6 => blockHi r2 (UInt8.ofNat r6)
def blockLos : List UInt8 := rows.flatMap fun r2 => (List.range 256).map fun r6 => blockLo r2 (UInt8.ofNat r6)
def blockLos2 : List UInt8 := blockLos.map (· + 0x20)

/-- `BackgroundColors` (`$85CF`), the player palette's first color. -/
def bgColors : List UInt8 := smbPrg% 0x85CF 8

theorem bgColors_rom : ∀ i : UInt8, i < 8 → gameRom ((0x85CF + i.toUInt16) &&& 0x7FFF) ∈ bgColors := by
  have h : (List.range 8).all (fun n => bgColors.contains (gameRom ((0x85CF + (UInt8.ofNat n).toUInt16) &&& 0x7FFF))) = true := by
    native_decide
  intro i hi
  have hn : i.toNat < 8 := by simpa [UInt8.lt_iff_toNat_lt] using hi
  have := List.all_eq_true.mp h i.toNat (List.mem_range.mpr hn)
  simpa using this

/-- A block record's bytes: address, length 2, the top two tiles, address one row down, the bottom two tiles, for
any of the four kinds (`blk0Fields`–`blk3Fields`). -/
def blkVals : Nat → List UInt8
  | 0 => blockHis | 1 => blockLos | 2 => [0x02] | 3 => [0x45, 0x47, 0x57, 0x24] | 4 => [0x45, 0x47, 0x58, 0x24]
  | 5 => blockHis | 6 => blockLos2 | 7 => [0x02] | 8 => [0x47, 0x59, 0x24] | 9 => [0x47, 0x5A, 0x24] | _ => [0]

/-- The values byte `j` of a record can have (`j = len k` is its terminator). -/
def vals : Kind → Nat → List UInt8
  | .upd, j => match j with
    | 0 => [0x20] | 1 => [0x6D] | 2 => [0x02] | 3 => digits | 4 => digits | 5 => [0x20] | 6 => [0x62] | 7 => [0x06]
    | 8 => 0x24 :: digits | 14 => [0] | _ => digits
  | .blk, j => blkVals j
  | .rep, j => blkVals j
  | .tim, j => match j with
    | 0 => [0x20] | 1 => [0x7A] | 2 => [0x03] | 6 => [0] | _ => digits
  | .pal, j => match j with
    | 0 => [0x3F] | 1 => [0x10] | 2 => [0x04] | 3 => bgColors
    | 4 => [0x37, 0x16, 0x30] | 5 => [0x27] | 6 => [0x16, 0x18, 0x19] | _ => [0]
  | .crot, _ => (List.range 256).map UInt8.ofNat

/-- A buffer-2 offset from which a relocated column or attribute record writes `$03A1`. -/
def dangerous (v : UInt8) : Bool := (columnStores v).contains 0x3A1 || (attributeStores v).contains 0x3A1

/-- Records before the one covering offset 63, as counts: score/coin, head-hit block, timer, palette, rotation, and
whether the window began with the replacement. -/
structure Counts where
  u : Nat
  b : Nat
  t : Nat
  p : Nat
  c : Nat
  r : Nat

def Counts.offset (n : Counts) : Nat := 14 * n.u + 10 * n.b + 6 * n.t + 7 * n.p + 7 * n.c + 10 * n.r

def maxOf : Kind → Nat
  | .upd => 9 | .blk => 2 | .tim => 1 | .pal => 1 | .crot => 1 | .rep => 1

def Counts.of (n : Counts) : Kind → Nat
  | .upd => n.u | .blk => n.b | .tim => n.t | .pal => n.p | .crot => n.c | .rep => n.r

/-- The record of kind `k` starting after the records `n` can cover offset 63, and its byte there is dangerous. -/
def bad (n : Counts) (k : Kind) : Bool :=
  let o := n.offset
  -- room for `k` after `n`
  n.of k + 1 ≤ maxOf k && o ≤ 63 && 63 ≤ o + len k &&
    -- the replacement only first, rotation only below `$31`
    (k != .rep || o == 0) && (k != .crot || o < 0x31) &&
    (vals k (63 - o)).any dangerous

def allCounts : List Counts :=
  (List.range 10).flatMap fun u => (List.range 3).flatMap fun b => (List.range 2).flatMap fun t =>
  (List.range 2).flatMap fun p => (List.range 2).flatMap fun c => (List.range 2).map fun r => ⟨u, b, t, p, c, r⟩

def kinds : List Kind := [.upd, .blk, .tim, .pal, .crot, .rep]

/-- **Only a head hit's block, at four alignments.** Over every combination of earlier records the counts allow, a
record whose byte at `$0340` can be dangerous is a head-hit block starting at offset 54, 55, 59 or 62. -/
theorem only_head_hit_blocks : allCounts.all (fun n => kinds.all fun k =>
    !bad n k || (k == .blk && [54, 55, 59, 62].contains n.offset)) = true := by native_decide

/-- Each alignment occurs among the abstract record counts. For example,
four score/coin records and a timer record place a block record at offset 62.
A separate reachability argument must connect those counts to controller inputs. -/
theorem alignments_reachable : [54, 55, 59, 62].all (fun o =>
    allCounts.any fun n => n.offset == o && bad n .blk) = true := by native_decide


/-! ## The templates are the records

Layer A's field lists, byte by byte, are inside `vals`: the score/coin and timer updates when their digits are 0–9,
the block records on the surface's rows, the palette when its background index is below 8. -/

/-- `DigitsMathRoutine`'s step keeps a digit 0–9 when the modifier, as a signed byte, is at most 10: as written
at most 9, plus the one carry the digit to its right can add. A negative sum borrows and leaves 9. -/
theorem digitResult_decimal (m old : UInt8) (hm : m ≤ 10 ∨ 0x80 ≤ m) (ho : old ≤ 9) :
    Digits.DigitMath.digitResult m old ≤ 9 := by
  unfold Digits.DigitMath.digitResult
  bv_decide

theorem mem_digits {v : UInt8} (h : v ≤ 9) : v ∈ digits := by
  have : ∀ w : Fin 10, UInt8.ofNat w.val ∈ digits := by decide
  have hv : v.toNat < 10 := by have := UInt8.le_iff_toNat_le.mp h; simp at this; omega
  simpa using this ⟨v.toNat, hv⟩

theorem getD_cons_zero {a : UInt8} {l : List UInt8} : (a :: l).getD 0 0 = a := rfl
theorem getD_cons_succ {a : UInt8} {l : List UInt8} {j : Nat} : (a :: l).getD (j + 1) 0 = l.getD j 0 := rfl

theorem upd1_fits (ram : UInt16 → UInt8)
    (hd : ∀ a ∈ [0x7ED, 0x7EE, 0x7DD, 0x7DE, 0x7DF, 0x7E0, 0x7E1, 0x7E2], ram a ≤ 9) (j : Nat) :
    (upd1Fields ram).getD j 0 ∈ vals .upd j := by
  have h := hd
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  match j with
  | 0 | 1 | 2 | 5 | 6 | 7 | 14 => simp [upd1Fields, vals]
  | 3 => simpa [upd1Fields, vals] using mem_digits h0
  | 4 => simpa [upd1Fields, vals] using mem_digits h1
  | 8 => cases e : ram 0x7DD == 0 <;> simp [upd1Fields, vals, e, mem_digits h2]
  | 9 => simpa [upd1Fields, vals] using mem_digits h3
  | 10 => simpa [upd1Fields, vals] using mem_digits h4
  | 11 => simpa [upd1Fields, vals] using mem_digits h5
  | 12 => simpa [upd1Fields, vals] using mem_digits h6
  | 13 => simpa [upd1Fields, vals] using mem_digits h7
  | n + 15 => simp [upd1Fields, vals, mem_digits (show (0 : UInt8) ≤ 9 by decide)]

theorem st5_fits (ram : UInt16 → UInt8) (hd : ∀ a ∈ [0x7F8, 0x7F9, 0x7FA], ram a ≤ 9) (j : Nat) :
    (st5Fields ram).getD j 0 ∈ vals .tim j := by
  have h := hd
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  match j with
  | 0 | 1 | 2 | 6 => simp [st5Fields, vals]
  | 3 => simpa [st5Fields, vals] using mem_digits h0
  | 4 => simpa [st5Fields, vals] using mem_digits h1
  | 5 => simpa [st5Fields, vals] using mem_digits h2
  | n + 7 => simp [st5Fields, vals, mem_digits (show (0 : UInt8) ≤ 9 by decide)]

theorem hi_mem {r2 : UInt8} (h : SurfaceRow r2) (r6 : UInt8) : blockHi r2 r6 ∈ blockHis := by
  simp only [blockHis, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨r2, by rcases h with rfl | rfl | rfl | rfl <;> simp [rows], r6.toNat, r6.toNat_lt, by simp⟩

theorem lo_mem {r2 : UInt8} (h : SurfaceRow r2) (r6 : UInt8) : blockLo r2 r6 ∈ blockLos := by
  simp only [blockLos, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨r2, by rcases h with rfl | rfl | rfl | rfl <;> simp [rows], r6.toNat, r6.toNat_lt, by simp⟩

theorem lo2_mem {r2 : UInt8} (h : SurfaceRow r2) (r6 : UInt8) : blockLo r2 r6 + 0x20 ∈ blockLos2 :=
  List.mem_map.mpr ⟨_, lo_mem h r6, rfl⟩

theorem blk_fits (ram : UInt16 → UInt8) (h : SurfaceRow (ram 2)) (j : Nat) :
    (blk0Fields ram).getD j 0 ∈ blkVals j ∧ (blk1Fields ram).getD j 0 ∈ blkVals j ∧
    (blk2Fields ram).getD j 0 ∈ blkVals j ∧ (blk3Fields ram).getD j 0 ∈ blkVals j := by
  have hh := hi_mem h (ram 6)
  have hl := lo_mem h (ram 6)
  have hl2 := lo2_mem h (ram 6)
  match j with
  | 0 | 5 => simp [blk0Fields, blk1Fields, blk2Fields, blk3Fields, blkVals, hh]
  | 1 => simp [blk0Fields, blk1Fields, blk2Fields, blk3Fields, blkVals, hl]
  | 6 => simp [blk0Fields, blk1Fields, blk2Fields, blk3Fields, blkVals, hl2]
  | 2 | 3 | 4 | 7 | 8 | 9 | 10 => simp [blk0Fields, blk1Fields, blk2Fields, blk3Fields, blkVals]
  | n + 11 => simp [blk0Fields, blk1Fields, blk2Fields, blk3Fields, blkVals]

theorem pcol_fits' (ram prg : UInt16 → UInt8) (htab : ∀ i : UInt8, i < 8 → prg ((0x85CF + i.toUInt16) &&& 0x7FFF) ∈ bgColors)
    (hidx : (bif ram 0x744 == 0 then ram 0x74E else ram 0x744) < 8) (j : Nat) :
    (pcolFields ram prg).getD j 0 ∈ vals .pal j := by
  match j with
  | 0 | 1 | 2 | 5 | 7 => simp only [pcolFields, List.getD_cons_succ, List.getD_cons_zero, vals]; decide
  | 3 =>
    simp only [pcolFields, List.getD_cons_succ, List.getD_cons_zero, vals]
    cases e : ram 0x744 == 0 <;> simp only [e, Bool.cond_true, Bool.cond_false] at hidx ⊢
    · exact htab _ hidx
    · exact htab _ hidx
  | 4 | 6 =>
    simp only [pcolFields, List.getD_cons_succ, List.getD_cons_zero, vals]
    cases ram 0x756 == 2 <;> cases ram 0x753 == 0 <;> decide
  | n + 8 =>
    simp only [pcolFields, List.getD_cons_succ]
    simp [vals]

theorem pcol_fits (ram : UInt16 → UInt8) (hidx : (bif ram 0x744 == 0 then ram 0x74E else ram 0x744) < 8) (j : Nat) :
    (pcolFields ram gameRom).getD j 0 ∈ vals .pal j :=
  pcol_fits' ram gameRom bgColors_rom hidx j

end Smb.Buffer.Landing
