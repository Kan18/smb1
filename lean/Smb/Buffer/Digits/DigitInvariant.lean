import Smb.Buffer.Digits.DigitMath
import Lean.Elab.Tactic.Omega

/-!
Conditional event invariant for the 36 displayed score/coin/timer digits.
The event-to-ROM-trace refinement and alias exclusion are explicit external
premises; this file proves the range closure once those events are justified.
-/
namespace Smb.Buffer.Digits.DigitInvariant
open Smb.Buffer.Digits.DigitMath
open Smb Smb.Routine

abbrev Digits := Fin 36 → UInt8

def Good (d : Digits) : Prop := ∀ i, d i ≤ 0x75

def write (d : Digits) (i : Fin 36) (v : UInt8) : Digits :=
  fun j => if j = i then v else d j

inductive Event where
  | reset
  | setSmall (i : Fin 36) (v : Fin 10)
  | math (i : Fin 36) (modifier : UInt8)
  | copy (dest src : Fin 36)
  | noAlias

def step (e : Event) (d : Digits) : Digits :=
  match e with
  | .reset => fun _ => 0
  | .setSmall i v => write d i (UInt8.ofNat v.val)
  | .math i m => write d i (digitResult m (d i))
  | .copy dest src => write d dest (d src)
  | .noAlias => d

theorem small_below_75 (v : Fin 10) :
    (UInt8.ofNat v.val) ≤ 0x75 := by
  have h : ∀ u : Fin 10, (UInt8.ofNat u.val) ≤ 0x75 := by decide
  exact h v

theorem step_good (e : Event) (d : Digits) (hd : Good d) :
    Good (step e d) := by
  intro j
  cases e with
  | reset => simp [step]
  | setSmall i v =>
      by_cases h : j = i
      · simp [step, write, h, small_below_75]
      · simpa [step, write, h] using hd j
  | math i modifier =>
      by_cases h : j = i
      · simp [step, write, h, digitResult_below_8f]
      · simpa [step, write, h] using hd j
  | copy dest src =>
      by_cases h : j = dest
      · simpa [step, write, h] using hd src
      · simpa [step, write, h] using hd j
  | noAlias => exact hd j

def run : List Event → Digits → Digits
  | [], d => d
  | e :: es, d => run es (step e d)

theorem run_good (es : List Event) (d : Digits) (hd : Good d) :
    Good (run es d) := by
  induction es generalizing d with
  | nil => exact hd
  | cons e es ih => exact ih _ (step_good e d hd)

def zeroDigits : Digits := fun _ => 0

theorem zeroDigits_good : Good zeroDigits := by
  intro i
  simp [zeroDigits]

/-- A clean classified event trace never leaves `$8f` in a displayed digit.
This conclusion is conditional on the list of events actually describing
all writes to those cells. -/
theorem classified_trace_no_8f (es : List Event) (i : Fin 36) :
    run es zeroDigits i ≠ 0x8f := by
  have h := run_good es zeroDigits zeroDigits_good i
  bv_decide

def digitIndex (y : UInt8) (hy : y ≤ 35) : Fin 36 :=
  ⟨y.toNat, by
    have h := UInt8.le_iff_toNat_le.mp hy
    change y.toNat ≤ 35 at h
    omega⟩

/-- Machine copy plus the classified history. `hagrees` is the exact
event-to-RAM correspondence premise still needed from a whole-game trace. -/
theorem classified_copy_ne_8f
    (es : List Event)
    (a x y sp p : UInt8) (ram prg : UInt16 → UInt8) (cyc : UInt64)
    (hc : CodeAt prg 0x0f47 copyCode)
    (hI : p &&& 4 ≠ 0) (hy : y ≤ 35)
    (hagrees : ram (0x7d7 + y.toUInt16) =
      run es zeroDigits (digitIndex y hy)) :
    let s : Plain := ⟨⟨0x8f47, a, x, y, sp, p⟩, ram, prg, cyc, false⟩
    let t := ((CPU.runTo (σ := Plain) 0x8f4d 3).run s).2
    t.ram (0x304 + x.toUInt16) ≠ 0x8f := by
  have hgood := run_good es zeroDigits zeroDigits_good (digitIndex y hy)
  have hsource : ram (0x7d7 + y.toUInt16) ≤ 0x75 := by
    rw [hagrees]
    exact hgood
  have hcopy := copied_digit_below_8f a x y sp p ram prg cyc
    hc hI hy hsource
  have hbound := hcopy.2.2
  dsimp only
  intro heq
  rw [heq] at hbound
  exact (by decide : ¬ ((0x8f : UInt8) ≤ 0x75)) hbound

/-- The same classified-copy result on the full NES, under the usual quiet
ROM premise and exact event-to-RAM correspondence. -/
theorem classified_copy_ne_8f_nes
    (es : List Event) (s : NES)
    (hq : s.Quiet) (hprg : s.prg = Smb.prg)
    (hpc : s.pc = 0x8f47) (hI : s.p &&& 4 ≠ 0)
    (hy : s.y ≤ 35)
    (hagrees : ramAt s (0x7d7 + s.y.toUInt16) =
      run es zeroDigits (digitIndex s.y hy)) :
    let t := ((CPU.runTo (σ := NES) 0x8f4d 3).run s).2
    ramAt t (0x304 + s.x.toUInt16) ≠ 0x8f := by
  have hgood := run_good es zeroDigits zeroDigits_good (digitIndex s.y hy)
  have hsource : ramAt s (0x7d7 + s.y.toUInt16) ≤ 0x75 := by
    rw [hagrees]
    exact hgood
  have hcopy := copied_digit_below_8f_nes s hq hprg hpc hI hy hsource
  have hbound := hcopy.2
  dsimp only
  intro heq
  rw [heq] at hbound
  exact (by decide : ¬ ((0x8f : UInt8) ≤ 0x75)) hbound

end Smb.Buffer.Digits.DigitInvariant
