import Smb.Plain
import Std.Tactic.BVDecide

/-!
# Disjointness of indexed addresses

Buffer writers store at `c + x` for a base `c` and an 8-bit index `x`, which ranges over `c`..`c + 255`. These
rewrite such address comparisons to `false` when the ranges can't meet, with side conditions on literals only, so
a symbolic run can drop aliasing it can't have, as it goes.
-/
namespace Smb.Buffer

theorem idx_ne_k (c k : UInt16) (x : UInt8) (hc : c ≤ 0x700) (hk : k < c ∨ c + 0xFF < k) :
    ((c + x.toUInt16) &&& 0x7FF == k) = false := by
  bv_decide

theorem k_ne_idx (c k : UInt16) (x : UInt8) (hc : c ≤ 0x700) (hk : k < c ∨ c + 0xFF < k) :
    (k == (c + x.toUInt16) &&& 0x7FF) = false := by
  bv_decide

theorem stack_ne_idx (c : UInt16) (sp x : UInt8) (hc : 0x200 ≤ c ∧ c ≤ 0x700) :
    ((0x100 ||| sp.toUInt16) &&& 0x7FF == (c + x.toUInt16) &&& 0x7FF) = false := by
  bv_decide

theorem idx_ne_stack (c : UInt16) (sp x : UInt8) (hc : 0x200 ≤ c ∧ c ≤ 0x700) :
    ((c + x.toUInt16) &&& 0x7FF == (0x100 ||| sp.toUInt16) &&& 0x7FF) = false := by
  bv_decide

/-- Adding a byte index in this base range cannot wrap into the RAM mirrors. -/
theorem rom_idx_not_ram (c : UInt16) (x : UInt8) (hc : 0x2000 ≤ c ∧ c ≤ 0xFF00) :
    decide (c + x.toUInt16 < 0x2000) = false := by
  simp only [decide_eq_false_iff_not]
  bv_decide

/-- `cmp` against zero always sets carry. -/
theorem dec_ge_zero (n : UInt8) : decide (n ≥ 0) = true := by
  simp [UInt8.le_iff_toNat_le]

end Smb.Buffer
