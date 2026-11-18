import Smb.Routine.XInvNext
import Smb.Routine.PlayKeep
import Smb.LocalBound.HorizontalDistance

/-!
# From one frame's `XStep` to the next frame's entry

`next_entry`: if one frame's player code gives `XStep` from the RAM at its `PlayerCtrlRoutine` entry (`b`) to the
RAM at its return into the engine (`a`), and the next frame's entry (`b'`) has the horizontal bytes as at `a`
(`PlayKeep.rest_run`, `PlayerJoin.to_routine`), the tail's copy of the on-screen X in `$0755` and the side-collision
timer still running where it was set, then `XInv` holds at `b'` and Mario's progress measure moved at most 640
sub-pixels forward (2.5 pixels) from `b` to `b'`.
-/
namespace Smb.Routine.FrameChain
open Smb Smb.Routine Smb.Routine.HorizontalLimit Smb.Routine.PlayKeep Smb.LocalBound.HorizontalDistance

theorem phi_congr {r r' : UInt16 → UInt8} (hk : ∀ a ∈ hbytes, r' a = r a) : phi r' = phi r := by
  have h86 := hk 0x86 (by simp [hbytes])
  have h6d := hk 0x6D (by simp [hbytes])
  have h400 := hk 0x400 (by simp [hbytes])
  have h71a := hk 0x71A (by simp [hbytes])
  have h71c := hk 0x71C (by simp [hbytes])
  unfold phi pixelP leftL
  rw [h86, h6d, h400, h71a, h71c]

theorem next_entry (b a b' : UInt16 → UInt8) (hX : XStep b a) (hk : ∀ x ∈ hbytes, b' x = a x)
    (h755 : b' 0x755 = (pixelP a - leftL a).toUInt8) (h785 : a 0x785 = 0x10 → b' 0x785 ≠ 0) :
    XInv b' ∧ fwdLe (phi b') (phi b) 640 = true := by
  refine ⟨xinv_next b a b' hX (hk _ (by simp [hbytes])) (hk _ (by simp [hbytes])) (hk _ (by simp [hbytes]))
    (hk _ (by simp [hbytes])) (hk _ (by simp [hbytes])) (hk _ (by simp [hbytes])) (hk _ (by simp [hbytes]))
    (hk _ (by simp [hbytes])) h755 h785, ?_⟩
  rw [phi_congr hk]
  exact hX.2.2.2.2.1

/-- `xinv_next` without the exact copy: all `XInv` needs of `$0755` is that when it says Mario was far enough right to
scroll and the side-collision timer is out, he isn't exactly at the screen's left edge. A fresh copy gives that
(`next_entry`); so does a copy one frame stale on an injury blink frame, if he can't have fallen back `$50` pixels. -/
theorem xinv_next' (ram out next : UInt16 → UInt8) (h : XStep ram out) (hk : ∀ x ∈ hbytes, next x = out x)
    (h755 : 0x50 ≤ next 0x755 → next 0x785 = 0 → pixelP out - leftL out ≠ 0)
    (h785 : out 0x785 = 0x10 → next 0x785 ≠ 0) : XInv next := by
  obtain ⟨hv, he, hp, hd, _⟩ := h
  have k57 := hk 0x57 (by simp [hbytes])
  have hP : pixelP next = pixelP out := by
    simp only [pixelP, hk 0x86 (by simp [hbytes]), hk 0x6D (by simp [hbytes])]
  have hL : leftL next = leftL out := by
    simp only [leftL, hk 0x71A (by simp [hbytes]), hk 0x71C (by simp [hbytes])]
  have hR : edgeR next = edgeR out := by
    simp only [edgeR, hk 0x71B (by simp [hbytes]), hk 0x71D (by simp [hbytes])]
  refine ⟨by rw [k57]; exact hv, by rw [hR, hL]; exact he, by rw [hk 0x3A1 (by simp [hbytes])]; exact hp, ?_, ?_⟩
  · rw [hP, hL]
    rcases hd with hd | ⟨hd, _⟩
    · exact Or.inl hd
    · exact Or.inr hd
  · intro h1 h2
    rw [hP, hL]
    have hne := h755 h1 h2
    rcases hd with hd | ⟨_, ht⟩
    · refine ⟨hne, ?_⟩
      revert hd; generalize pixelP out - leftL out = d; intro hd; bv_decide (config := { enums := false })
    · exact absurd h2 (h785 ht)

theorem next_entry' (b a b' : UInt16 → UInt8) (hX : XStep b a) (hk : ∀ x ∈ hbytes, b' x = a x)
    (h755 : 0x50 ≤ b' 0x755 → b' 0x785 = 0 → pixelP a - leftL a ≠ 0) (h785 : a 0x785 = 0x10 → b' 0x785 ≠ 0) :
    XInv b' ∧ fwdLe (phi b') (phi b) 640 = true := by
  refine ⟨xinv_next' b a b' hX hk h755 h785, ?_⟩
  rw [phi_congr hk]
  exact hX.2.2.2.2.1

/-- **Player calls in a row.** If each call's player code keeps `XStep` from an entry where `XInv` holds, each hands
the horizontal bytes to the next entry, and the `$0755` and timer conditions hold at each entry, then `XInv` holds at
every entry, and covering `D` sub-pixels from the first entry to the last takes at least `⌈D/640⌉` calls. -/
theorem calls_bound (b a : Nat → UInt16 → UInt8) (n D : Nat) (h0 : XInv (b 0))
    (hstep : ∀ k, k < n → XInv (b k) → XStep (b k) (a k))
    (hk : ∀ k, k < n → ∀ x ∈ hbytes, b (k + 1) x = a k x)
    (h755 : ∀ k, k < n → 0x50 ≤ b (k + 1) 0x755 → b (k + 1) 0x785 = 0 → pixelP (a k) - leftL (a k) ≠ 0)
    (h785 : ∀ k, k < n → a k 0x785 = 0x10 → b (k + 1) 0x785 ≠ 0)
    (hw : ∀ k, k ≤ n → InWindow (b k)) (ho : ∀ k, k < n → InWindow (a k))
    (hd : (phi (b 0)).toNat + D ≤ (phi (b n)).toNat) : (D + 639) / 640 ≤ n := by
  have hinv : ∀ k, k ≤ n → XInv (b k) := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hkn
      exact (next_entry' (b k) (a k) (b (k + 1)) (hstep k (by omega) (ih (by omega))) (hk k (by omega))
        (h755 k (by omega)) (h785 k (by omega))).1
  exact minimum_updates b a n D hw ho (fun k hkn => hstep k hkn (hinv k (by omega)))
    (fun k hkn => by rw [phi_congr (hk k hkn)]; exact Nat.le_refl _) hd

end Smb.Routine.FrameChain
