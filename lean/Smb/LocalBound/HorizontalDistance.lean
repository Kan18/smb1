import Smb.Routine.HorizontalLimitNes

/-!
# A distance bound from the ROM's horizontal movement summaries

This is a conditional lower bound for ordinary movement segments, including segments
of 1-1. `XStep` comes from the ROM-backed ground/jump/fall theorems. We convert its
modular displacement into a natural-number bound and telescope across updates.

The caller must cover every intervening writer (or show it does not increase `phi`),
keep positions in a non-wrapping window, and relate updates to video frames. No
route, start/finish distance, or universal 1-1 invariant is assumed proved here.
-/
namespace Smb.LocalBound.HorizontalDistance
open Smb.Routine.HorizontalLimit

/-- A generous non-wrapping window: the first 32768 pixels. It is a hypothesis,
not a claim that all executions of 1-1 stay in that window. -/
def InWindow (ram : UInt16 → UInt8) : Prop := (phi ram).toNat < 0x800000

/-- Inside the window, the modular backward allowance cannot conceal a forward jump. -/
theorem modular_to_nat (old new : UInt32)
    (ho : old.toNat < 0x800000) (hn : new.toNat < 0x800000)
    (h : fwdLe new old 640 = true) : new.toNat ≤ old.toNat + 640 := by
  have ho' : old < 0x800000 := ho
  have hn' : new < 0x800000 := hn
  have hb : new ≤ old + 640 := by
    unfold fwdLe at h
    bv_decide (config := { enums := false })
  change new.toNat ≤ (old + 640).toNat at hb
  simp only [UInt32.toNat_add, UInt32.reduceToNat] at hb
  omega

theorem update_bound {ram out : UInt16 → UInt8}
    (hi : InWindow ram) (ho : InWindow out) (h : XStep ram out) :
    (phi out).toNat ≤ (phi ram).toNat + 640 :=
  modular_to_nat _ _ hi ho h.2.2.2.2.1

/-- Entry RAM at update k, RAM at its end, and the next update's entry need not
be identical. The intervening code may move progress backwards, but not forwards.
This explicitly prevents silently discarding enemy/pipe/flagpole writes. -/
theorem distance_bound (entry out : Nat → UInt16 → UInt8) (n : Nat)
    (hw : ∀ k, k ≤ n → InWindow (entry k))
    (ho : ∀ k, k < n → InWindow (out k))
    (hs : ∀ k, k < n → XStep (entry k) (out k))
    (hr : ∀ k, k < n → (phi (entry (k+1))).toNat ≤ (phi (out k)).toNat) :
    (phi (entry n)).toNat ≤ (phi (entry 0)).toNat + 640*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun k hk => hw k (by omega)) (fun k hk => ho k (by omega))
      (fun k hk => hs k (by omega)) (fun k hk => hr k (by omega))
    have step := update_bound (hw n (by omega)) (ho n (by omega)) (hs n (by omega))
    have rest := hr n (by omega)
    omega

/-- Covering D subpixels takes at least ceil(D/640) ordinary updates.
One pixel is 256 subpixels. No assumption of monotone movement is needed. -/
theorem minimum_updates (entry out : Nat → UInt16 → UInt8) (n D : Nat)
    (hw : ∀ k, k ≤ n → InWindow (entry k))
    (ho : ∀ k, k < n → InWindow (out k))
    (hs : ∀ k, k < n → XStep (entry k) (out k))
    (hr : ∀ k, k < n → (phi (entry (k+1))).toNat ≤ (phi (out k)).toNat)
    (hd : (phi (entry 0)).toNat + D ≤ (phi (entry n)).toNat) :
    (D+639)/640 ≤ n := by
  have := distance_bound entry out n hw ho hs hr
  omega

/-- The update bound gives a video-frame bound only after proving the scheduling
inequality n ≤ frames. It is deliberately an explicit premise. -/
theorem minimum_frames (entry out : Nat → UInt16 → UInt8) (n D frames : Nat)
    (hw : ∀ k, k ≤ n → InWindow (entry k))
    (ho : ∀ k, k < n → InWindow (out k))
    (hs : ∀ k, k < n → XStep (entry k) (out k))
    (hr : ∀ k, k < n → (phi (entry (k+1))).toNat ≤ (phi (out k)).toNat)
    (hd : (phi (entry 0)).toNat + D ≤ (phi (entry n)).toNat)
    (hclock : n ≤ frames) : (D+639)/640 ≤ frames := by
  exact Nat.le_trans (minimum_updates entry out n D hw ho hs hr hd) hclock

/-- A concrete first surface-segment target from the current 1-1 replay:
start at or behind pixel 40; reach pixel 914 + 1/8. These coordinates were
observed at entries in frames 195 and 562, respectively. The theorem is universal
under its listed premises, but identifying the target with *every* possible pipe
entry is a separate ROM/route obligation. -/
theorem first_surface_checkpoint (entry out : Nat → UInt16 → UInt8) (n : Nat)
    (hw : ∀ k, k ≤ n → InWindow (entry k))
    (ho : ∀ k, k < n → InWindow (out k))
    (hs : ∀ k, k < n → XStep (entry k) (out k))
    (hr : ∀ k, k < n → (phi (entry (k+1))).toNat ≤ (phi (out k)).toNat)
    (hstart : (phi (entry 0)).toNat ≤ 10240)
    (hfinish : 234016 ≤ (phi (entry n)).toNat) : 350 ≤ n := by
  have := distance_bound entry out n hw ho hs hr
  omega

end Smb.LocalBound.HorizontalDistance
