import Smb.Movement.Vertical

/-! The upward 165–167 band in the open-floor vertical model. This does not
cover stomps, head hits, springs, or entry from inside the floor, and it does
not establish the horizontal conditions for touching the pole. -/
namespace Smb.Movement.JumpBand

def inBand (s : S) : Bool := 165 ≤ s.y && s.y ≤ 167 && 0x80 ≤ s.vy

def bandShape (s : S) : Bool := s.y == 166 && s.ysub == 40 && s.vy == 251 &&
  s.gfall == 144 && s.y0 == 176 && s.rise == 1

def firstFast (s : S) : Bool := s.y == 171 && s.ysub == 0 && s.vy == 251 && s.vf == 40

def startFast (s : S) (c : Nat) (a : Bool) : Bool :=
  s.st == 0 && s.y == 176 && s.prevA == 0 && decide (3 ≤ c) && a

theorem band_checked : vset.toList.all (fun s => !inBand s || bandShape s) = true := by
  native_decide

theorem predecessor_checked : vset.toList.all (fun s =>
    [0,1,2,3,4].all (fun c => [false,true].all (fun a =>
      !inBand (vstep c a s) || firstFast s))) = true := by native_decide

theorem launch_checked : vset.toList.all (fun s =>
    [0,1,2,3,4].all (fun c => [false,true].all (fun a =>
      !firstFast (vstep c a s) || startFast s c a))) = true := by native_decide

private theorem class_mem {c : Nat} (hc : c < 5) : c ∈ [0,1,2,3,4] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem bool_mem (a : Bool) : a ∈ [false,true] := by cases a <;> simp

/-- An upward state in the band can only have Y=166, with the strong jump's
vertical state. The slow jump never occupies 165, 166 or 167 while rising. -/
theorem band_shape {s : S} (hv : VReach s) (hb : inBand s = true) : bandShape s = true := by
  have h := List.all_eq_true.mp band_checked s (by simpa [VReach, Std.HashSet.mem_toList] using hv)
  simpa only [hb, Bool.not_true, Bool.false_or] using h

/-- The band is reached from the first frame of a strong jump. -/
theorem band_predecessor {s : S} (hv : VReach s) (c : Nat) (hc : c < 5) (a : Bool)
    (hb : inBand (vstep c a s) = true) : firstFast s = true := by
  have h := List.all_eq_true.mp predecessor_checked s (by simpa [VReach, Std.HashSet.mem_toList] using hv)
  have h := List.all_eq_true.mp (List.all_eq_true.mp h c (class_mem hc)) a (bool_mem a)
  simpa only [hb, Bool.not_true, Bool.false_or] using h

/-- That preceding frame must itself be a fresh class-3/4 jump from Y=176. -/
theorem first_predecessor {s : S} (hv : VReach s) (c : Nat) (hc : c < 5) (a : Bool)
    (hb : firstFast (vstep c a s) = true) : startFast s c a = true := by
  have h := List.all_eq_true.mp launch_checked s (by simpa [VReach, Std.HashSet.mem_toList] using hv)
  have h := List.all_eq_true.mp (List.all_eq_true.mp h c (class_mem hc)) a (bool_mem a)
  simpa only [hb, Bool.not_true, Bool.false_or] using h

/-- In any two consecutive open-floor model steps ending in the rising band,
the first step was the fresh strong jump. This leaves the horizontal obstruction
and exceptional vertical sources as separate obligations. -/
theorem two_step_origin {s : S} (hv : VReach s)
    (c0 c1 : Nat) (hc0 : c0 < 5) (hc1 : c1 < 5) (a0 a1 : Bool)
    (hb : inBand (vstep c1 a1 (vstep c0 a0 s)) = true) :
    startFast s c0 a0 = true :=
  first_predecessor hv c0 hc0 a0
    (band_predecessor (vreach_next hv c0 hc0 a0) c1 hc1 a1 hb)

end Smb.Movement.JumpBand
