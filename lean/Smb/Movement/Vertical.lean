import Smb.Movement.Model
import Std.Data.HashSet

/-!
# Every vertical state on open ground

Mario's vertical cells don't depend on the horizontal ones, except that a jump's strength picks one of five classes by `$700`. So they have a small closure of their own, which `vertical_ok` checks by running it: from standing on the floor, by any jump class and any A pattern, for as long as you like.

That settles what a frame on open ground needs of them. Mario stays well inside the screen, his speed stays small, and every fall reaches the floor in the window of `Y` that lands, rather than the one that pushes him sideways.

The cells a jump overwrites before reading are cleared on the ground, as `norm` does.
-/
namespace Smb.Movement

/-- The vertical cells of `s`, with the horizontal cells and the ones the ground doesn't read cleared. -/
def vcells (s : S) : S :=
  if s.st == 0 then
    { v := 0, f := 0, abs := 0, face := 0, move := 0, st := s.st, t783 := 0, r703 := 0, y := s.y, ysub := 0, vy := s.vy, vf := s.vf, g := 0, gfall := 0, y0 := 0, rise := 0, prevA := s.prevA }
  else
    { v := 0, f := 0, abs := 0, face := 0, move := 0, st := s.st, t783 := 0, r703 := 0, y := s.y, ysub := s.ysub, vy := s.vy, vf := s.vf, g := s.g, gfall := s.gfall, y0 := s.y0, rise := s.rise, prevA := s.prevA }

/-- A value of `$700` in each jump class. -/
def classAbs : Nat → UInt8
  | 0 => 0 | 1 => 9 | 2 => 0x10 | 3 => 0x19 | _ => 0x1C

/-- The input that only presses A, or doesn't. -/
def aInput (a : Bool) : In := ⟨false, false, false, a, false, false, false⟩

/-- The frame's movement, up to landing, on the vertical cells. -/
def vmove (c : Nat) (a : Bool) (s : S) : S := fallS (moved (aInput a) { s with abs := classAbs c })

/-- One frame on the vertical cells, landing on the floor at 176. -/
def vstep (c : Nat) (a : Bool) (s : S) : S :=
  vcells { land 176 (vmove c a s) with prevA := if a then 0x80 else 0 }

/-- The starting vertical states: standing, with A held or not. -/
def vstarts : List S := [vcells { start with prevA := 0 }, vcells { start with prevA := 0x80 }]

def vnexts (s : S) : List S := [0, 1, 2, 3, 4].flatMap fun c => [false, true].map fun a => vstep c a s

/-- The closure, by search. Nothing rests on how it's found: `vertical_ok` checks it's closed. -/
def vsearch : Nat → Std.HashSet S → List S → Std.HashSet S
  | 0, seen, _ => seen
  | n + 1, seen, fr => Id.run do
    let mut seen' := seen
    let mut nx : List S := []
    for s in fr do
      for t in vnexts s do
        if !seen'.contains t then
          seen' := seen'.insert t
          nx := t :: nx
    return vsearch n seen' nx

def vset : Std.HashSet S := vsearch 200 (Std.HashSet.ofList vstarts) vstarts

/-- What a frame on open ground needs of a vertical state. -/
def vsafe (s : S) : Bool :=
  s.st ≤ 2 && 0x40 ≤ s.y && s.y ≤ 176 && s.vy + 8 < 0x10 && (s.st != 0 || (s.y == 176 && s.vy == 0 && s.vf == 0)) &&
    ([0, 1, 2, 3, 4].all fun c => [false, true].all fun a =>
      let m := vmove c a s
      0x40 ≤ m.y && m.st ≤ 2 && (m.st != 0 || (m.y == 176 && m.vy == 0)) && (m.y < 176 || (m.y &&& 15 < 5 && m.y < 192 && m.vy < 0x80)))

def vcheck : Bool :=
  vstarts.all vset.contains && vset.toList.all fun s => vsafe s && (vnexts s).all vset.contains

theorem vertical_ok : vcheck = true := by native_decide

/-- The vertical cells are closed under a frame, and safe. -/
def VReach (s : S) : Prop := vset.contains s = true

theorem vreach_safe {s : S} (h : VReach s) : vsafe s = true := by
  have h0 := vertical_ok
  simp only [vcheck, Bool.and_eq_true, List.all_eq_true] at h0
  exact (h0.2 s (by simpa [VReach, Std.HashSet.mem_toList] using h)).1

theorem vreach_next {s : S} (h : VReach s) (c : Nat) (hc : c < 5) (a : Bool) : VReach (vstep c a s) := by
  have h0 := vertical_ok
  simp only [vcheck, Bool.and_eq_true, List.all_eq_true] at h0
  have h1 := (h0.2 s (by simpa [VReach, Std.HashSet.mem_toList] using h)).2
  refine h1 _ ?_
  simp only [vnexts, List.mem_flatMap, List.mem_map]
  refine ⟨c, ?_, a, by cases a <;> simp, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem vreach_start (b : UInt8) (hb : b = 0 ∨ b = 0x80) : VReach (vcells { start with prevA := b }) := by
  have h0 := vertical_ok
  simp only [vcheck, Bool.and_eq_true, List.all_eq_true] at h0
  rcases hb with rfl | rfl
  · exact h0.1 _ (by simp [vstarts])
  · exact h0.1 _ (by simp [vstarts])

end Smb.Movement
