import Smb.Routine.ModelStep
import Smb.Movement.Vertical

/-!
# The game's vertical cells, in the model's closure

`Smb.Movement.vertical_ok` checks the closure on the model's own step. Here the frame `ModelFrame` proves of the game lands in it, whatever the input and the horizontal cells.
-/
namespace Smb.Routine.LaunchVert
open Smb.Movement
open Smb.Routine.ModelBridge (ite_bif tbl5_jc tbl3_sc tbl3_fc)
open Smb.Routine.ModelFrame (afterBg)
open Smb.Routine.ModelStep (landC)

/-- The state after the game's frame, as `follows_of_parts` has it. -/
def after (i : In) (L : Bool) (s : S) : S := { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }

theorem jumpClass_lt (a : UInt8) : Smb.Movement.jumpClass a < 5 := by
  simp only [Smb.Movement.jumpClass]
  repeat' split
  all_goals omega

theorem class_rep (a : UInt8) : Smb.Movement.jumpClass (classAbs (Smb.Movement.jumpClass a)) = Smb.Movement.jumpClass a := by
  simp only [Smb.Movement.jumpClass]
  repeat' split
  all_goals first | rfl | (simp_all [classAbs] <;> omega)

macro "vert_tac" : tactic => `(tactic| (
  simp only [vcells, vstep, vmove, after, aInput, afterBg, land, landC, setMove, fallS, moved, jumpStart, speedClass, frictionClass, running, timerSet,
    routine, skid, friction, rightV, leftV, absOf, class_rep,
    apply_ite S.v, apply_ite S.f, apply_ite S.abs, apply_ite S.face, apply_ite S.move, apply_ite S.st, apply_ite S.t783, apply_ite S.r703,
    apply_ite S.y, apply_ite S.ysub, apply_ite S.vy, apply_ite S.vf, apply_ite S.g, apply_ite S.gfall, apply_ite S.y0, apply_ite S.rise, apply_ite S.prevA,
    apply_ite In.r, apply_ite In.l, apply_ite In.b, apply_ite In.a, apply_ite In.other, apply_ite In.down, apply_ite In.timer,
    tbl5_jc, ite_bif, decide_eq_true_eq, Bool.decide_eq_true] at *
  simp only [bne] at *
  bv_decide (config := { enums := false })))

set_option maxHeartbeats 8000000 in
theorem after_v (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).v = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).v := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_f (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).f = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).f := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_abs (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).abs = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).abs := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_face (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).face = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).face := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_move (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).move = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).move := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_st (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).st = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).st := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_t783 (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).t783 = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).t783 := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_r703 (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).r703 = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).r703 := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_y (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).y = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).y := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_ysub (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).ysub = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).ysub := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_vy (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).vy = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).vy := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_vf (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).vf = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).vf := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_g (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).g = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).g := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_gfall (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).gfall = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).gfall := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_y0 (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).y0 = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).y0 := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_rise (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).rise = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).rise := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem after_prevA (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (vcells (after i L s)).prevA = (vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s)).prevA := by
  subst hL
  vert_tac

set_option maxHeartbeats 8000000 in
theorem move_y (i : In) (s : S) (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (fallS (moved i s)).y = (vmove (Smb.Movement.jumpClass s.abs) i.a (vcells s)).y := by
  vert_tac

set_option maxHeartbeats 8000000 in
theorem move_vy (i : In) (s : S) (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (fallS (moved i s)).vy = (vmove (Smb.Movement.jumpClass s.abs) i.a (vcells s)).vy := by
  vert_tac

set_option maxHeartbeats 8000000 in
theorem move_st (i : In) (s : S) (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) :
    (fallS (moved i s)).st = (vmove (Smb.Movement.jumpClass s.abs) i.a (vcells s)).st := by
  vert_tac

/-- The game's frame stays in the closure. -/
theorem vreach_after (i : In) (L : Bool) (s : S) (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s))))
    (hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0) (hv : VReach (vcells s)) : VReach (vcells (after i L s)) := by
  have e : vcells (after i L s) = vstep (Smb.Movement.jumpClass s.abs) i.a (vcells s) :=
    Smb.Routine.ModelStep.S_ext (after_v i L s hL hg) (after_f i L s hL hg) (after_abs i L s hL hg) (after_face i L s hL hg) (after_move i L s hL hg) (after_st i L s hL hg)
      (after_t783 i L s hL hg) (after_r703 i L s hL hg) (after_y i L s hL hg) (after_ysub i L s hL hg) (after_vy i L s hL hg) (after_vf i L s hL hg)
      (after_g i L s hL hg) (after_gfall i L s hL hg) (after_y0 i L s hL hg) (after_rise i L s hL hg) (after_prevA i L s hL hg)
  rw [e]
  exact vreach_next hv _ (jumpClass_lt _) _

theorem vcells_st (s : S) : (vcells s).st = s.st := by simp only [vcells]; split <;> rfl
theorem vcells_y (s : S) : (vcells s).y = s.y := by simp only [vcells]; split <;> rfl
theorem vcells_vy (s : S) : (vcells s).vy = s.vy := by simp only [vcells]; split <;> rfl
theorem vcells_vf (s : S) : (vcells s).vf = s.vf := by simp only [vcells]; split <;> rfl

/-- What the closure says of a state in it, and of its next move. -/
structure VFacts (s : S) : Prop where
  st : s.st ≤ 2
  ylo : 0x40 ≤ s.y
  yhi : s.y ≤ 176
  vy : s.vy + 8 < 0x10
  ground : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0
  mlo : ∀ i : In, 0x40 ≤ (fallS (moved i s)).y
  mst : ∀ i : In, (fallS (moved i s)).st ≤ 2
  mground : ∀ i : In, (fallS (moved i s)).st = 0 → (fallS (moved i s)).y = 176 ∧ (fallS (moved i s)).vy = 0
  mland : ∀ i : In, (fallS (moved i s)).y < 176 ∨ ((fallS (moved i s)).y &&& 15 < 5 ∧ (fallS (moved i s)).y < 192 ∧ (fallS (moved i s)).vy < 0x80)

theorem vfacts {s : S} (hv : VReach (vcells s)) : VFacts s := by
  have h := vreach_safe hv
  simp only [vsafe, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, List.all_eq_true, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [vcells_st] at h1
  rw [vcells_y] at h2 h3
  rw [vcells_vy] at h4
  have hg : s.st = 0 → s.y = 176 ∧ s.vy = 0 ∧ s.vf = 0 := fun e => by
    rw [vcells_st, vcells_y, vcells_vy, vcells_vf] at h5
    rcases h5 with h | h
    · exact absurd e h
    · exact ⟨h.1.1, h.1.2, h.2⟩
  have hm := fun (i : In) => h6 (Smb.Movement.jumpClass s.abs) (by
    have := jumpClass_lt s.abs
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega) i.a (by cases i.a <;> simp)
  refine ⟨h1, h2, h3, h4, hg, fun i => ?_, fun i => ?_, fun i e => ?_, fun i => ?_⟩
  · rw [move_y i s hg]; exact (hm i).1.1.1
  · rw [move_st i s hg]; exact (hm i).1.1.2
  · rw [move_st i s hg] at e
    rw [move_y i s hg, move_vy i s hg]
    rcases (hm i).1.2 with h | h
    · exact absurd e h
    · exact ⟨h.1, h.2⟩
  · rw [move_y i s hg, move_vy i s hg]
    rcases (hm i).2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1.1, h.1.2, h.2⟩

end Smb.Routine.LaunchVert
