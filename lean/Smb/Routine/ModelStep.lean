import Smb.Routine.ModelFrame

/-!
# From the routine's cells to the model's `step`

The game keeps cells that `Smb.Movement.norm` drops, so a run of the game and of the model agree only on the cells that matter. A held A shows the difference most: on the ground the game remembers it, and the model does the same by leaving A out of that frame's input.
-/
namespace Smb.Routine.ModelStep
open Smb.Movement
open Smb.Routine.ModelBridge (ite_bif tbl5_jc tbl3_sc tbl3_fc)
open Smb.Routine.ModelFrame (afterBg)

/-- The input the model sees: A held from before does nothing on the ground. -/
def effIn (s : S) (i : In) : In :=
  if s.st == 0 && s.prevA != 0 then { i with a := false, timer := s.t783 != 0 } else { i with timer := s.t783 != 0 }

/-- The landing test at floor `g`, as `land` reads it. -/
def landC (g : UInt8) (s : S) : Bool :=
  s.st != 0 && s.vy < 0x80 && s.y ≥ g && s.y &&& 15 < 5 && s.y < g + 16

macro "step_tac" : tactic => `(tactic| (
  simp only [norm, step, rawStep, land, landC, afterBg, preFall, setMove, fallS, moved, jumpStart, speedClass, frictionClass, running, timerSet,
    routine, skid, friction, rightV, leftV, absOf, tbl5_jc, openGround, effIn,
    apply_ite S.v, apply_ite S.f, apply_ite S.abs, apply_ite S.face, apply_ite S.move, apply_ite S.st, apply_ite S.t783, apply_ite S.r703,
    apply_ite S.y, apply_ite S.ysub, apply_ite S.vy, apply_ite S.vf, apply_ite S.g, apply_ite S.gfall, apply_ite S.y0, apply_ite S.rise, apply_ite S.prevA,
    apply_ite In.r, apply_ite In.l, apply_ite In.b, apply_ite In.a, apply_ite In.other, apply_ite In.down, apply_ite In.timer,
    ite_bif, decide_eq_true_eq, Bool.decide_eq_true] at *
  try simp only [tbl3_sc, tbl3_fc] at *
  simp only [bne] at *
  bv_decide (config := { enums := false })))

set_option maxHeartbeats 8000000 in
theorem step_v (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).v =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).v := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_f (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).f =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).f := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_abs (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).abs =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).abs := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_face (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).face =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).face := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_move (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).move =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).move := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_st (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).st =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).st := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_t783 (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).t783 =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).t783 := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_r703 (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).r703 =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).r703 := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_y (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).y =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).y := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_ysub (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).ysub =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).ysub := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_vy (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).vy =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).vy := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_vf (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).vf =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).vf := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_g (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).g =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).g := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_gfall (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).gfall =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).gfall := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_y0 (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).y0 =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).y0 := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_rise (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).rise =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).rise := by
  subst hL
  step_tac

set_option maxHeartbeats 8000000 in
theorem step_prevA (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    (norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 }).prevA =
      (Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s)).prevA := by
  subst hL
  step_tac

theorem S_ext {a b : S} (h1 : a.v = b.v) (h2 : a.f = b.f) (h3 : a.abs = b.abs) (h4 : a.face = b.face) (h5 : a.move = b.move) (h6 : a.st = b.st)
    (h7 : a.t783 = b.t783) (h8 : a.r703 = b.r703) (h9 : a.y = b.y) (h10 : a.ysub = b.ysub) (h11 : a.vy = b.vy) (h12 : a.vf = b.vf) (h13 : a.g = b.g)
    (h14 : a.gfall = b.gfall) (h15 : a.y0 = b.y0) (h16 : a.rise = b.rise) (h17 : a.prevA = b.prevA) : a = b := by
  cases a; cases b; simp_all

/-- What the game does on open ground, normalized, is a step of the model. -/
theorem step_of_bg (i : In) (s : S) (L : Bool) (hspd : s.vy + 0x40 < 0x80) (hy : s.st = 0 → s.y &&& 0xF0 = s.y)
    (hL : L = ((fallS (moved i s)).st == 0 || landC 176 (fallS (moved i s)))) :
    norm openGround { afterBg L (setMove (fallS (moved i s))) with prevA := if i.a then 0x80 else 0 } =
      Smb.Movement.step openGround 176 false (effIn s i) (norm openGround s) :=
  S_ext (step_v i s L hspd hy hL) (step_f i s L hspd hy hL) (step_abs i s L hspd hy hL) (step_face i s L hspd hy hL) (step_move i s L hspd hy hL)
    (step_st i s L hspd hy hL) (step_t783 i s L hspd hy hL) (step_r703 i s L hspd hy hL) (step_y i s L hspd hy hL) (step_ysub i s L hspd hy hL)
    (step_vy i s L hspd hy hL) (step_vf i s L hspd hy hL) (step_g i s L hspd hy hL) (step_gfall i s L hspd hy hL) (step_y0 i s L hspd hy hL)
    (step_rise i s L hspd hy hL) (step_prevA i s L hspd hy hL)

end Smb.Routine.ModelStep
