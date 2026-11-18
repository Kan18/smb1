import Smb.Routine.ImposeGravityNes
import Smb.Tas

/-!
# The TAS reaches downward speed 5

`gravityVel_mario_speed5` shows that the "maximum speed 4" clamp lets one call produce speed 5.
Here the full NES model, running HappyLee's TAS inputs, reaches such a call: in frame 336
(zero-indexed, of `tasInputs`), 2,058 instructions in, Mario (`X = 0`) enters `ImposeGravity`
with velocity `$0470`, gravity `$90` and maximum 4, and leaves with speed 5.

Only the arrival at that state is checked by running the model (`native_decide`, as for the
upper bound). The routine's effect is then *derived* from `imposeGravity_nes`, whose
preconditions are checked on that state: this is the pattern for connecting a routine
theorem to legal play.
-/
namespace Smb.Routine

/-- Run `n` instructions of the current frame, as `NES.frame` does; `none` if the frame ends
first. -/
def frameSteps : Nat → NES → Option NES
  | 0, s => some s
  | n + 1, s => if s.frameDone then none else frameSteps n (CPU.step.run s).2

/-- The state `n` instructions into frame `k` (zero-indexed) of `inputs`, starting from the
fixed initial state as `beatenBy` does. -/
def framePoint (inputs : List UInt8) (k n : Nat) : Option NES :=
  let s := NES.runFrames (inputs.take k) initial
  frameSteps n { s with pad0 := inputs.getD k 0, pad1 := 0, polls := 0, frameDone := false }

theorem speed5Point_isSome : (framePoint tasInputs 336 2058).isSome := by native_decide

/-- The state at Mario's `ImposeGravity` call in frame 336 of the TAS. -/
def speed5Point : NES := (framePoint tasInputs 336 2058).get speed5Point_isSome

/-- Everything `imposeGravity_nes` needs, and the inputs to the call. -/
def speed5Facts (s : NES) : Bool :=
  s.ram.size == 0x800 && s.ctrl &&& 0x80 == 0 && !s.nmiPending && !s.nmiPolled && !s.dmaPending &&
  decide (s.prg = Smb.prg) && s.pc == 0xBFD7 && s.p &&& 4 != 0 && s.x == 0 && s.a == 0 &&
  ramAt s 0 == 0x90 && ramAt s 2 == 4 && ramAt s (ySpeedIdx 0) == 4 && ramAt s (yForceIdx 0) == 0x70

theorem speed5Point_facts : speed5Facts speed5Point = true := by native_decide

/-- The speed byte of a velocity. (Kept separate: `bv_decide` on the goal below would see the
closed TAS terms as constants and try to evaluate them in the kernel.) -/
theorem speed_of_vel (ram : UInt16 → UInt8) (x : UInt8) {v : UInt16} (h : yvel16 ram x = v) :
    ram (ySpeedIdx x) = (v >>> 8).toUInt8 := by
  subst h; simp only [yvel16]; generalize ram (ySpeedIdx x) = a; generalize ram (yForceIdx x) = b
  bv_decide

/-- Legal TAS inputs bring Mario to an `ImposeGravity` call that sets his downward speed to 5,
one more than the routine's maximum. -/
theorem tas_mario_speed5 :
    framePoint tasInputs 336 2058 = some speed5Point ∧
    ramAt ((CPU.runTo (σ := NES) 0xC046 60).run speed5Point).2 (ySpeedIdx 0) = 5 := by
  refine ⟨by simp [speed5Point], ?_⟩
  have h := speed5Point_facts
  simp only [speed5Facts, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, and_assoc] at h
  obtain ⟨hsize, hctrl, hnmi, hpoll, hdma, hprg, hpc, hp, hx, ha, h0, h2, hspd, hfrc⟩ := h
  have hq : speed5Point.Quiet := ⟨hsize, hctrl, hnmi, hpoll, hdma⟩
  have hx' : speed5Point.x < 0x32 := by rw [hx]; decide
  have hspd' : ramAt speed5Point (ySpeedIdx speed5Point.x) + 0x40 < 0x80 := by rw [hx, hspd]; decide
  have hmax : ramAt speed5Point 2 < 0x40 := by rw [h2]; decide
  obtain ⟨-, -, -, -, -, -, -, hvel, -⟩ := imposeGravity_nes speed5Point hq hprg hpc hp hx' hspd' hmax
  have hv0 : yvel16 (ramAt speed5Point) speed5Point.x = 0x0470 := by
    simp only [yvel16, hx, hspd, hfrc]; decide
  rw [hv0, ha, h0, h2, hx] at hvel
  -- With `A = 0` the upward amount (`$01`) is unused; drop it before evaluating, or the
  -- kernel would evaluate `ramAt speed5Point 1`, i.e. the whole TAS prefix.
  have hg : ∀ up : UInt8, gravityVel 0 0x90 up 4 0x0470 = 0x0500 := fun up => by
    simp only [gravityVel, beq_self_eq_true, Bool.cond_true]; decide
  have hv : yvel16 (ramAt ((CPU.runTo (σ := NES) 0xC046 60).run speed5Point).2) 0 = 0x0500 := by
    rw [hvel]; exact hg _
  exact speed_of_vel _ _ hv

end Smb.Routine
