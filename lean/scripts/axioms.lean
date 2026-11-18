import Smb.LocalBound.HorizontalDistance
import Smb.Goal.OneOne
import Smb.Routine.FrameRun
import Smb.UpperBound
import Smb.Routine.HorizontalLimitNes
import Smb.Routine.AbsCheck
import Smb.Routine.EngineTail
import Smb.Routine.AbsBridge
import Smb.Routine.HandlerFrame
import Smb.Routine.MoveObjectHorizontallyNes
import Smb.Routine.MoveObjectHorizontallyAlias
import Smb.Routine.ImposeGravityNes
import Smb.Routine.ImposeGravityOverflow
import Smb.Routine.ImposeGravityTas
import Smb.Routine.FloorReach
import Smb.Routine.HammerBro
import Smb.Routine.FrameClose
import Smb.Routine.PpuBoot
#print axioms Smb.upper_bound
#check @Smb.upper_bound
#print axioms Smb.Routine.moveObjectHorizontally_nes
#print axioms Smb.Routine.moveObjectHorizontally_alias
#print axioms Smb.Routine.imposeGravity_nes
#print axioms Smb.Routine.imposeGravity_overflow
#print axioms Smb.Routine.gravityVel_withinMax
#print axioms Smb.Routine.gravityVel_mario_speed5
#print axioms Smb.Routine.tas_mario_speed5
#print axioms Smb.Vertical.no_skip
#print axioms Smb.Routine.tas_hammerBro_inherits
#print axioms Smb.Routine.HorizontalLimitNes.frame0_side_limit_nes
#print axioms Smb.Abs.step_eval
#print axioms Smb.Abs.inv_runTo
#print axioms Smb.Routine.EngineTail.tail_nes
#print axioms Smb.Abs.ninv_step
#print axioms Smb.Abs.ninv_runTo
#print axioms Smb.Abs.ginv_stepN
#print axioms Smb.Routine.HandlerFrame.frames
#print axioms Smb.Routine.HandlerFrame.frames_bounds
#print axioms Smb.Routine.FrameGuard.finv_stepN
#print axioms Smb.Routine.Frame.invariant
#print axioms Smb.Routine.Frame.no_guard
#print axioms Smb.Routine.Frame.bounds
#print axioms Smb.Routine.PpuBoot.sch_run

#print axioms Smb.LocalBound.HorizontalDistance.minimum_frames
#print axioms Smb.LocalBound.HorizontalDistance.first_surface_checkpoint

#print axioms Smb.Goal.oneOne_of_deps
#print axioms Smb.Goal.speed_grab
#print axioms Smb.Goal.launch_grab
#print axioms Smb.Goal.tas_milestones
#print axioms Smb.Goal.exitBound_tight
#print axioms Smb.Routine.Launch.launch_run
#print axioms Smb.Routine.Launch.frame0_side_launch_nes
#print axioms Smb.Routine.FrameRun.finv_run
#print axioms Smb.Goal.high_grab_witness
