import Smb.Routine.MovementSubs0
import Smb.Routine.MovementSubs1
import Smb.Routine.MovementSubs2
import Smb.Routine.MovementSubs3

/-!
# A movement frame from each of the states 0–3 (`PlayerMovementSubs`, `$B329`), generated

The four summaries are exposed by `MovementSubs0`–`3`. `PlayerMovementSubs` (crouch flag; `PlayerPhysicsSub`: jump start and X physics; then, through
`JumpEngine`, `OnGroundStateSub`, `JumpSwimSub` or `FallingSub` by `Player_State`) as call
theorems, one per starting state: on the ground (`ms0`), jumping (`ms1`), falling (`ms2`), climbing (`ms3`). The
closed forms come from symbolic execution (`Smb.Summary`). The ground and jumping summaries are generated once
and their exact call theorems are checked in six separate cases to bound peak memory.
The falling summary separates generation from its eight-path call proof; climbing uses
`sym_theorem` to generate and prove its call theorem in one pass. Conditions, each a hypothesis: not changing size (`$070B = 0`), not
swimming (`$0704 = 0`), no jumpspring animating (`$070E = 0`), downward speed byte below `$40`.
The flags and the cycle count are left existential (the physics callee leaves its cycles
unspecified). The routine returns through `OnGroundStateSub` (`$B36C`) or `ImposeGravity`
(`$C046`); the end PC is part of the closed form.
-/
