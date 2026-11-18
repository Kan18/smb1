# Toward a lower bound on World 1-1

[`OneOneOptimal`](../lean/Smb/Goal/OneOne.lean) asks whether any sequence of
fewer than **1,943 inputs** can reach gameplay in another world or level, or
leave the supported model. The upper limit is tight because the target TAS
leaves 1-1 at exactly 1,943. The universal lower bound is open.

The exit test requires gameplay mode as well as a changed world or level byte.
At startup both bytes are `$FF`, so a check on those bytes alone would
incorrectly count the empty input sequence as an exit. A change to those bytes
during gameplay still counts, including one caused by a glitch.

## Route milestones

Frame counts below count completed inputs. The surface-to-bonus and return
pipes change Mario's coordinates directly, so distance divided by running
speed only bounds the sections between transitions.

| Completed inputs | TAS milestone | Frames since previous milestone |
|---:|---|---:|
| 195 | Control starts | 195 |
| 563 | Enter the bonus pipe | 368 |
| 654 | Control in the bonus room | 91 |
| 765 | Enter the return pipe | 111 |
| 1,047 | Control on the surface | 282 |
| 1,287 | Grab the flag at Y = 164 | 240 |
| 1,943 | Leave 1-1 | 656 |

`tas_milestones`, `tas_clean`, and `tas_leaves` in
[`OneOne.lean`](../lean/Smb/Goal/OneOne.lean) certify these milestones, the
buffer assumptions along the TAS, and its exit. Use
[`milestones.c`](../analysis/one_one/milestones.c) to inspect the route.

The candidate lower bound is a graph with milestones for control, death and
respawn, pipes, and the flag. Its checked graph calculation gives earliest
candidate grabs of 1,287 for a low grab and 1,260 for a high or walk-skip grab.
To apply that calculation, `oneOne_of_deps` needs every route to either
stay in 1-1 or follow the graph with the stated edge costs. It also needs
supportedness, a minimum time to first control, and a lower bound from the
chosen flag grab to the exit. These are the open fields of `Deps` for runs
with the model's `NoOverflow` assumption. `DirtyBound` is the open obligation
for runs outside those limits.

## What the movement proofs establish

- [`HorizontalDistance`](../lean/Smb/LocalBound/HorizontalDistance.lean)
  derives a minimum of `ceil(distance / 640)` ordinary updates when the
  hypotheses ensure at most 640 subpixels (2.5 pixels) of forward progress
  per update, with position preserved between updates. It also gives a
  conditional 350-update bound for reaching the first surface checkpoint.
- [`LaunchRun`](../lean/Smb/Goal/LaunchRun.lean) proves adherence to the
  launch movement model under its entry and frame hypotheses. Its
  `pipe_368'` gives 368 frames for the surface distance to the pipe, given
  the launch state, timing, and speed conditions. The first 33 frames are
  where acceleration makes a difference.
- [`PlayCycle`](../lean/Smb/Routine/PlayCycle.lean) composes checked regions
  across the handler, player, enemies, tail and parser. The cycle includes
  normal play with the flag loaded and the pipe-entry update. It has explicit
  exits for phase changes.
  [`PlayCycleWitness`](../lean/Smb/Goal/PlayCycleWitness.lean) proves entry
  into the invariant along the TAS at completed-input counts 195–610 and
  1,047–1,286.
- [`FramesBound`](../lean/Smb/Routine/FramesBound.lean) and
  [`FramesLaunch`](../lean/Smb/Routine/FramesLaunch.lean) extend player-call
  facts to video frames, subject to the entry conditions and the absence of
  odd frames. The bounds are 2.5 pixels forward and 4 pixels in absolute
  horizontal pixel displacement per frame. A lagging or repeated player
  call and a phase exit need separate handling.
  [`LaunchRunCycle`](../lean/Smb/Goal/LaunchRunCycle.lean) and
  [`ExitRunCycle`](../lean/Smb/Goal/ExitRunCycle.lean) use these results for
  the surface stretches.

Connecting the launch invariant at first control to `CycleInv` is an open
obligation. The frame bounds also require `EntryOK` at each player call,
which includes a vertical speed bound and a relation between Mario's world
position, the saved screen coordinate `$0755`, and the side-collision timer
`$0785`. Injury blinking can leave the saved coordinate one frame old.
The ROM facts about the normal position copy
and timer decay are in [`TailCopy`](../lean/Smb/Routine/TailCopy.lean) and
[`TimerKeep`](../lean/Smb/Routine/TimerKeep.lean).

One proposed proof carries the relation across complete gameplay updates.
A normal copy refreshes the coordinate. An injury blink skips it on odd
frame-counter parity, so the stale value must be bounded by the displacement
since the previous update. A paused frame keeps the counter and timer.
The proposed relation uses `d = player X - left edge` at the end of a frame.

- If `$0755 >= $50` and `$0785 <= 1`, then `$49 <= d <= $F0`.
- On even frame-counter parity, `$0755 >= $50` implies either
  `$50 <= d <= $F0` or `d = $FFFF` with `$0785 >= 3`.

A copy frame should establish both clauses. A blink frame would inherit
the first from the previous even frame, allowing for a retreat of at most
7 pixels relative to the edge. This needs the region to carry relative
position through the tail and a separate case for frames ending before
the tail has run. The across-frame invariant remains open.
[`PlayWritersAll`](../lean/Smb/Routine/PlayWritersAll.lean) is the optional
target for checking the writer sets, including the frame counter, saved
coordinate, and side timer.

## Flag height and the frame rule

The TAS grabs low at Y = 164. A high grab at Y ≤ 161 adds a flag slide and
changes the castle walk. The checked `high_grab_witness` grabs six frames
earlier at Y = 138, then leaves 21 frames later. A 240-frame lower bound on
the flag approach therefore only makes sense for low grabs.

A grab in Y = 165–167 can skip the castle walk. The vertical model's
[`JumpBand`](../lean/Smb/Movement/JumpBand.lean) result narrows when an
ordinary launch from the ground can rise through this band. A real exclusion
would also need horizontal collision geometry and exceptional paths such as
stomps and clips. The goal only needs to rule out a skip fast enough to gain
a frame rule. See [frame timing](frame-timing.md) and the
[walk-skip probes](../analysis/walk_skip/README.md).

The TAS's limiting count is one tick beyond a 21-tick boundary.
The trace shows 370 on the clock at the grab. An earlier grab can
also change the timer tally, so a saved frame must be evaluated against
the resulting limiting count. The castle walk, countdown, and music floor
still need ROM arguments that cover alternate states.

## VRAM buffer corruption

The normal-play proof assumes at every instruction that buffer 1's offset
`$0300` is at most `$34` and buffer 2's offset `$0340` is at most `$21`
during play (`$90` otherwise). The TAS meets those limits in 1-1. Replacing
them requires reasoning over the bytes each writer can emit, the schedule of
those writes, and the consequences if they land on live game state.

- **Counts.** A surface window between buffer-1 clears has at most four
  updates under the parser-only scheduling hypotheses. The conditional
  record count gives 176 bytes. Coin tiles can keep a window open in the
  bonus room. Bounding that window needs the coin layout and movement
  reach there. Four pixels per update lets the surface reach argument touch
  three columns, so the assumed two-head-hit count needs tighter reasoning
  or an independent cooldown argument.
- **Contents.** [`Window`](../lean/Smb/Buffer/Window.lean) confines relocated
  buffer-2 stores to `$0341`–`$03DD` when the offset is below `$80`.
  [`Landing`](../lean/Smb/Buffer/Landing.lean) narrows which surface records can
  put a value at `$0340` that then writes `$03A1`. Under its record, count,
  and decimal-digit hypotheses the record is a head-hit block, starting at
  offset 54, 55, 59, or 62. This leaves a concrete question about awards and
  blocks that can coexist in one window. The surface and bonus-room parser
  states still need to be distinguished to rule out surface coin tiles.
- **Effects.** `$03A1` feeds the camera and can cause the screen-edge clamp
  to advance Mario. A sufficiently large offset could reach `$03EE`, the
  block-object index, and redirect later stores. A stale buffer header can
  also affect rendering and the sprite-zero wait. Edited-state probes
  reveal these mechanisms. A legal run that produces the requisite bytes
  at the requisite times remains to be established.

See [buffer semantics](buffer-semantics.md) for the checked record formulas
and [the cell map](buffer-cell-map.md) for downstream readers.
