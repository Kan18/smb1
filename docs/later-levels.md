# Extending the proof beyond World 1-1

A whole-game proof will need bounds for ordinary movement and for the
transitions that can change position, control, or destination. The checked
regions used in 1-1 have level-specific entry and memory constraints.

## What needs to change

| 1-1 assumption or proof scope | Later-level obligation |
|---|---|
| Buffer 1 offset at most `$34` | The TAS reaches 67 in 4-1 and 8-2. Reason about which buffer records can overlap live state and when |
| No vine, exits at `$B93E` | Vines occur on the route. Bound `$0398`, the index for the store at `$B93E`, and cover climbing and dismount movement |
| Limited enemy IDs and slots | Cover frenzy, platforms and Bowser. High bits in slot flags select the parent path at `$D741` |
| Parser state follows the area's forward chain | In castles, `ExecGameLoopback` can rewind the player, camera and parser by four pages. Account for a graph of parser states |
| Ordinary player calls | Add swimming, jumpsprings, size changes, and phase exits. Prove the vertical-speed and saved screen-position premises |
| At most one complete player call per frame | Bound call scheduling when the handler runs late. Keep distinct the frame boundary, controller read and gameplay update |

The parser's exact saved tuples let the region checker track object counters
together with their place in the level stream. The TAS visits 347 such states
at `$AF67` in 1-1, and closing the chain gives 1,318. The TAS's later levels
visit between 499 and 1,490 states each. Retain the area pointer in the tuple:
the surface and bonus room have different metatiles. A respawn or pipe entry
can backload several objects in one parser pass through `$0728` and `$0729`.
The staircase counter starts at 9 and decrements length + 1 times, so areas
with stairs of length 9 or more would need a different argument.

[`level_facts.c`](../analysis/engine_bounds/level_facts.c) reports the
target's area types, buffer offset peaks, and enemy slot use. The targets
below use zero-based aligned indices. Buffer peaks are measured at frame
boundaries while `OperMode_Task` is 3.

| Level | First gameplay-mode frame in level | `$0300` peak | `$0340` peak |
|---|---:|---:|---:|
| 1-1 | 40 | 42 | 29 |
| 1-2 | 1,942 | 44 | 29 |
| 4-1 | 3,764 | 67 | 29 |
| 4-2 | 6,040 | 44 | 29 |
| 8-1 | 7,721 | 27 | 29 |
| 8-2 | 10,811 | 67 | 29 |
| 8-3 | 12,954 | 31 | 29 |
| 8-4 | 15,055 | 21 | 29 |

## Pipes, scrolling, and area loads

An ordinary pipe can change area without changing world or level. A warp can
change world and level when Mario contacts the pipe, before the mode
countdown, initialization, and parser preparation. Those stages can change
the area pointer again before control starts.

[`PositivePipeCaller`](../lean/Smb/Routine/PositivePipeCaller.lean) links
`LandPlyr` at `$DD44` to the destination routine at `$DEE8` under its
foot-tile and input conditions. [`WarpDestination`](../lean/Smb/Routine/WarpDestination.lean)
checks the actual destination table. For 1-2 the ordinary warp selector
depends on the area and whether the warp text writer has run. Establish the
selector's history before reasoning from it.
[`WarpAreaBridge`](../lean/Smb/Routine/WarpAreaBridge.lean) proves area
initialization preserves world, level, area, pointer, power, interval phase
and RNG seed while clearing the warp selector and frame counter. It still
needs the conditions at entry, including what the preceding countdown
leaves.

Two places on the target route make the camera part of the timing problem:

- **4-2 wrong warp.** Entering the pipe with Mario at X ≥ 1,348 can still
  load the coin room. Each descent frame scrolls by the last walking
  update's pixel step, and a later row-`0E` command can replace
  `AreaPointer` from `$2F` to `$42` before load. The target uses side
  collisions to hold the camera back, then brakes so the entry update
  moves Mario zero whole pixels. A search that ranks only Mario's distance
  can drop this setup long before the pipe.
- **8-4 turnaround room.** The return pipe goes to water only after
  the camera reaches X = 3,345, where a row-`0E` command changes the
  pointer from `$65` to `$02`. Earlier entries can loop the room.
  The wall jump, turnaround, and water exit need their own bounds.
  Area `$65` contains a Hammer Bro at X = `$1110` within the entrance
  scan window. A proof ruling out an alternative entrance with stale
  `AltEntranceControl` must account for that enemy.

For a tighter route graph, carry at least power and movement state, the
camera and parser, the timer phases, and RNG. The assumptions needed to
abstract away other CPU and graphics timing state remain open.

## Enemy state and the flag

- In 8-2 the TAS reaches the walk-skip band by rising after a stomp.
  The pole expects Mario's X low nibble in 6–9. Which grab heights gain
  time depends on the timer and transition phase of the specific level.
- If slots 0–4 are occupied at castle creation, the star flag can overwrite
  the flagpole flag in slot 5. `FlagpoleSlide` at `$B2A4` then skips the
  slide because the slot lacks ID `$30`. The cost of keeping the slots
  occupied must be included in any route using this mechanism.
- A Hammer Bro can inherit a jump countdown from an earlier occupant.
  [`HammerBro`](../lean/Smb/Routine/HammerBro.lean) proves the local
  initialization behavior and confirms it occurs on the target in 8-3.
  Partner slots, spawn capacity and retained fields may need similar
  treatment for platforms and other enemies.
- A Koopa stomped at Y = `$C5` can revive with
  `(Y + $3E) & $FF = $03`, below the terrain-probe threshold at
  `$E15B`. A floor-support argument must include that guard. Enemy
  probes at low Y can also read beyond the usual block-buffer rows.

## Buffer overflow in 1-2

A buffer-1 record that reaches `$0340` can leave a nonzero buffer-2 offset
and stale bytes at the start of buffer 2. The next graphics upload may
interpret those bytes as a record before the relocated column. A bad
status-bar write can remove the sprite-zero collision and leave the NMI
handler waiting at `$8150`. A lower bound needs to account for these
effects even when the relocated record misses live game RAM.

Large offsets can reach `$03EE`, the block-object index. In a ROM sweep
with edited offsets, `$90` put only a zero terminator there. Offsets
`$92`–`$9E` can put a column byte there. This makes head hits in page
columns 9–15 interesting because a block record can supply those offset
values. See [the sweep](../analysis/buffer/sweep_0340_12.c) and
[record formulas](buffer-semantics.md).

One way to overwrite the block-object index needs the head-hit record
to start at exactly offset 62. The proposed alignment is four 14-byte
score/coin records plus the six-byte timer record. The head-hit cooldown
uses `$0784` (set to `$10`). A proof using it needs to cover every writer
and account for the intervening updates. A power-up or injury delays the
next controllable hit. The parser and coin pickup schedule also constrain
when the corrupted offset will survive to a render.

The unresolved cases include ceiling rows near columns 40–47, 56–63,
72–79, 88–92 and 105–111. At 41–42, side collisions can hold the camera
far enough back to keep Goomba 29 on screen while the earlier Koopa pair
has spawned. An input experiment reached the ceiling hit with that camera
position. Aligning the payouts, coin, timer and parser phase remains open.
[`screen_x_beam.c`](../analysis/buffer/screen_x_beam.c) searches for these
camera setups from a supplied checkpoint. A legal replay reaching the
complete overwrite and gaining time has not been established here.
