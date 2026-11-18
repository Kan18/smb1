# Level transition timing

The game's 21-tick rule comes from `IntervalTimerControl` (`$077F`), inside
the vertical blank interrupt handler at `$80F0`–`$8119`. An enabled timer tick
subtracts one from the counter, wrapping from 0 to 20. The interval timers
(`$0795`–`$07A3`) decrement on the wrap, and the frame timers
(`$0780`–`$0794`) decrement on each tick.

[`TimerStep`](../lean/Smb/Routine/TimerStep.lean) proves the update rule and
the 21-tick period for counts 0 through 20. With `TimerControl` at least 2
the handler decrements it and skips these timers. At value 1 it decrements
to 0 and permits a tick. Pause also prevents the timer block from executing.
A video frame can end while the previous interrupt is still running.
A controller poll, a timer tick, and a completed game update are distinct
events. A universal elapsed-time bound must connect them.

## From an area change to first control

The formulas below describe the recorded route. The proof still needs to
cover all relevant entry states and interruptions. Indices are zero-based,
and denote the state after that frame.

Let `A` be the frame on which the game-mode task becomes 0. The observed
sequence is two frames for area initialization (the second without a timer
tick), then screen tasks through `A + 8`. An intermediate screen appears if
`AltEntranceControl = 0` and either the area is a castle or the intermediate
screen has not been disabled.

- Without the intermediate screen, engine state 7 is reached at `A + 26`.
- With it, let `r = (ITC(A) - 7) mod 21`. The seventh wrap after the
  intermediate screen begins is at `W = A + 8 + (r + 1) + 6 * 21`.
  Engine state 7 is reached at `W + 18`. At `V = W + 20`, ITC is 0.
- From state 7, the observed time to state 8 is 1 frame for an ordinary
  start, 17 for the high entrance at Y = `$20`, and 96 for a pipe exit.
  The next frame is the first whose input reaches player control.

Vertical pipe entry reaches `A` after 48 frames on the observed route.
Side pipe entry uses `ChangeAreaTimer`, generally 160 on screen page 0
and 52 otherwise. A special entrance can lead straight to another area
change, as in the scripted pipe intro.

## From a flag grab to an area change

Let `G` be the grab and `S` the end of the slide. With Y ≥ 162 the slide
ends on `G`. Otherwise the slide takes 61 or 62 frames depending on the
flag slot's inherited subpixel byte. Let `D` be the end of the castle walk
and `T` the time left on the clock at the grab.

| Event | Observed timing |
|---|---|
| Timer tally ends | `s3 = D + T + 1` |
| Fireworks and delay end | `s4 = s3 + 32 + F`. Last digit 1, 3, or 6 calls for that many fireworks, otherwise zero. The three- and six-firework delays also depend on the star flag's slot |
| Interval-timer limiter | `w5 = s4 + ITC(s4) + 1 + 5 * 21` |
| Music limiter | `s5 = max(w5, music_start + 324)` |
| Mode task resets | `A = s5 + 1` |

The 324-frame music floor is measured. The walk duration depends on grab
height and level geometry. A grab at Y = 165–167 can cause an immediate wall
collision as the castle walk begins, cutting it to one or two frames.
The target uses this in 8-2. [World 1-1](lower-bound-1-1.md#flag-height-and-the-frame-rule)
describes the remaining reachability question there.

## Frame-rule margins

From one intermediate-screen anchor `V` to the next, the observed count is
`21 * (ceil(tau / 21) + K)` enabled ticks. For the ordinary flag calculation
with music out of the way, `tau` counts the ticks to `s4` and `K = 13`.
For a warp pipe, `tau` is the ticks to entry plus 56 and `K = 7`.

| TAS section | Limiting tick count | Ticks to save for one earlier rule |
|---|---:|---:|
| 1-1 | 1,618 | 1 |
| 1-2 | 1,710 | 9 |
| 4-1 | 1,941 | 9 |
| 4-2 | 1,568 | 14 |
| 8-1 | 2,769 | 18 |
| 8-2 | 1,867 | 19 |
| 8-3 | 1,816 | 10 |

A route change can affect the limiting count through the grab time, timer
tally, fireworks, music start, and transitions. Pause can also change RNG
and later gameplay, so a measured delay on one path is insufficient for
excluding it. The [timing tools](../analysis/frame_timing/README.md) produce
the TAS trace and compare these formulas against the recorded events.
