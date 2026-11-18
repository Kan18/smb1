# The NES model and finish condition

[`Smb.Game`](../lean/Smb/Game.lean) fixes the cartridge, initial state, controller
rules, and finish predicate. [`Smb.Nes`](../lean/Smb/Nes.lean) executes each
controller input through one NTSC video frame. The first frame is partial
because the model starts after power-on and a soft reset. A run of length `n`
means the state after `n` inputs. Replay traces number the first input 0.

## Completion

`finalVictory` requires the byte at `$0770` to be 2 (victory mode), `$075F`
to be 7, and `$075C` to be 3. World and level numbers in RAM start at zero.
The upper bound certifies that combination at a frame boundary.

A whole-game proof must choose its endpoint explicitly. In an aligned replay
of the target, the last nonzero input is at completed-input count 17,848.
The victory-mode store at `$DE15` and the first frame-boundary victory occur
at count 17,866. With neutral input continuing, the routine begins printing
the victory messages at 18,191 and queues selector `$0F` at 18,383. The last
nonzero input gives a property of the recording. Determining the earliest point
at which inputs could stop requires a separate continuation rule and proof.

[`EndingSelector`](../lean/Smb/Routine/EndingSelector.lean) shows that the local
routine queues `$0F` and event music 4 when the primary message counter is 3,
the secondary counter is 0, and the world byte is 7. The level byte can be
arbitrary. The later button gate checks world and timer without checking the
level. Any proof relating displayed text to `finalVictory` must use additional
facts about what game histories can reach those routines.

## Timing and scope

| Behavior | Model |
|---|---|
| Video frame boundary | Scanline 240, dot 0, with the current instruction and accepted interrupt entry completed |
| CPU bus cycle | One PPU dot before the access, NMI edge sampled after the second dot, then the third dot |
| Vblank | Set at scanline 241, dot 1. Reading status at dot 0 can suppress it |
| NMI | Separate edge latch and instruction poll. Branches have special polling rules |
| OAM DMA | Waits for a read, then stalls for 513 or 514 cycles. The last consecutive write selects the page |
| Sprite status | Sprite-zero hit appears after the pixel collision. Status reads latch vblank at the start and sample sprite flags at the end |
| Open bus | Driven bit groups refresh and decay on a deterministic schedule |

A sticky `unmodelled` flag marks cases outside the implemented hardware
behavior. Examples include APU status reads, DMC DMA, IRQ enable, and certain
changes to rendering or addressing during visible scanlines. The model
tracks CPU-visible graphics events and approximates some hardware timing.
The relationship to a physical NES remains unproved.

[`LowerBound`](../lean/Smb/Game.lean) requires every shorter input sequence
to remain supported and fail to win. A run that trips a support guard leaves
its outcome unresolved. The proof also needs to account for glitches which
change the sequence of game updates, overwrite tracked RAM, or take an
unexpected route through the original code.
