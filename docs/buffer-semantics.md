# VRAM buffer semantics

The level-independent half of replacing `NoOverflow`: what the ROM does to VRAM buffer 1 (`$0300` offset, data
from `$0301`) and buffer 2 (`$0340`, from `$0341`). The local record proofs
can be reused across levels. Each level still has to establish record values,
event rates, and the effect of any misplaced writes. The plan, and why it's split this way, is in [lower-bound-1-1.md](lower-bound-1-1.md#vram-buffer-corruption).
Lean is in [`lean/Smb/Buffer`](../lean/Smb/Buffer).

## How the records are stated

A symbolic summary describes what the ROM routine does under its entry
hypotheses, which can include offsets outside the buffer. The record lemmas
describe the contiguous writes from `$0301 + o` when the index cannot wrap.
They state the new `$0300` value and account for the routine's working bytes
and stack. The clean statements bound the offset so that the 8-bit index doesn't wrap, which is the case a bound
on the offset is about. That doesn't keep a record below `$0400`: at the largest offsets they allow, the status
record's terminator (offset 246) and the player palette's (248) land on `$0400`, Mario's X sub-pixel. The
lemmas say so exactly; a proof that the buffer stays clear of `$0400` needs a smaller offset bound. [`Addr`](../lean/Smb/Buffer/Addr.lean) has the rewrites that
let a symbolic run drop aliases a byte index can't produce: an indexed buffer address never equals a fixed one
outside its 256-byte range, the stack, or a ROM table.

The proofs check their code and table bytes against the supplied cartridge
with `native_decide` (`*_in_rom`).

## What's proved

| Writer | Record from `$0301 + o` | Offset | Lean |
|---|---|---|---|
| NMI `InitBuffer` (`$80C6`) | Clears buffer 1's header (`$0300`, `$0301`) unless `$0773` = 6, when it clears buffer 2's instead | 0 | `NmiClear` |
| `OutputNumbers` (`$8F11`), selectors 0–5 | `hi lo len` digits `0` | `o + len + 3` | `StatusRecord` |
| `WriteBlockMetatile` (`$8A6D`), four tile kinds | `hi lo 2 t0 t1 hi lo+$20 2 t2 t3 0` | `o + 10` | `BlockRecord` |
| `GetPlayerColors` (`$85F1`) | `$3F $10 $04` background color, three player colors, `0` | `o + 7` | `PaletteRecord` |
| `ColorRotation` (`$89E1`), when `$09 &&& 7 = 0` and `o < $31` | `$3F $0C $04` palette 3 with the rotating color, `0` | `o + 7` | `PaletteRecord` |
| `UpdateNumber` (`$BC36`) for player 1 (`$02`) or 2 (`$13`) | coin record, then score record over its terminator, leading zero as `$24` | `o + 14` | `StatusUpdate` |
| `WriteBottomStatusLine`'s world and level (`$865D`) | `$20 $73 $03` world+1 `$28` level+1 `0` | `o + 6` | `SetupRecord` |
| `OutputNumbers` with selector 6 and up | nothing; the timer's second, high-nybble call | `o` | `SetupRecord` |

The status selectors: 0 is the title's top score (`$22F0`), 1 and 2 the score (`$2062`, 6 digits), 3 and 4 the
coins (`$206D`, 2), 5 the timer (`$207A`, 3). A block's address is computed from the block-buffer row offset `$02`
and pointer `$06` with the ROM's own arithmetic (`blockLo`, `blockHi`). The player palette's background color is
read through `$0744` or the area type `$074E`, and the rotation's colors through `$074E` and `$06D4`; the records
give them as the ROM bytes at those indices, so a level's proof has to bound the indices. `ColorRotation` changes
nothing when its guard fails, and when it writes, its record ends below `$0339`, so it can never reach `$0340`.

## Which code produces each record

The following ROM call sites are starting points for bounding event
rates on a particular level.

| Record | Reached from |
|---|---|
| Score/coin update (14 bytes) | `AddToScore`: floatey-number awards (`LoadNumTiles`), the flagpole score (`GiveFPScr`), a broken brick (`BrickShatter`), and every coin through `GiveOneCoin` → `CoinPoints` (a coin block's jumping coin `JCoinC`, a coin tile `HandleCoinMetatile`); also `ELPGive` (extra-life reward) and `WriteTopScore` |
| Timer (6 bytes) | `RunGameTimer` → `ResGTCtrl`, from the main object loop |
| Block (10 bytes) | `DestroyBlockMetatile` from a block hit (`DBlockSte`), `ReplaceBlockMetatile` from a block object finishing (`UpdateLoop`); `RemBridge`/`MoveVOffset` from `RemoveBridge` (Bowser's bridge) |
| Player palette (7) | the intermediate screen (`SetupIntermediate`, the screen-routine fall-through), level start (`SetStPos`), a power-up (`Shroom_Flower_PUp`), losing one (`ForceInjury`) |
| Color rotation (7) | the main object loop (`ProcELoop`) |
| Rope (10) | balance platforms (`DoOtherPlatform`), only below offset `$20` |
| World/level (6), game text, warp numbers | screen routines only: `WriteBottomStatusLine` (jump table), `WriteGameText` (top status line, intermediate screens, game over, warp zones), `PrintWarpZoneNumbers` (from `EndGameText`) |
| Coin-tile erase (buffer 2 at `$0341`, sets `$0773` to 6) | `RemoveCoin_Axe`: a coin above a broken brick (`CheckTopOfBlock`), a coin tile or the axe (`ErACM`) |

## Relocation: buffer 2's writers at `$0341 + v`

The column and attribute writers read `v = $0340` and start at
`$0341 + v`. Each store adds an 8-bit index to its own base address, so
later parts of the record can wrap to lower addresses. The highest
possible store address is `$0443`.

| Writer | Stores, all indices mod 256 | Then |
|---|---|---|
| Column | header `$0341+v` (`CurrentNTAddr` high), `$0342+v` (low), `$0343+v` (`$9A`); row `r` < 13: tiles at `$0344+(v+2r)`, `$0345+(v+2r)`; terminator `$0341+(v+29)` | `$0340 := v + 29`, `$0773 := 6` |
| Attribute | row `r` < 7: `$0341+(v+4r)` (`$23`/`$27`), `$0342+(v+4r)` (address low), `$0343+(v+4r)` (`$01`), `$0344+(v+4r)` (`AttributeBuffer[r]`); terminator `$0341+(v+28)` | `$0340 := v + 28`, `$0773 := 6` |

Equivalently, a column pass can write a byte `A` in `$0360`–`$043C` exactly when `A − $035E ≤ v ≤ A − $0341`,
and an attribute pass when `A − $035D ≤ v ≤ A − $0341` (`GeneralAddressClasses.lean` checks both for every
address and every `v`). The column's tile bytes are read through `MetatileGraphics` at `$8B08`/`$8B0C`: one of
four palette tables at `$8B10`, `$8BAC`, `$8C64`, `$8C8C`, at an index below 256, so 179 possible values, `$00`–`$EB`.
A level's metatiles narrow this.

In Lean:

- **Attribute** (`RenderAttribute`): a ROM summary with `v` symbolic and
  `ratt_ram_record`: for `v ≤ $9B`, which keeps it clear of `AttributeBuffer`, the 29-byte record at `$0341 + v`
  with the address arithmetic stated (`attrHi`, `attrBase`), and `$0340` moved to `v + 28`.
- **Column**, in three pieces, each from the ROM: the header (`ColumnEnds.chead_ram_record`: `CurrentNTAddr` high
  and low and `$9A` at `$0341 + v`, with `v` saved in `$00`), the 13 rows ([`Buffer/Renderer`](../lean/Smb/Buffer/Renderer): `RowCompose.thirteen_rows` runs them with `$00` moving by 2 a row,
  `ExactMoveStore.every_row_left_store`/`_right_store` give each row's tile stores at `$0344`/`$0345 + $00`), and
  the tail (`ColumnEnds.ctail_terminator`: the terminator at `$0341 + ($00 + 3)` and `$0340 := $00 + 3`).
  `GeneralAddressClasses` checks the address formulas over all byte offsets
  and the stated address band.

What the stray bytes then do is the [cell map](buffer-cell-map.md): which routines read each field in that range.

## Layer B: what a window can do (`Window`)

Given Layer C's facts as hypotheses on the RAM a record reads, these are proved by computation over Layer A's
record definitions:

| Theorem | Says | Hypothesis (Layer C must prove for 1-1) |
|---|---|---|
| `upd1Fields_low`, `upd2Fields_low` | a score/coin update's bytes are all below `$80` | its eight digits are below `$80` (`Digit`) |
| `st5Fields_low` | so are the timer's | its three digits are below `$80` |
| `blkFields_low` | so are a block's, any kind | the row offset `$02` is a surface row: `$30`, `$60`, `$70` or `$A0` |
| `pcolFields_low_rom` | so are the player palette's, on the game's ROM | background index below 8 (`bgColors_low` checks the ROM's `BackgroundColors` table) |
| `crot_short` | color rotation's record ends before `$0340` | none: its own guard |
| `relocation_reach` | from a buffer-2 offset below `$80`, every column and attribute store is in `$0341`–`$03DD` | none |
| `surface_window` | the window's offset is at most 176, so its stores stay at or below `$03B1` (`surface_reach`) | per window: 6 floatey awards, the flag's score, one block replacement, one each of timer, rotation and palette (`Schedule` proves all but the palette), and at most 2 head hits, each a score/coin update and a block |

Together: if every byte a buffer-1 store leaves in `$0340` comes from these records, the next render writes no
further than `$03DD`, so it never reaches the block objects, `$03EE`, `AttributeBuffer` or Mario's sub-pixels.
The [cell map](buffer-cell-map.md) lists readers of the reachable fields
and the effects observed in edited runs.

## Layer C, first fact: the digits ([`Buffer/Digits`](../lean/Smb/Buffer/Digits))

Layer B needs every displayed digit below `$80`. The narrower byte
classification in [`Landing`](../lean/Smb/Buffer/Landing.lean) uses decimal
digits. Its `digitResult_decimal` lemma preserves 0–9 for a signed modifier
of at most 10. Applying it to a run requires bounds on the digits, their
modifiers, and their writers.

`DigitMath.one_store_below_8f_nes` runs `DigitsMathRoutine`'s
store (`$8F68`–`$8F78`) on the NES and shows the digit it writes is at most `$75`, whatever the old digit and the
amount (the routine tests the sign before the decimal carry; `$7F + 0` gives `$75`, so the bound is tight).
`copied_digit_below_8f_nes` carries the bound through `OutputNumbers`' copy into buffer 1, and
`DigitInvariant.run_good` keeps it over any trace of resets, small sets, additions and copies. `Window.digit_of_good`
turns it into Layer B's `Digit`.

What's left of this fact is the trace's side condition: that nothing else writes `$07D7`–`$07FA`. The ordinary writers are `StoreNewD` (`$8F75`), `CopyScore` (`$8FB2`, copying a
player's score to the top score, so the bound carries), `InitScores` (zeros) and `SetStPos`, which loads the timer's
start from the level header. Besides those, 34 other indexed stores (enemy timers, the area parser's length
counters, the sound and timer clears, `RotPRandomBit`'s `ror`, and others) reach these cells only with an index
past their own tables. Nine indirect stores can't be placed by syntax: `InitByte` (zeros, during memory init), the
title-screen copy `OutputTScr`, and seven block-buffer and metatile writers that go through a pointer into the
block buffers. Excluding the out-of-table indices and pointers is the same stray-store question as for `$0340`.

## Layer C, the surface's counts ([`Schedule`](../lean/Smb/Buffer/Schedule.lean), [`ScheduleRom`](../lean/Smb/Buffer/ScheduleRom.lean))

Each count is a small automaton over the cells that schedule its event, with the automaton's step proved from or
checked against the ROM:

| Count | Automaton | From the ROM |
|---|---|---|
| A window is at most 4 updates | `parserStep`, the task countdown from 8; `no_four_sixes`: four updates in a row never all end with `$0773` at 6 | `parser_table_renders`: the `AreaParserTasks` table sends tasks 1, 2, 5, 6 to `RenderAreaGraphics` and the rest to `IncrementColumnPos` or `AreaParserCore`; the attribute render follows task 0 |
| One award per floatey slot per window | `slotStep`; `awards_le_one`: at most one award in any 6 updates, from any timer | `floatey_idle`, `floatey_expire`, `floatey_tick`, `floatey_award`: the routine for slot `x`, run symbolically; it reaches `jsr AddToScore` only when the timer it reads is `$2B`, and decrements it |
| One timer print per window | `cooldown_le_one` with `n = $18` | `resGTCtrl_in_rom`: the print's only path sets `GameTimerCtrlTimer` to `$18` first |
| One color rotation per window | `rotation_le_one`: `FrameCounter &&& 7 = 0` holds once in any 8 consecutive values | `crotActive` (Layer A) |
| One block replacement per window | — | `blockUpdater_busy`: `BlockObjMT_Updater` writes nothing to buffer 1 when `$0301` is nonzero, so a delayed replacement only ever opens a window, and the other block object waits |

The count includes the block record written immediately by a head hit,
any score or coin record from that hit, and the later replacement record.
Under the stated event limits the total is
6 × 14 (floatey) + 2 × 24 (head hits) + 14 (flag) + 10 (replacement) + 6 + 7 + 7 = 176.

What these still assume, as hypotheses a whole-run invariant has to supply:
- **Writers.** The schedules rely on the modeled writers of the address
  control, parser task number, score award timers, and game timer. The
  optional [`PlayWritersAll`](../lean/Smb/Routine/PlayWritersAll.lean)
  checks those writer sets under the normal-play cycle's conditions.
  Extending the result to weaker buffer limits requires checking for
  other indexed writes under those limits.
- **Schedule.** `GameEngine` calls each slot's routine once an update, and the frame timers fall by at most one an
  update. `parserStep` transcribes the handler's countdown (`$92B0`–`$92C7`), which is checked byte for byte but
  not run symbolically.
- **No coin tiles on the surface.** `RemoveCoin_Axe` can keep the window open for another update by setting
  the address control to 6. Excluding that case on the surface needs a
  proof about the metatiles the parser can write there.
- **Head hits and palette.** At most 2 head hits and one palette change per 4-update window. Head hits need the
  reach argument: a big Mario breaking a brick keeps rising (`BrickShatter` sets his speed to −2), so the bound
  rests on how many block columns his head point can cross in 4 updates, which needs the horizontal speed limit.

## Still to do

- The level-specific writers: `DrawEraseRope` (guarded below `$20`), `RemoveBridge`, and `WriteGameText` with
  `PrintWarpZoneNumbers`. `WriteGameText` writes from buffer index 0 and doesn't append, and the warp-zone path
  sets the offset to `$2C`, so neither can carry an offset past the buffer.
- The callers of `UpdateNumber` and the block writer (`AddToScore`, `GiveOneCoin`, the floatey numbers, the block
  objects), which say when each event happens: that's where Layer C's rates come from.
- Joining the column's three proved pieces into one theorem: the header (`ColumnEnds.chead_ram_record`), the 13
  rows ([`Buffer/Renderer`](../lean/Smb/Buffer/Renderer)) and the tail
  (`ColumnEnds.ctail_terminator`). Each is proved from the ROM; the composition is chaining their run equations.
- The cell map's per-field classification for each level: which fields' objects can exist there, and which fields
  are rewritten every frame before they're read.
