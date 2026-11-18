# The cell map: what a relocated buffer write can reach

A corrupted buffer-2 offset `v` makes the next column or attribute record
start at `$0341 + v`. Its 8-bit index can wrap within the record. All of
these stores stay within `$0341`–`$0443`. See [the record formulas](buffer-semantics.md).
The tables list the ROM's ordinary readers and writers of fields in
that range. A proof must also cover indexed and indirect accesses whose
effective address reaches a field with an unexpected index or pointer.

## How a level uses it

A safety argument for a relocated write can use one of three kinds of evidence.

1. **The object doesn't exist in the level.** Bowser (`$0363`–`$036A`), firebars (`$0388`), vines (`$0398`–`$039D`),
   balance and lift platforms (`$03A0`–`$03A2`, `$0401`), and bubbles
   (`$03B0`, `$03BB`, `$03D3`, `$042C`). A proof must exclude every
   relevant reader on the path under consideration. Some fields have
   readers outside the object routines. For example,
   `BowserGfxFlag` is read by ordinary enemy graphics code.
2. **The field is rewritten every frame before it's read.** The relative positions (`$03AD`–`$03BE`) come from
   `GetObjRelativePosition` and the offscreen bits (`$03D0`–`$03D6`) from `GetOffScreenBitsSet` before the drawing
   and collision code use them. Whether that order holds on every path is a per-routine fact to prove; the
   `$0340` sweep's runs that converged after a few frames are consistent with it.
3. **Persistent state that changes play.** `$03D8` (enemy offscreen mask, read by enemy collisions),
   `$03E4`–`$03F1` (the block objects, including `$03EE`, the block-hit index behind the zero-page chain),
   `$03F9`–`$03FF` (`AttributeBuffer`), `$0400` (Mario's X sub-pixel), `$0416`/`$0417` (vertical sub-pixels),
   `$0433`/`$0434` (vertical move force) and `$043C`. These need an argument that a record can't reach them, or an
   accounting of what it does.

Under the [surface record hypotheses](buffer-semantics.md), a buffer-1
byte that reaches `$0340` is below `$80`. The relocated record then
stays within `$0341`–`$03DD`, which includes the enemy offscreen mask at
`$03D8` and stops short of the block-object fields starting at `$03E4`.

## Which reachable cells matter on 1-1's surface (measured)

[`rewrite_probe.c`](../analysis/buffer/rewrite_probe.c) forces each cell from `$0363` to `$03DC` to four values at the
start of a TAS frame on 1-1's surface (every seventh frame from 200 to 1187, 93 frames) and compares game RAM two
frames later with the unedited run, ignoring sprite memory, the buffers and the cell itself. Only three cells ever
made a difference:

| Cell | Changed | Why |
|---|---|---|
| `$036A` `BowserGfxFlag` | 320 of 372 runs | read by the enemy-graphics code for every enemy (`CheckForESymmetry`, `MirrorEnemyGfx`) |
| `$03A1` `Platform_X_Scroll` | 284 of 372 | `ScrollHandler` adds it to the scroll amount |
| `$03C4` player sprite attribute | 180 of 372 | read by the player's graphics and pipe code |

The other sampled edits, including those to `$03D8`, produced no
difference in the compared RAM after two frames of TAS inputs. The
comparison measures the outcome at that point. It leaves the order of
intervening reads and writes unresolved.

`$03A1` is the one that bears on time. With Mario at screen X `$70` or more, `ScrollHandler` scrolls by the whole
`Player_X_Scroll`, so a stray value there jumps the camera. [`edit_03a1.c`](../analysis/buffer/edit_03a1.c) forces
it at TAS frames 300, 450 and 1100: values up to `$70` move the screen up to about 100 pixels ahead within five
frames, values from `$80` scroll it slightly back or not at all, and Mario's own position never gains (at `$70` he
loses 6–10 pixels). A relocated column can reach `$03A1` from `$0340` = `$43`–`$60`, and buffer 1 can leave values
in that range on the surface (block address low bytes `$4E`, `$54`; block tiles `$45`–`$5A`). So this path isn't
excluded by bytes; what a jumped camera can change (column parsing, enemy loading, the level end's scroll lock) is
an open obligation.

**One-frame push.** A stray `$03A1` lasts one frame: every path through
`ScrollHandler` ends at `InitPlatScrl`, which clears it. But in that frame the camera moves by the stray value plus
Mario's scroll speed, as long as the sum stays below `$80`. If that leaves Mario left of the screen's edge,
`KeepOnscr` sets his X to the edge, and keeps his speed only if right is held. [`sweep_03a1`](../analysis/buffer/sweep_03a1.c)
forces each value `$40`–`$7F` on every TAS frame from 196 to 559. The one-frame gain is up to 44 px with Mario 80 px
from the screen's left edge (where scrolling starts), falling 2 px for every 2 px further right, to 15 px at 112,
where Mario sits while running. On the TAS's own inputs the gain is lost within about 10 frames, but those inputs
aren't adapted to the edited state. Whether legal inputs can produce
and keep the gain remains open.

**What wider buffer limits break in the checker.** Rerunning the play regions' embedded configs with `$0300` up to
`$D5` and `$0340` up to `$9C` instead of `$34` and `$21`: the tail region raises 24 alarm sites, the parser's tail
link 20 and `H` 2, before the run was stopped. The tail's and parser's are all buffer stores reaching `$0398`
(`VineFlagOffset`, bounded to 0) and `$03A1`. The wider bounds used in this experiment require accounting for writes
to both cells.

## Fields from `$0341` to `$0443`

| Field | Address | Read by | Written by |
|---|---|---|---|
| `VRAM_Buffer2` | `$0341` | — | AttribLoop, RenderAreaGraphics, SetAttrib |
| `BowserBodyControls` | `$0363` | CheckBowserFront, CheckBowserRear, ChkMouth, FeetTmr, RemoveBridge, SpawnFBr | FeetTmr, InitBowser, RemoveBridge, SpawnFBr |
| `BowserFeetCounter` | `$0364` | FeetTmr, RemoveBridge | FeetTmr, InitBowser, RemoveBridge |
| `BowserMovementSpeed` | `$0365` | GetDToO | B_FaceP, CompDToO, InitBowser |
| `BowserOrigXPos` | `$0366` | GetDToO, GetPRCmp | InitBowser |
| `BowserFlameTimerCtrl` | `$0367` | SetFlameTimer | SetFlameTimer |
| `BowserFront_Offset` | `$0368` | BridgeCollapse, InitBowserFlame | InitBowser |
| `BridgeCollapseOffset` | `$0369` | RemoveBridge | InitBowser, RemoveBridge |
| `BowserGfxFlag` | `$036A` | CheckBowserFront, CheckBowserGfxFlag, CheckForESymmetry, MirrorEnemyGfx, ProcessBowserHalf | CopyFToR, ProcessBowserHalf |
| `FirebarSpinSpeed` | `$0388` | ProcFirebar | InitShortFirebar |
| `VineFlagOffset` | `$0398` | CheckFrenzyBuffer, DifLoop, NextVO, Setup_Vine, VDrawLoop, VineObjectHandler | KillVine, NextVO |
| `VineHeight` | `$0399` | RunVSubs, VineEntr, VineObjectHandler, WrCMTile | KillVine, VineObjectHandler |
| `VineObjOffset` | `$039A` | DrawVine, KillVine | NextVO |
| `VineStart_Y_Position` | `$039D` | ChkFTop | Setup_Vine |
| `BalPlatformAlignment` | `$03A0` | AlignP | ClearVRLoop, SetBPA |
| `Platform_X_Scroll` | `$03A1` | ScrollHandler | InitPlatScrl, SetPVar |
| `PlatformCollisionFlag` | `$03A2` | CheckBalPlatform, ChkJH, ChkSmallPlatCollision, ChkToMoveBalPlat, ChkYPCollision, DecHT, DoOtherPlatform, DropPlatform, PlatformFall, RightPlatform, XMovingPlatform | ChkJH, DecHT, InitDropPlatform, InitHammerBro, LargePlatformCollision, SetCollisionFlag, SmallPlatformCollision |
| `SprObject_Rel_XPos` | `$03AD` | BoundingBoxCore, ChkETmrs, GBBAdr, InitPlatformFall, RendFore, RenderPlayerSub | GetObjRelativePosition |
| `Enemy_Rel_XPos` | `$03AE` | AddHA, ChkETmrs, DSFLoop, DrawFlameLoop, DrawLargePlatform, DrawPowerUp, DrawSmallPlatform, DrawVine, EnemyGfxHandler, FlagpoleGfxHandler, SetupExpl, SetupFloateyNumber, SetupGFB, SubtR1 | DrawFlameLoop |
| `Fireball_Rel_XPos` | `$03AF` | DrawExplosion_Fireworks, DrawFireball | SetupExpl |
| `Bubble_Rel_XPos` | `$03B0` | BlockBufferCollision, ContinueSwimStomp, DrawBubble | — |
| `Block_Rel_XPos` | `$03B1` | DChunks, DrawBlock, SceLoop2 | — |
| `Misc_Rel_XPos` | `$03B3` | JCoinGfxHandler, NotRsNum, RenderH | — |
| `SprObject_Rel_YPos` | `$03B8` | BoundingBoxCore, RenderPlayerSub | GetObjRelativePosition |
| `Enemy_Rel_YPos` | `$03B9` | AddVA, DSFLoop, DrawFlameLoop, DrawPowerUp, DrawVine, SetupExpl, SetupGFB, VAHandl | — |
| `Fireball_Rel_YPos` | `$03BA` | DrawExplosion_Fireworks, DrawFireball | SetupExpl |
| `Bubble_Rel_YPos` | `$03BB` | DrawBubble | — |
| `Block_Rel_YPos` | `$03BC` | DChunks, DrawBlock | — |
| `Misc_Rel_YPos` | `$03BE` | RenderH | — |
| `SprObject_SprAttrib` | `$03C4` | ChkBehPipe, CyclePlayerPalette, PipeDwnS, PlayerSubs, RenderPlayerSub, ResetPalStar | CyclePlayerPalette, HandlePipeEntry, InCastle, PlayerSubs, PlyrPipe, ResetPalStar, SetStPos |
| `Enemy_SprAttrib` | `$03C5` | EnemyGfxHandler | BPGet, EraseEnemyObject, MoveFlyingCheepCheep, PutinPipe, RunNormalEnemies |
| `SprObject_OffscrBits` | `$03D0` | CheckPlayerVertical, PlayerOffscreenChk | GetOffScreenBitsSet |
| `Enemy_OffscreenBits` | `$03D1` | BotSP, BulletBillHandler, CMBits, ChkFlagOffscreen, ChkJH, DrawFlameLoop, GetEnemyBoundBoxOfsArg, ProcFirebar, SLChk, SprObjectOffscrChk, VDrawLoop | — |
| `FBall_OffscreenBits` | `$03D2` | RunFB | — |
| `Bubble_OffscreenBits` | `$03D3` | DrawBubble | — |
| `Block_OffscreenBits` | `$03D4` | BlkOffscr, DChunks | — |
| `Misc_OffscreenBits` | `$03D6` | PlayerHammerCollision, RenderH | — |
| `EnemyOffscrBitsMasked` | `$03D8` | ECLoop, EnemiesCollision, HandlePECollisions, NotGoomba, PlayerEnemyCollision, TerMTile | CMBits, CheckpointEnemyID |
| `Block_Orig_YPos` | `$03E4` | UpdateLoop | DBlockSte |
| `Block_BBuf_Low` | `$03E6` | UpdateLoop | DBlockSte |
| `Block_Metatile` | `$03E8` | ChkRep, UpdateLoop | PutMTileB |
| `Block_PageLoc2` | `$03EA` | SetupJumpCoin | InitBlock_XY_Pos |
| `Block_RepFlag` | `$03EC` | ReplaceBlockMetatile, UpdateLoop | BouncingBlockHandler, BrickShatter, ReplaceBlockMetatile, UpdateLoop |
| `SprDataOffset_Ctrl` | `$03EE` | BrickShatter, CheckTopOfBlock, DBlockSte, GetAltOffset, InvOBit, PlayerHeadCollision, VineBlock | InvOBit |
| `Block_ResidualCounter` | `$03F0` | ReplaceBlockMetatile | ReplaceBlockMetatile |
| `Block_Orig_XPos` | `$03F1` | DChunks | SpawnBrickChunks |
| `AttributeBuffer` | `$03F9` | AttribLoop, SetAttrib | AttribLoop, SetAttrib |
| `SprObject_X_MoveForce` | `$0400` | UseAdder | TScrClear, UseAdder |
| `YPlatformTopYPos` | `$0401` | CCSwim, ProcMoveRedPTroopa, SFlmX, YMovingPlatform | CCSwim, FinishFlame, InitRedPTroopa, SFlmX, SetYO |
| `SprObject_YMF_Dummy` | `$0416` | ClimbingSub, ImposeGravity, PositionPlayerOnS_Plat | ClimbingSub, ImposeGravity, InitJS |
| `Enemy_YMF_Dummy` | `$0417` | CCSwim, CCSwimUpwards, FlagpoleRoutine, MoveLiftPlatforms, SFlmX, SetupToMovePPlant | AddFBit, CCSwim, CCSwimUpwards, FlagpoleRoutine, InitPiranhaPlant, MoveLiftPlatforms, ProcMoveRedPTroopa, SetFrT, SpawnFromMouth, YMovingPlatform |
| `Bubble_YMF_Dummy` | `$042C` | MoveBubl | MoveBubl |
| `SprObject_Y_MoveForce` | `$0433` | AlterYP, ChkUpM, ClimbingSub, DrawVine, ImposeGravity | AlterYP, ChkUpM, GetYPhy, InitJS, LandPlyr, PositionPlayerOnVPlat, ProcClimb |
| `Enemy_Y_MoveForce` | `$0434` | AddCCF, BlooberSwim, ChkSwimYPos, ChkToMoveBalPlat, DrawEraseRope, FlyCC, MoveLiftPlatforms, ProcMoveRedPTroopa, ProcSwimmingB, SFlmX, SetupToMovePPlant, SlowSwim, YMovingPlatform | AddCCF, InitBowserFlame, InitCheepCheep, InitPiranhaPlant, InitVStf, MovePodoboo, PlatLiftDown, PlatLiftUp, ProcSwimmingB, SetMF, SlowSwim, StopPlatforms |
| `Block_Y_MoveForce` | `$043C` | — | BumpBlock, SpawnBrickChunks |

