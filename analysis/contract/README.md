# Player and normal-play regions

The normal-play proof breaks one game update into regions for the interrupt
handler, the player, enemies, the engine tail, the area parser, and the
closing path back to the handler. Each region has entry conditions, a list
of tracked memory values, and exits. The checked Lean configurations
are in `Smb/Play*Data.lean`. [`PlayCycle`](../../lean/Smb/Routine/PlayCycle.lean)
links them. [World 1-1](../../docs/lower-bound-1-1.md) explains the conditions
still needed to enter and use the cycle on every route.

## Start from the checked configurations

Build `smbabs` with `lake build smbabs` inside `lean/`. Run these commands
from the repository root with the cartridge from the
[build instructions](../../README.md#reproduce-the-upper-bound).

```sh
python3 analysis/contract/prot_probe.py scratch/play-regions
lean/.lake/build/bin/smbabs "$ROM" scratch/play-regions/H.cfg
```

`prot_probe.py OUTDIR CELL...` exports the handler, enemy, parser and
closing configurations and can add protected cells. For example, add a
cell when trying to show that a region leaves it unchanged. The player
and engine tail have their own configuration data. The
[bounds checker guide](../engine_bounds/README.md) explains how to read
alarms and inspect a region.

## Player fragments

| Config | Region |
|---|---|
| `player_pre.cfg` | Player-region entry at `$8175` to player control |
| `player_ctrl.cfg` | `PlayerCtrlRoutine` to background collision |
| `collision.cfg` | Background collision to the wall response, return, or phase exit |
| `collision_bounds.cfg` | Background collision through the wall response and attribute update |
| `player_post.cfg` | `PlayerHole` at `$B179` to return or pit death |
| `head_hit.cfg` | `PlayerHeadCollision` from `$BCED` to `$DCE7` |

Run `lean/.lake/build/bin/smbabs "$ROM" analysis/contract/collision.cfg` to inspect the
collision region. To regenerate its Lean data from the normal-play
player configuration, run:

```sh
python3 analysis/contract/gen_head_hit.py analysis/contract/collision.cfg lean/Smb/CollisionData.lean collision
```

The links to and between the fragments are checked by
[`PlayLinks`](../../lean/Smb/Routine/PlayLinks.lean),
[`PlayerEnter`](../../lean/Smb/Routine/PlayerEnter.lean), and
[`PlayerCtrlLink`](../../lean/Smb/Routine/PlayerCtrlLink.lean).
[`PlayerJoin`](../../lean/Smb/Routine/PlayerJoin.lean) carries horizontal
movement facts through a complete player call. For the launch regions,
`launch_cells.c` and `launch_regions.py` produce inputs for `gen_launch.py`.

`play_regions.py` and `play_shared.py` generate candidate normal-play
configurations. The parser and enemy generators partition the larger
regions so that each part can be checked separately. Some generators
take intermediate bounds and tables from these runs. Start with the
exported checked regions when extending an existing proof. The
checked-in data contains the configurations needed to build Lean.
