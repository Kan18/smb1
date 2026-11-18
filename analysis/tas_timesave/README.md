# Finding and inspecting faster segments

`lab` reports mode and area transitions or traces Mario, the camera and
enemies. `seg` searches from a target movie state using the C NES model.
It keeps a limited number of promising states per frame and can export
a full movie after verifying the candidate with ordinary replay.

From the repository root, with `ROM` and `TAS` set as in the
[build instructions](../../README.md#reproduce-the-upper-bound):

```sh
mkdir -p scratch
cc -O2 emu/nes.c analysis/tas_timesave/lab.c -o scratch/lab
cc -O3 -pthread analysis/tas_timesave/seg.c -lm -o scratch/seg
scratch/lab "$ROM" "$TAS" events
scratch/lab "$ROM" "$TAS" trace 17860 17865
OUT=scratch/axe.fm2 scratch/seg "$ROM" "$TAS" 17860 10 20 5 1 'x>=0' axe
emu/replay "$ROM" scratch/axe.fm2 --tas-startup
```

The example starts after aligned frame 17,860 and searches up to ten
more frames for final victory. A result matching the target reaches
the same finish at frame index 17,865.

Search arguments are `f0 frames width per_cell threads waypoint... goal`.
Waypoints constrain Mario's world X (`x>=X`, `x<=X`) or the camera's X
(`cam>=C`). Goals include `pipe[:PTR]`, `side[:PTR]`, `axe` (final-castle
victory), and `exit` (control in the next level). For a specific pipe
destination, the replay checks the area pointer after the descent.
See [the source header](seg.c) for options such as `LAG`, `ENTRYV`, and
`GOALY` when camera position or braking matters.

The search uses a limited input alphabet, a position and timing estimate,
selected memory bytes for deduplication, and capped frontiers. A successful
power-on replay establishes a candidate in the model. A search miss leaves
open whether there is a faster route.
