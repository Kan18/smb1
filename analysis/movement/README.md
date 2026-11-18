# Searching Mario's movement model

`model.h` implements the movement rules of the proved player routine
summaries. The tools search restricted models to identify useful timing
bounds or input sequences.

- `launch_dp` keeps the best position for each movement state on open
  ground. With terrain enabled, position is part of the state.
- `range_dp` includes a fixed tile map and splits ranges of the position
  and speed fractions when their carries change. The bonus-room search
  from the TAS entry reaches the exit in 111 frames under this model.
  The result still needs a proof connecting the abstraction to every
  relevant ROM path.
- `line_search` searches a chosen set of buttons, records parents, and
  replays a found sequence on the C NES model.

From the repository root, with `ROM` and `TAS` set as in
[the build instructions](../../README.md#reproduce-the-upper-bound):

```sh
mkdir -p scratch
cc -O2 emu/nes.c analysis/movement/launch_dp.c -o scratch/launch_dp
scratch/launch_dp "$ROM" "$TAS" 194 60
```

The open-ground launch has a separate checked argument in
[`LaunchRun.lean`](../../lean/Smb/Goal/LaunchRun.lean), which states the
conditions needed to turn a movement-model result into a frame bound.
