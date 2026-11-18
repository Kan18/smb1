# Replaying and exploring inputs

An FM2 movie gives the buttons for each frame in `RLDUTSBA` order.
For example, `|0|R.....BA|||` holds Right, B, and A on controller 1
for one frame. The shared parser is [`emu/movie.h`](../emu/movie.h).

Check a complete movie with `emu/movieinfo ROM MOVIE` and replay it with
`emu/replay ROM MOVIE --tas-startup`. Aligned tools start from power-on
and a reset, then drop the blank first input row. The raw convention
plays every row from power-on and applies any recorded commands.
Use the aligned convention when comparing with the target theorem.

## Branch from a movie

Run from the repository root after setting `ROM` and `TAS` as in
[the build instructions](../README.md#reproduce-the-upper-bound).

```sh
mkdir -p scratch
cc -O2 emu/nes.c analysis/buffer/drive_inputs.c -o scratch/drive_inputs
PNG=scratch/shot_ PNGAT=11 scratch/drive_inputs "$ROM" "$TAS" 1000 '12:RB,32:RBA' scratch/probe.bin
```

That continues from the state after aligned frame 1,000 with twelve
frames of Right+B and thirty-two of Right+B+A. The optional picture
index is relative to the continuation and starts at zero. Use
`@scratch/probe.bin` in place of `MOVIE FRAME` to continue again from
the saved state. To draw a range of frames directly from a movie, build
[`movie_shots.c`](../analysis/buffer/movie_shots.c).

For level transitions, pipe destinations and enemy positions, use the
[`lab` event and trace commands](../analysis/tas_timesave/README.md).
For a search that keeps promising continuations and exports a replayable
movie, use `seg` in that same directory.

A saved state is useful for exploring. To establish that a discovery is
reachable, put the entire prefix and continuation into an FM2 and replay
from power-on. Record any RAM edits separately. If a proposed result
depends on a frame boundary, inspect the game's update and interrupt
order as well as the frame-end snapshots.

## Small exhaustive experiments

`make -C emu bfs` builds the bounded search in [`bfs.c`](../emu/bfs.c).
It tries all 256 controller-1 bytes per frame with controller 2 idle.
For a small search after exactly 17,863 aligned inputs:

```sh
mkdir -p scratch
: > scratch/kept-ram.txt
emu/bfs "$ROM" 1 scratch/kept-ram.txt "$TAS" 17863
```

Use an empty file to retain all RAM. With a nonempty file, the search
tries erasing the listed bytes and can rewrite that file as it discovers
reads before writes. Unsupported execution or a frontier above the tool's
capacity leaves the search unresolved. The separate
[fixed-entry Lean proof](../lean/Smb/LocalBound.lean) establishes the
three-frame minimum from this entry.
