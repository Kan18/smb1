# Flag-grab walk-skip exploration

`ws.c` inspects or searches positions near flagpoles and other terrain.
It starts from the state after the specified aligned movie frame.

```sh
mkdir -p scratch
cc -O2 emu/nes.c analysis/walk_skip/ws.c -o scratch/ws
scratch/ws "$ROM" "$TAS" trace 1283 1286
```

`trace`, `map` and `foes` inspect a movie. `bfs` and `fastjump`
explore selected continuations. The `jumpgrid` and `inground` commands
edit the starting state, which is useful for isolating a mechanism.
See the command usage in [`ws.c`](ws.c).

The searches restrict the frontier and merge states by selected player
bytes. A failure leaves open whether the walk skip can be reached.
[World 1-1](../../docs/lower-bound-1-1.md#flag-height-and-the-frame-rule)
states the outstanding proof obligation.
