# Probing solid-tile boundaries

`bgc.h` is a hand-written decision table for `PlayerBGCollision` at
`$DC64`. The verifier prints its predicted collision outcomes alongside
traces from the NES model. The retained 1-2 input sequence exercises the
lower-screen collision gate.

```sh
mkdir -p scratch
cc -O2 emu/nes.c analysis/solid_boundary/verify.c -o scratch/solid-verify
scratch/solid-verify "$ROM" "$TAS" analysis/solid_boundary/inputs/pit_1-2.inputs
```

[`HeadWindow`](../../lean/Smb/Routine/HeadWindow.lean) and
[`WallOrder`](../../lean/Smb/Routine/WallOrder.lean) prove specific
arithmetic and routine properties. Closing a solid-boundary argument
still requires covering the relevant entry states and collision order.
