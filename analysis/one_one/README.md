# Inspecting World 1-1

`milestones.c` prints changes of phase, position, and timer state on an
aligned movie. Use it with the milestones in the
[1-1 proof plan](../../docs/lower-bound-1-1.md).

```sh
mkdir -p scratch
cc -O2 emu/nes.c analysis/one_one/milestones.c -o scratch/milestones
scratch/milestones "$ROM" "$TAS" 2160
```

`buffer_range.c` and `buffer_streak.c` trace the buffer offsets and writes.
`edit_0340.c` and `edit_03ee.c` intentionally change the model's RAM to
isolate effects of an overflow. `bonus_overflow.c` explores short routes
from the bonus-room entry. An edited-state result shows what an overwrite
can do once present. To establish reachability, reproduce it with
controller inputs from power-on.
