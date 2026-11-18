# Tracing frame rules and transitions

`ftrace` records per-frame state, including controller-poll and timer
observations. `check.py` compares pipe, flag, and area-load timing with the
trace. `chain.py` computes the number of ticks and the margin to the next
21-tick boundary between intermediate screens.

```sh
mkdir -p scratch
cc -O2 emu/nes.c analysis/frame_timing/ftrace.c -o scratch/ftrace
scratch/ftrace "$ROM" "$TAS" --tas-startup > scratch/timing.csv
python3 analysis/frame_timing/check.py scratch/timing.csv
python3 analysis/frame_timing/chain.py scratch/timing.csv
```

See [the timing formulas](../../docs/frame-timing.md) for how to interpret
the trace. [`TimerStep`](../../lean/Smb/Routine/TimerStep.lean) proves
the period of the timer block in enabled ticks.
