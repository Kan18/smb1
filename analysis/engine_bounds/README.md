# Checking bounds across the game engine

A region starts at a specified ROM address with a set of possible
register and RAM values. `smbabs` searches for an invariant by growing
those sets and reports unfinished runs when it reaches a search limit.
It can also check
whether a region leaves chosen RAM cells unchanged and whether its
exit states fit the next region's entry conditions.

[`AbsSem`](../../lean/Smb/Routine/AbsSem.lean) connects the instruction
semantics to `CPU.step`. [`AbsCheck`](../../lean/Smb/Routine/AbsCheck.lean)
proves that an accepted table is an invariant under its entry and
execution conditions. The table generator in
[`Abs/Fix.lean`](../../lean/Smb/Abs/Fix.lean) proposes the tables, which
the checker verifies.

## Explore a region

Supply `ROM` as in the [build instructions](../../README.md#reproduce-the-upper-bound).

```sh
(cd lean && lake build smbabs)
lean/.lake/build/bin/smbabs "$ROM" analysis/contract/collision.cfg
```

For the full normal-play cycle, see the
[player region guide](../contract/README.md). The checker supports Plain
regions (no I/O or interrupts), NES regions, and whole-frame regions.
The corresponding Lean checks are `check`, `checkN`, and `checkF`.

- `check true` covers the region under its entry and run conditions.
  The surrounding proof must establish those conditions and connect
  each relevant exit to a successor.
- `prot CELL` requires the region to preserve a cell. `watch`, `dump`,
  and `dumpc` help find writers and inspect the boxes around an alarm.
- `nogrow` holds the proposed bounds fixed. `next PC FILE` compares the
  boxes at that exit with the next configuration's entries.
- An `assume` on a buffer offset supplies a run hypothesis. The Lean
  soundness statement requires `Clean` at every step that uses it.
  The 1-1 argument must justify the chosen limits for the cases it covers.

Small sets of relevant values scale better than tracking all of RAM.
The parser needs exact tuples of its position in the area data and object
counters. Losing that relation can make an unrelated object look as
though it overruns a rendering loop. Track the counter where needed
and split on it around the loop. A load or branch can narrow a register
while a later load of its source cell still uses the original wider set.
Track and split the source cell when that distinction affects dispatch.

## Find bounds for a new region

`mine.c` collects candidate sets by tracing a movie. `run.sh` builds
a config for a region from a seed file and runs the checker (it uses
the `timeout` command). `union.py` combines the globals from multiple
regions. A missing cell in a sparse list means any value is allowed, so
the union leaves it unrestricted. The resulting sets are candidates
until checked.

The parser's saved state chain lets its entry configs keep object fields
tied to the current record. `parser_chain.txt` and `parser_blocks.txt`
supply the 1-1 tuples and permitted block values. `close_chain.sh` grows
the chain using the parser region's exits. Its current area limits are
specific to 1-1, so rederive those inputs before applying it to another
level. See [later levels](../../docs/later-levels.md) for examples.

The table checks can be expensive, especially in parser and enemy
regions. Build one affected Lean module at a time when memory is limited.

## Prove a single ROM routine

`lean/scripts/routine.py gen` traces a ROM address and prints excerpt references
and stop conditions for a symbolic proof. Run it from the repository root
with the cartridge at the default path:

```sh
python3 lean/scripts/routine.py gen B8BD --until B8EE --name example
```

Each reference specifies a CPU address and a byte count. Run
`lean/scripts/gen_data.py` again after adding a reference to a Lean module.
Use `--call` for callees with existing summaries and `--table ADDR:LEN` for
ROM data used by the proof. Indirect branches
may need separately traced targets. See
[`Smb/Summary.lean`](../../lean/Smb/Summary.lean) for `sym_summary` and
[`SummaryCheck`](../../lean/Smb/Routine/SummaryCheck.lean) for a compact
example connecting a summary to the executable semantics.
