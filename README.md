I wanted to see if Claude/GPT could produce a formal proof of whether the SMB1 TAS is optimal. AI agents worked on a bunch of Lean theorems about the game, but it didn't really produce anything super interesting yet. Note that the rest of the README and the repo is AI-generated and I haven't reviewed it thoroughly myself.

# Super Mario Bros. TAS optimality

This project studies whether any sequence of controller inputs can beat
[HappyLee's warps TAS of the original NES game](https://tasvideos.org/1715M).
Lean runs the original cartridge code in an executable NES model. The C
implementation supports replay, inspection, and search.

The recorded inputs reach final-castle victory in **17,866 frames** in the model. This gives an upper bound. The minimum time for the full game
and for World 1-1 remains open. From the exact state three frames before this
run's victory, Lean separately proves that three frames are necessary and that
neutral input suffices. See [the replay theorem](lean/Smb/UpperBound.lean) and
[the fixed-state result](lean/Smb/LocalBound.lean).

The run starts from the model's power-on state followed by one soft reset. One
controller-1 byte is supplied per frame, including simultaneous Left and Right.
Controller 2 is idle and there are no further resets. The first blank movie
frame is dropped to align startup. Victory means the model's RAM shows victory
mode in World 8-4 at a frame boundary. See [The NES model and finish condition](docs/model.md)
for hardware coverage and how this timing relates to other possible endpoints.

## Reproduce the upper bound

Use Python 3.10 or later and Lean through Elan. The version is pinned in
[`lean/lean-toolchain`](lean/lean-toolchain). The C tools also need a C compiler
and Make. Supply these two inputs locally:

- Your `Super Mario Bros. (World).nes`, with PRG+CHR MD5 `8e3630186e35d477231bf8fd50e54cdd`.
- `happylee-supermariobros,warped.fm2` from [publication #1715](https://tasvideos.org/1715M).

From the repository root, with the movie saved under `downloads/tas1715/`, run the following.

```sh
ROM='Super Mario Bros. (World).nes'
TAS='downloads/tas1715/happylee-supermariobros,warped.fm2'
python3 lean/scripts/gen_data.py "$ROM" "$TAS" lean/Smb/Data
(cd lean && lake build Smb.UpperBound)
```

The generator validates the cartridge and movie inputs. It creates
`Rom.lean`, `Tas.lean`, and `ProofRom.lean` in the ignored `lean/Smb/Data/`
directory. Proofs specify cartridge excerpts by CPU address and byte count.
Regenerate these files after adding or changing an excerpt reference.

The `native_decide` proof evaluates the compiled Lean model and relies on
Lean's compiler as well as its kernel.

For the three-frame result, run `lake build Smb.LocalBound` inside `lean/`.
The proof covers all 256 controller-1 bytes on each tested frame from the
specified state. For the wider set of local proofs, run `lake build`. Some
modules recompute large bounds tables. Build an individual module when working
on one section of the game. The [axiom audit](lean/scripts/axioms.lean) covers
selected theorems and can be run with `lake env lean scripts/axioms.lean` after
building their imports.

## Replay and investigate

```sh
make -C emu
emu/replay "$ROM" "$TAS" --tas-startup
emu/movieinfo "$ROM" "$TAS"
```

The C report uses zero-based frame indices, so the first victory is at index
17,865. `movieinfo` reports the movie's level transitions, deaths, and victory.
For the same replay in Lean, build `smbcheck` and use its `dump-tas` command:

```sh
(cd lean && lake build smbcheck)
mkdir -p scratch
lean/.lake/build/bin/smbcheck dump-tas scratch/tas.ram
```

- [World 1-1 proof plan](docs/lower-bound-1-1.md) describes the route argument,
  established bounds, and open cases.
- [The bounds checker](analysis/engine_bounds/README.md) and
  [player region tools](analysis/contract/README.md) show how to extend proofs
  to more code paths.
- [Frame timing](docs/frame-timing.md), [buffer semantics](docs/buffer-semantics.md),
  and [later levels](docs/later-levels.md) record the ROM behavior that affects
  the timing argument.
- [The input workbench](docs/tas-workbench.md) covers short continuations,
  screenshots, and searches for better routes.

## License

The original project code and documentation are available under the
[MIT License](LICENSE). The cartridge ROM, TAS movie, and generated files
containing their data are supplied or produced locally and are outside the
scope of this license.
