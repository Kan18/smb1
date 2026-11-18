#!/bin/bash
# usage: run.sh SEEDS NAME ENTRY EXIT [SECONDS] [OUTDIR]: one region from these seeds; saves NAME.g, prints the verdict.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
seeds=$1; name=$2; entry=$3; exit=$4; limit=${5:-300}; dir=${6:-$root/scratch/engine-bounds}
mkdir -p "$dir"
# Explicit seed bounds override defaults; do not emit duplicate global directives.
python3 - "$here/region.head" "$seeds" "$entry" "$exit" "$dir/$name.g" > "$dir/$name.cfg" <<'PYCFG'
import sys
from pathlib import Path
head, seed, entry, stop, saved = sys.argv[1:]
seed = Path(seed).read_text()
rows = [line.split('#', 1)[0].split() for line in seed.splitlines()]
addresses = {int(w[1], 16) for w in rows if len(w) > 1 and w[0] == 'global'}
print(f'entry {entry} F9\nexit {stop}')
for line in Path(head).read_text().splitlines():
    w = line.split('#', 1)[0].split()
    if w and w[0] == 'global' and int(w[1], 16) in addresses:
        continue
    print(line)
print(seed)
print(f'saveg {saved}')
PYCFG
start=$(date +%s)
set +e
timeout "$limit" "${SMBABS:-$root/lean/.lake/build/bin/smbabs}" "$root/Super Mario Bros. (World).nes" "$dir/$name.cfg" > "$dir/$name.out" 2> "$dir/$name.err"
rc=$?
echo "$name ${entry}→${exit} rc=$rc $(( $(date +%s) - start ))s: $(grep -E '^check' "$dir/$name.out") | $(grep -E '^promoted cells' "$dir/$name.out" | cut -c1-110) | $(grep -E '^boxes' "$dir/$name.out" | cut -c1-100)"
grep -vE '^promoted|^boxes|^check|hot tuples|most boxes' "$dir/$name.out" | head -8 | cut -c1-190
exit $rc
