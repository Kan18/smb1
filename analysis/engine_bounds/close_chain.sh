#!/bin/bash
# usage: close_chain.sh BOUNDS.g WORKDIR: grow parser_chain.txt until the parser region's exits are all on it, and record in parser_blocks.txt what it writes to the block buffers.
# Uses SMBABS like rounds.sh. Run it twice in a row to confirm: the second run has to report one round and no new states.
set -eu
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
bin=${SMBABS:-$root/lean/.lake/build/bin/smbabs}
mkdir -p "$2"
BLOCKS_EMPTY=1 python3 "$here/regions.py" "$1" "$2" > /dev/null
cells=$(head -1 "$here/parser_chain.txt" | cut -d' ' -f2-)
{ grep -v -E '^(next|saveg|gwiden) ' "$2/A.cfg"; echo 'gwiden 100000'; echo "saveg $2/chain.g"; echo "chain 8178 $2/chain.txt $cells"; echo 'chaintail 725 726 71f 6a0 720 721'; echo 'chainend 90 62'; echo 'chainend 7b 8a'; } > "$2/close.cfg"
"$bin" "$root/Super Mario Bros. (World).nes" "$2/close.cfg"
cp "$2/chain.txt" "$here/parser_chain.txt"
python3 - "$2/chain.g" "$here/parser_blocks.txt" <<'PY'
import sys
vals = set()
for line in open(sys.argv[1]):
    w = line.split()
    if w[0] == 'global' and 0x500 <= int(w[1], 16) <= 0x69F:
        if w[2] == 'top':
            sys.exit(f'block buffer cell {w[1]} is unbounded')
        vals.update(int(v, 16) for v in w[2:])
open(sys.argv[2], 'w').write(' '.join(f'{v:02x}' for v in sorted(vals)) + '\n')
print(len(vals), 'block values:', ' '.join(f'{v:02x}' for v in sorted(vals)))
PY
