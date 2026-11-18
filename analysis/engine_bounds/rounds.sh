#!/bin/bash
# usage: rounds.sh SEEDS.g OUTDIR SECONDS [MAXROUNDS]: run every region against shared bounds, union what they found, and repeat until none grows.
# Each round is a new directory OUTDIR/rN. Exit 0 once a round has every region accepted by the checker, every link held and no growth, 1 otherwise, 2 if a round can't start.
# Set NOCHECK to skip the checker until a round is stable: the next round then runs with it, and only a checked round can count as the fixed point.
set -u
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
seeds=$1; out=$2; limit=$3; rounds=${4:-6}
unchecked=${NOCHECK:-}
bin=${SMBABS:-$root/lean/.lake/build/bin/smbabs}
for n in $(seq 1 "$rounds"); do
  d=$out/r$n; mkdir -p "$out"
  mkdir "$d" || exit 2  # an earlier run's files must not pass for this round's
  python3 "$here/regions.py" "$seeds" "$d" > /dev/null || exit 2
  if [ -n "$unchecked" ]; then for r in H P E T A Z; do echo nocheck >> "$d/$r.cfg"; done; fi
  for r in H P E T A Z; do
    # the same config, the configs its links read, the binary and the ROM give the same result, so an unchanged region isn't run again. Its paths are per round, so they don't count
    key=$( (sed "s#$d/#ROUND/#g" "$d/$r.cfg"; for f in $(awk '$1 == "next" {print $3}' "$d/$r.cfg"); do sed "s#$d/#ROUND/#g" "$f"; done; shasum "$bin"; shasum "$root/Super Mario Bros. (World).nes") | shasum | cut -d' ' -f1)
    c=$out/cache/$key
    if [ -f "$c/$r.rc" ]; then
      for e in out err rc g; do cp "$c/$r.$e" "$d/$r.$e"; done
    else
      ( timeout "$limit" "$bin" "$root/Super Mario Bros. (World).nes" "$d/$r.cfg" > "$d/$r.out" 2> "$d/$r.err"; echo "$? " > "$d/$r.rc"
        if [ -f "$d/$r.g" ]; then mkdir -p "$c"; for e in out err rc g; do cp "$d/$r.$e" "$c/$r.$e"; done; fi ) &
    fi
  done
  wait
  ok=1; grew=0
  for r in H P E T A Z; do
    rc=$(cat "$d/$r.rc"); g=$(grep -c '^grew' "$d/$r.out"); grew=$((grew + g))
    # 3 is the generator's "finished clean, unchecked"
    [ "$rc" = "0 " ] || { [ -n "$unchecked" ] && [ "$rc" = "3 " ]; } || ok=0
    echo "round $n $r rc=$rc grew=$g $(grep -E '^boxes' "$d/$r.out" | cut -c1-70) | $(grep -E '^check' "$d/$r.out") | $(grep -E '^[0-9a-f]{4} \[' "$d/$r.out" | cut -c1-70 | head -6 | tr '\n' ';') | $(grep -E '^next' "$d/$r.out" | sed 's/.*cfg: //' | tr '\n' ';')"
  done
  python3 "$here/union.py" "$d/union.g" "$d/H.g" "$d/P.g" "$d/E.g" "$d/T.g" "$d/A.g" "$d/Z.g" || exit 1
  seeds=$d/union.g
  if [ "$ok" = 1 ] && [ "$grew" = 0 ]; then
    if [ -z "$unchecked" ]; then echo "fixed point at round $n: $d/union.g"; exit 0; fi
    echo "stable and unchecked at round $n: checking from here"; unchecked=
  fi
done
exit 1
