#!/bin/bash
# Validation of the fast forest checker (fnc4.c) against the reference checker (fnc.c):
# on every 2-connected graph of the given orders, the full per-pair output (-v) must agree exactly,
# line for line.  fnc.c is the tool used for the n <= 9 runs; fnc4.c is the tool used for n = 10.
#
# usage:  ./validate_fnc4.sh "4 5 6 7 8" [EXTRA_GENG_ARGS]
# needs:  geng (nauty 2.8.8) on the PATH or in this directory, and a C compiler.
# runtime: about 2 minutes for "4 5 6 7 8" (the n = 8 reference run dominates).
set -e
cd "$(dirname "$0")"
GENG=${GENG:-./geng}
command -v "$GENG" >/dev/null 2>&1 || test -x "$GENG" || { echo "geng not found (set GENG=...)"; exit 2; }
test -x ./fnc   || cc -O2 -o fnc   fnc.c  -lm
test -x ./fnc4n || cc -O3 -o fnc4n fnc4.c -lm
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
status=0
for n in $1; do
  "$GENG" -q -C "$n" $2 > "$T/v.g6"
  ./fnc   -v < "$T/v.g6" > "$T/ref.txt"
  ./fnc4n -v < "$T/v.g6" > "$T/fast.txt"
  if cmp -s "$T/ref.txt" "$T/fast.txt"; then
    echo "AGREE n=$n graphs=$(wc -l < "$T/v.g6") lines=$(wc -l < "$T/ref.txt")"
  else
    echo "DISAGREE n=$n"
    diff "$T/ref.txt" "$T/fast.txt" | head -5
    status=1
  fi
done
echo "VALIDATION $([ $status -eq 0 ] && echo PASS || echo FAIL)"
exit $status
