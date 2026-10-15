#!/bin/bash
# usage: assemble.sh data.lean  -> writes Main.lean
D=$(dirname "$0")
{ cat "$D/KoebeWitness.lean"; cat "$D/KoebePart2.lean"; cat "$1"; cat "$D/KoebePart3.lean"; } > "$D/Main.lean"
echo "assembled $D/Main.lean ($(wc -l < "$D/Main.lean") lines)"
