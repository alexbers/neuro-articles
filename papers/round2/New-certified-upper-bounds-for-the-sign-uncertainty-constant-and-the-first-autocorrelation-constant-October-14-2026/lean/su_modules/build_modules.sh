#!/bin/bash
# usage: build_modules.sh <mathlib project dir> <module dir> [lean bin dir]
# Compiles SUCore, SULeaves*, SUMain in order (one process each, bounded memory); prints time/RSS per module.
P=$1; M=$(readlink -f $2); [ -n "$3" ] && export PATH=$3:$PATH
mkdir -p $M/olean
cd $P
for f in SUCore $(cd $M && ls SULeaves*.lean | sed 's/.lean//' | sort -V) SUMain; do
  echo "=== $f"
  if [ "$f" = SUMain ]; then out=""; else out="-o $M/olean/$f.olean"; fi
  lake env bash -c "cd $M && LEAN_PATH=\$LEAN_PATH:$M/olean /usr/bin/time -f '$f: wall=%es maxrss=%MkB exit=%x' lean -R $M $out $M/$f.lean" 2>&1 | grep -v "^Hint\|^Note\|linter\|^  \[apply\]\|^$" | grep -v "warning\|getElem?_replicate\|Bool.true_and\|this tactic is never executed"
  [ ${PIPESTATUS[0]} -ne 0 ] && echo "FAILED $f" && exit 1
done
echo ALLDONE
