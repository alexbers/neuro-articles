#!/bin/bash
# Compile the certificate modules in dependency order on agent B04's cores (2 in parallel where possible).
cd "$(dirname "$0")"
export L=$HOME/claude_math/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
export LEAN_PATH=$PWD
run() { /usr/bin/time -f "$1: wall=%es maxrss=%MkB exit=%x" taskset -c 9-11 nice -n 5 $L -o $1.olean $1.lean > $1.out 2>&1; tail -1 $1.out; }
export -f run
[ -f K19Core.olean ] || run K19Core
run K19Defs
grep -E '^K19(C_|CR|Chk)' modules.txt | xargs -P 3 -I{} bash -c 'run {}'
run K19Main
grep -v '^$' K19Main.out | grep -E 'axioms|error' 
