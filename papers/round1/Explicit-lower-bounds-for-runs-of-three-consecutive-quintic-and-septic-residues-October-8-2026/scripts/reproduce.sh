#!/bin/bash
# Reproduce the computations of A01 (run from this scripts/ directory). Uses ~1 GB RAM for L=1e8.
set -e
gcc -O2 -o ws2 ws2.c; gcc -O2 -o segchk segchk.c; gcc -O2 -o vchk vchk.c; gcc -O2 -o lam lam.c; gcc -O2 -o om om.c
# sanity: the DFS reproduces the known values (UNSAT just above, SAT at the value)
ulimit -s unlimited   # the DFS recurses once per prime
./lam 2 2 9; ./lam 2 2 10; ./lam 3 2 77; ./lam 3 2 78; ./lam 4 2 1224; ./lam 4 2 1225; ./lam 5 2 7888; ./lam 5 2 7889
# chi = Omega mod k (all primes -> 1): first zero triple
./om 5 3 1000000; ./om 7 3 10000000; ./om 11 2 10000000; ./om 13 2 100000000   # last: none below 1e8
# independent verification of the assignments (spf-based and segmented checkers)
./vchk 5 3 300000000 1 ../data/assignment_k5.txt
./segchk 5 3 400000000 1 ../data/assignment_k5.txt     # first zero triple at 313714024
./segchk 7 3 400000000 1 ../data/assignment_k7.txt     # first zero triple at 180317500
# local search from scratch (seed 7): finds an assignment for k=5, L=1e7 within seconds
./ws2 5 3 10000000 100000 7 0.1 50 1
