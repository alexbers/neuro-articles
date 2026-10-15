# Data

- `certificates.json` — the 45 signed difference sets of the paper, keyed as in Gordon's repository
  (`SDS(v,k,lambda,[m1,...,mr])`). Fields:
  - `group_moduli`;
  - `tier` (a = new, b = order-64 cases of Prop. 4.5, c = database correction); the `note` fields of
    tier-b entries predate the PDS search below;
  - `P`, `N` as coordinate tuples (exactly as in `lean/Main.lean`);
  - `P_index`, `N_index` as mixed-radix indices (as in Appendix A);
  - `note`.
- `verify_certificates.py` — independent checker: `python3 verify_certificates.py`, which prints
  `ALL OK`.
- `sds_ls.c` — simulated-annealing search. `sds_ex.c` — exhaustive search, with normalisations
  0 ∈ supp D and s_0 = +1, the support-parity filter, and sign backtracking.
- `ex_small.txt` — exhaustive-search log for the open cases with v ≤ 28.
- `validate_ex.txt` — validation of `sds_ex` on cases with known answers.
- `hyperoval.py` — checks that the hyperoval set in GF(4)^3 is a (64,18,2,6) PDS, and that
  P − {0}, with P its complement, is a (64,46,30) SDS.
- `pds_z3.py` — pseudo-Boolean (z3) search for regular (64,18,2,6) (`nls`) and (64,21,8,6) (`ls`)
  partial difference sets in all 11 abelian groups of order 64; logs `pds_z3_nls.txt`,
  `pds_z3_ls.txt`. `pds_ex.c`, `pds_ex2.c` — independent backtracking cross-checks (the second
  with stronger pruning); logs `pds_ex.txt`, `pds_ex2.txt` (runs that did not finish within the time
  limit concern only groups where the sets exist). Result: both kinds exist exactly in Z_2^6,
  Z_2^2 x Z_4^2 and Z_8^2 (Prop. 4.5); all 16 nonexistence verdicts are confirmed by backtracking.
