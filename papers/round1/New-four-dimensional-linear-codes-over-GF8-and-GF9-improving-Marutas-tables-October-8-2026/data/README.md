# Data for "New four-dimensional linear codes over GF(8) and GF(9) improving Maruta's tables"

* `codes/q<q>_n<n>_d<d>.txt` — the 32 base codes (24 over GF(9), 8 over GF(8)).
  Line 1: `q=<q> k=4 n=<n> d=<d>`. Every further line `m x0 x1 x2 x3` is a column `(x0,x1,x2,x3)^T`
  of the generator matrix, repeated `m` times. Field elements are integers:
  * GF(9) = F_3[x]/(x^2+x+2): the integer `c0 + 3*c1` denotes `c0 + c1*x`;
  * GF(8) = F_2[x]/(x^3+x+1): the integer `c0 + 2*c1 + 4*c2` denotes `c0 + c1*x + c2*x^2`.
  (The Lean file uses GF(9) = F_3[i]/(i^2+1); the matrices there are the images under the field
  isomorphism x -> 1+i, i.e. `c0 + c1*x -> (c0+c1) + c1*i`. GF(8) is represented identically.)
* `improvements.csv` — all 191 improved table entries: `q, d, Griesmer bound g_q(4,d), table lower
  bound, table upper bound (Maruta's table, 2026-10-08), new upper bound, base code, number t of
  punctured coordinates (the first t columns are deleted), whether the new value meets the lower bound`.
* `verify.py` — independent checker: `python3 verify.py codes/q8_n431_d376.txt` enumerates all
  q^4 - 1 nonzero codewords and prints the minimum distance and the weight distribution (needs numpy).
* `SHA256SUMS` — SHA-256 hashes of all files in this directory and of `../lean/Main.lean`,
  `../lean/lean_output.txt`.
