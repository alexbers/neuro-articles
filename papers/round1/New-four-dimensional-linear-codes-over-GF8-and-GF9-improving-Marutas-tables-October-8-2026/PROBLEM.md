# PROBLEM (A06): shorter four-dimensional linear codes over GF(8) and GF(9)

## TARGET

For a prime power `q` let `n_q(k,d)` be the smallest length `n` for which a linear `[n,k,d]_q`
code exists. For `k = 4` and `q ∈ {8, 9}` the exact value of `n_q(4,d)` is still unknown for
hundreds of values of `d`; the current state of knowledge is the interval
`n_lo(d) ≤ n_q(4,d) ≤ n_up(d)` recorded in T. Maruta's tables

* `q = 9`: <http://mars39.lomo.jp/opu/bound9_4-1.htm> (… `-2` … `-6`), 727 open values of `d`;
* `q = 8`: <http://mars39.lomo.jp/opu/bound8_4.htm> (… `-2` … `-6`), 415 open values of `d`.

**Target.** Construct explicit linear `[n,4,d]_q` codes (`q = 8` or `9`) with `n < n_up(d)`,
i.e. strictly shorter than every code recorded in the table, and certify them in Lean.
The strongest form: reach `n = n_lo(d)`, which determines `n_q(4,d)` exactly.
Every improvement must be checked against the *current* table (fetched 2026-10-08; the index page
says "Last change: 08/09/2026").

## DEFINITIONS

* A linear `[n,k,d]_q` code is a `k`-dimensional subspace `C ⊆ GF(q)^n` whose nonzero vectors all have
  Hamming weight `≥ d`. It is given by a `k × n` generator matrix `G`; `C = {uG : u ∈ GF(q)^k}`.
  `C` has dimension exactly `k` iff `u ↦ uG` is injective, which is implied by `wt(uG) ≥ d ≥ 1` for all
  `u ≠ 0`.
* Geometric view: the columns of `G` form a multiset `M` of `n` points of `PG(k−1,q)`, and
  `wt(uG) = n − |M ∩ u^⊥|`. Hence an `[n,k,d]_q` code is the same as a multiset of `n` points in which every
  hyperplane contains at most `n − d` points.
* Griesmer bound: `n_q(k,d) ≥ g_q(k,d) = Σ_{i=0}^{k−1} ⌈d/q^i⌉`.
* Table semantics: an entry `d | g | a-b` means `a ≤ n_q(4,d) ≤ b`; a single number means the value is known.

## STATUS AND SOURCES (why it is open)

* Maruta's tables (above) are the reference for `n_q(4,d)`; for `q = 9` and mid-range `d`
  (roughly `190 ≤ d ≤ 560`) the gap `n_up − n_lo` is 2–5.
* K. Kumegawa, T. Okazaki, T. Maruta, *On the minimum length of linear codes over the field of 9
  elements*, Electron. J. Combin. 24(1) (2017) #P1.50
  (<https://www.combinatorics.org/ojs/index.php/eljc/article/view/v24i1p50>): "We have also constructed new
  codes … e.g. [274,4,240]_9, [312,4,273]_9, [378,4,332]_9 … with the aid of a computer, but the upper bounds
  are still weak to be improved."
* Later work (e.g. Serdica J. Computing 2023, AMC 2023 "Nonexistence of some four dimensional linear codes
  attaining the Griesmer bound") improved *lower* bounds; the table index was last changed in 2026.
* codetables.de (Grassl) covers only `n ≤ 130` for `q = 8, 9`, so it does not contain the mid-range entries.
* Not claimed by OpenAI's 2026 release (`CONTENTS.md` contains no coding-theory item).

## RESEARCH DIRECTION

Prescribed-automorphism method (Braun–Kohnert–Wassermann / "orbits of projectivities", Maruta–Shinohara–
Takenaka): choose a cyclic group `⟨T⟩ ≤ PGL(4,q)`, compute its orbits on points and on planes of
`PG(3,q)`, and solve the integer program

  maximise `Σ_i |O_i| x_i`  subject to  `Σ_i |O_i ∩ H| x_i ≤ r`  for one plane `H` per plane-orbit,
  `x_i ∈ {0,1}` (or small multiplicities),

which yields an `(n, r)`-multiset, i.e. an `[n, 4, n−r]_q` code. Scan many random `T` of moderate order
(4–80) and all `r` for which the table has a gap. Verify every hit by full enumeration of all `q^4`
codewords, independently of the search code.

## PITFALLS

* Comparing with an outdated table / paper instead of the current online table; the table also has
  lower-bound updates (nonexistence results) that must be respected.
* An `(n, r)`-multiset gives `d = n − r` only if the **maximum** hyperplane multiplicity is `r`; it is not an
  improvement unless `n < n_up(n−r)`.
* Puncturing an `[n,4,d]` code gives `[n−t,4,d−t]`; derived improvements must be reported as such and
  not as independent results.
* Field representation: the search uses `GF(9) = F_3[x]/(x²+x+2)`, the Lean file `F_3[i]/(i²+1)`;
  the generator matrix must be transported by a field isomorphism (`x ↦ 1+i`), otherwise the certified
  matrix is a different code.
* Lean statement drift: the Lean predicate must say "length `n`, every nonzero message has weight `≥ d`"
  over the actual field (not over integers mod 9, not over a non-field ring), quantified over **all**
  nonzero messages, not only the normalised ones used in the computation.
* No `native_decide`, no `sorry`/`axiom`; the kernel must evaluate the finite check.

## CERTIFICATE

An explicit `4 × n` generator matrix (list of `n` columns) over GF(q) together with a Lean proof of
`IsCode L n d := L.length = n ∧ ∀ u ≠ 0, d ≤ wt (codeword L u)`, where `codeword L u = L.map (dot u)`
and `wt` counts nonzero entries; plus a proof that the coefficient structure used is a field with `q`
elements. Independent check: a Python enumeration of all `q^4 − 1` nonzero codewords giving the exact
weight distribution.
