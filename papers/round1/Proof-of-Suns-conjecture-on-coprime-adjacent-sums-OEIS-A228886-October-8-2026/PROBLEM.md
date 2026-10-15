# PROBLEM — Sun's coprime-sum circular permutations (OEIS A228886)

## TARGET

Prove, for **every** integer `n ≥ 1`:

> There is a permutation `i_0, i_1, …, i_n` of `0, 1, …, n` with `i_0 = 0` and `i_n = n` such that
> all `n + 1` cyclic adjacent sums
> `i_0+i_1, i_1+i_2, …, i_{n-1}+i_n, i_n+i_0`
> are coprime to both `n − 1` and `n + 1`  **if and only if**  `n ∉ {2, 4}`.

Equivalently: `A228886(n) > 0` for all `n ≥ 1` except `n = 2, 4` (Sun's conjecture).

Secondary target (same OEIS entry, comments; Sun arXiv:1309.1679, Remark 3.9(i)): the same
question with `n ± 1` replaced by `2n ± 1`. Sun guessed it holds for all `n` (OEIS wording:
"for any positive integer n"; paper wording: Conjecture 3.9 with `n ± 1 → 2n ± 1`, i.e.
for `n ≠ 2, 4`). Decide exactly for which `n ≥ 1` it holds.

## DEFINITIONS

* Permutation of `0..n`: a list of length `n+1` that is a rearrangement of `[0, 1, …, n]`
  (Lean: `l.Perm (List.range (n + 1))`).
* Cyclic adjacent sums of `[a_0, …, a_k]`: `a_j + a_{(j+1) mod (k+1)}` for `0 ≤ j ≤ k`; the last
  one is `a_k + a_0` (here `i_n + i_0 = n`).
* "coprime to `A`": `gcd(s, A) = 1` (with `gcd(s, 0) = s`, relevant for `n = 1`, `A = n − 1 = 0`).

## STATUS AND SOURCES (checked 2026-10-08)

* OEIS **A228886** (Z.-W. Sun, Sep 07 2013; terms up to a(26) added by M. Alekseyev, Jul 07 2026):
  "Conjecture: a(n) > 0 except for n = 2, 4." Comment: "On Sep 10 2013, Zhi-Wei Sun proved the
  conjecture for any positive odd integer n" (explicit permutations). No proof of the even case is
  recorded. https://oeis.org/A228886
* Z.-W. Sun, *Some new problems in additive combinatorics*, arXiv:1309.1679 (v7):
  Conjecture 3.9 (2013-09-07) = the target; Remark 3.9(ii) proves the odd case; Remark 3.9(i):
  "We also guess that n ± 1 in Conjecture 3.9 can be replaced by 2n ± 1."
  https://arxiv.org/abs/1309.1679
* Z.-W. Sun, on-line talk "Introduction to Combinatorial Number Theory (VI) – Permutations,
  Determinants and Permanents" (June 26, 2020), slide "Two conjectures related to coprime
  properties": states the conjecture with "Remark. I have proved this for any positive odd integer
  n." (even case still open in 2020). http://maths.nju.edu.cn/~zwsun/CNT-talk6.pdf
* Related but different: A228860 (sums coprime to `n`, permutations of `1..n`) — proved by
  H.-Q. Cao and H. Pan (2013) per the OEIS entry. Recent work on Sun's permutation conjectures
  (Y.-F. She, arXiv:2606.18311, arXiv:2609.19114; Hou–Sun primitive-sum conjecture) does not treat
  A228886.
* Not in google-deepmind/formal-conjectures (OEIS folder), not among the OEIS conjectures marked as
  proved by AI agents in 2026, not in OpenAI's 722-paper release (CONTENTS.md, grep).
  Web searches (several phrasings) found no proof of the even case.

So: odd `n` — solved by Sun (2013); **even `n` — open**; the `2n ± 1` companion — open.

## RESEARCH DIRECTION

Sun's odd-`n` permutations are zig-zags `x, n − x, x + c, n − x − c, …` whose adjacent sums take only
two values (`n` and `n ± 2`). For even `n` the same zig-zag cannot end at `n` (parity), and
`n ± 2` is not always coprime to `n ± 1`. Classify the sums `s = n + c` that are coprime to `n ± 1`
for *every* even `n` (or for every even `n` in a residue class mod 3), and build a zig-zag with a
short "phase-switching gadget" in the middle; use the reflection `v ↦ n − v` to move between the
residue classes `n ≡ 1` and `n ≢ 1 (mod 3)`. Treat the companion problem the same way.

## PITFALLS

* Proving only the odd case (already Sun's) or only `n` up to some bound (the OEIS already has data
  up to `n = 26`) does **not** count. A proof must cover all `n`.
* The exceptions must be handled: the statement is an *iff*; `n = 2, 4` must be shown impossible.
* Statement drift: the permutation is of `0..n` (not `1..n`), endpoints are fixed (`i_0 = 0`,
  `i_n = n`), the wrap-around sum `i_n + i_0` is included, and coprimality is required to *both*
  `n − 1` and `n + 1` (not to `n`, cf. A228860). `n = 1` uses `gcd(s, 0) = s`.
* Lean pitfalls: truncated `Nat` subtraction (`n − 1`, `n − 3`, `2n − 1`), off-by-one in index
  ranges, using a function `p : ℕ → ℕ` without bounding/injectivity on `{0..n}`; vacuous
  definitions (sanity-check with concrete positive and negative examples).
* The companion statement as worded in the OEIS ("for any positive integer n") must be checked at
  small `n` (it fails at `n = 2`).

## CERTIFICATE

A self-contained Lean 4 file (core only, no Mathlib) with
```lean
theorem sun_conjecture (n : Nat) (hn : 1 ≤ n) :
    (∃ l, SunCycle n (n - 1) (n + 1) l) ↔ (n ≠ 2 ∧ n ≠ 4)
theorem sun_companion (n : Nat) (hn : 1 ≤ n) :
    (∃ l, SunCycle n (2 * n - 1) (2 * n + 1) l) ↔ n ≠ 2
```
where `SunCycle n A B l` says: `l` is a permutation of `List.range (n+1)`, `l.head? = some 0`,
`l.getLast? = some n`, and every cyclic adjacent sum is coprime to `A` and to `B`;
no `sorry`/`axiom`/`native_decide`; `#print axioms` showing only standard axioms.
