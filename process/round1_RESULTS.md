# Research attempts, October 8, 2026 — results of 15 agents

Process: each agent picked a genuinely open problem in its assigned area, wrote an OpenAI-style problem
prompt (`PROBLEM.md`), attacked it, certified the result in Lean 4.34.1 (core only, no Mathlib) and
reported honestly (`README.md`). Agents with a result then wrote a preprint (author: Claude, Anthropic)
in `papers/`. Shared prompt: `PROMPT_TEMPLATE.md`; paper instructions: `PAPER_TEMPLATE.md`.
The coordinator independently re-checked results (Lean re-runs and/or own scripts in `_smoke/`).
An independent review of the papers (another session) is in `papers/SUMMARY-2026-10-08.md` and
`papers/*/REVIEW-2026-10-08.md`; its corrections are reflected below.

| Agent | Problem (open since) | Result | Lean | Coordinator check | Paper |
|---|---|---|---|---|---|
| A03 | Z.-W. Sun's conjecture, OEIS A228886 (2013) | **SOLVED** (even case + companion; companion false only at n=2) | ✔ std axioms | Lean re-run 474 s; own script n ≤ 3000 | Proof-of-Suns-conjecture… |
| A12 | Zhang–Zheng GAC conjecture, case n=13 (1995 / n=13 open since ~2018) | **SOLVED** (disproved: balanced f, deg 11, Δ=112<128) | ✔ | Lean re-run 155 s; own WHT/ANF script | A-balanced-13-variable… |
| A06 | Maruta's n_q(4,d) tables, q=8,9 (2011/2017) | **NEW RECORD**: 191 entries improved, 29 exact values | ✔ | own GF(8)/GF(9) min-distance check of all 230 codes | New-four-dimensional-linear-codes… |
| A15 | Open proper CW(n,k) entries (Gordon's repository) | **6 new proper CWs** (146,266,366,504,614,762); twin family conjectural | ✔ | Lean re-run 408 s; own PAF/properness script | New-proper-circulant-weighing… |
| A07 | Open signed-difference-set cases (Gordon 2022; He–Wu 2026) | no (9,8,1)-SDS in Z3² (Lean); 45 cases settled, all v≤28 decided | ✔ (16 nonexistence results computer-only) | own script: 46 certificates + 3⁹ enumeration | Settling-small-open-cases… |
| A10 | Line-free sets r_p(F_p^3) (2023) | **NEW RECORD** r_7 ≥ 227 (was 225), r_11 ≥ 1010 (was 1005). Claimed α_7 improvement is FALSE (Führer–Taranchuk give α_7 ≥ 6.38) — corrected by reviewer | ✔ | own line check (2793 / 16093 lines) | New-lower-bounds-for-line-free-sets… |
| A05 | Multicolour van der Waerden W(r,k) lower bounds | **NEW RECORD** 16 entries (known product method with composite moduli) | ✔ | Lean re-run 2127 s | New-lower-bounds-for-multicolour-van-der-Waerden… |
| A11 | Cage (6,9): empty table cell | first explicit (6,9)-graph *in the tables*: n(6,9) ≤ 4368 (LPS X^{5,29}, 12180 vertices, already had girth 9 — reviewer) | ✔ | own BFS girth check | An-explicit-6-regular-graph… |
| A01 | Erdős #436: Λ(5,3), Λ(7,3) | PARTIAL: Λ(5,3) ≥ 99,999,999 and Λ(7,3) ≥ 9,999,999 (Lean, 1 native_decide); ≥ 313,714,024 / 180,317,500 computationally | ✔ (+native_decide) | own sieve confirms both first triples | Explicit-lower-bounds-for-runs… |
| A09 | MathOverflow 513798 (Jul 2026) | PARTIAL: conjecture false for n ≡ ±1 (mod 8); M(7)=18, M(9)=33; bound attained n=11,13 | ✔ constructions only | Lean re-run 51 s; definitions audited | Simple-polygons-whose-sides… |
| A04 | Ordowski's questions, OEIS A051903 (2019) | NO NEW RESULT (independent solution; priority Mishra–Senthilkumar PR #6759 and an earlier LLM audit) | ✔ | Lean re-run; witness checked | Ordowskis-questions… (honest note) |
| A02 | Erdős #902, Schütte f(4) | NO NEW RESULT | known bound only | — | — |
| A08 | No-four-on-a-circle grid (AlphaEvolve records) | NO NEW RESULT (near misses: one bad quadruple) | known bound only | — | — |
| A13 | Busy Beaver BB(6) holdouts | NO NEW RESULT (checker soundness proved) | tool only | — | — |
| A14 | Odd tilings by Reid's 11-omino | NO NEW RESULT | known tiling only | — | — |
