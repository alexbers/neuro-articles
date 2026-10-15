# Round 2 (Oct 14–15, 2026) — results of agents B01–B10

Setup: 10 agents, each choosing a recognized open problem in an assigned area; compute on compute-node
(30 cores / 370 GB, two 10-hour Slurm windows), Lean 4.35.0 (+ Mathlib v4.35.0) certificates, honest
README per agent, preprint (author Claude, Anthropic) in `papers/` when the result is new.
Prompt: `PROMPT_TEMPLATE.md`. Coordinator checks: Lean re-runs on the node and independent scripts in `coord/`.
Interruption: all agents were stopped on Oct 14 ~07:40 by an API weekly limit and resumed on Oct 15 03:00.

| Agent | Problem | Result | Lean | Coordinator check | Paper |
|---|---|---|---|---|---|
| B03 | Symmetric Hadamard matrices, open orders (Đoković 2022 list) | **SOLVED**: first symmetric Hadamard matrices of orders 532 = 4·133 and 732 = 4·183 (260 still open) | ✔ std axioms, no native_decide | Lean re-run 66 s; own numpy check H = Hᵀ, HHᵀ = nI | Symmetric-Hadamard-matrices-of-orders-532-and-732 |
| B10 | Smale's mean value conjecture (1981) | PARTIAL: lim K_d ≥ 1.048 (explicit quantitative failure; qualitative failure already follows from GPT-6 Astra, Sept 2026 + monotonicity) | witness only (std axioms); realisation lemma + monotonicity on paper | Lean re-run 32 s; independent referee agent: CORRECT (fixes applied) | The-best-constant-in-Smales-mean-value-problem-exceeds-1.048 |
| B02 | Hypergraph Ramsey numbers (Radziszowski DS1.18 §7.1) | **NEW RECORD** ×5: R(4,5;3) ≥ 38, R(5,5;3) ≥ 98 (was 88), R(4,6;3) ≥ 68, R(5,5;4) ≥ 38, R(5,6;4) ≥ 98 (≥ 104 C-checked only) | ✔ decide +kernel | own C clique checker: R(4,5;3), R(5,5;3) witnesses | New-lower-bounds-for-hypergraph-Ramsey-numbers… |
| B04 | Kissing number τ₁₉ (Cohn table) | **NEW RECORD** τ₁₉ ≥ 12277 (was 12276, K. Li Oct 2026) | ✔ 33 modules, no native_decide | own exact check of all 75 M pairs | A-kissing-configuration-of-12277-points-in-dimension-19 |
| B05 | Cap-set capacity (FunSearch / X-evolve benchmark) | **NEW RECORD** (small) C ≥ 2.2203344 (was 2.2203085) | ✔ with native_decide for 5 finite checks (disclosed) | Lean re-run 214 s | A-new-lower-bound-for-the-cap-set-capacity |
| B06 | AlphaEvolve benchmarks: sign-uncertainty C_SU, autocorrelation C₁ | **NEW RECORD** C_SU ≤ 48/(50π) ≈ 0.30558 (was 0.3089); C₁ ≤ 1.5027434864131 (−3·10⁻¹⁰, marginal) | ✔ sign statement (Hermite step on paper); C₁ full in Mathlib | own rebuild of P (deg 600) + own Descartes check of all 41 leaves | New-certified-upper-bounds-for-the-sign-uncertainty… |
| B09 | Covering codes (Kéri tables; football pool) | **NEW RECORD** K(20,3) ≤ 1984 (was 2048, "trivial"); football pool not improved | ✔ | own BFS over all 2²⁰ words | An-improved-upper-bound-for-binary-covering-codes… |
| B07 | Heilbronn triangle problem (live table, 2026 competition) | **NEW RECORD** triangle n = 35: 0.0042542725 (was 0.0041984702, +1.33%); n = 23: 0.0092790559 (was 0.0092756411) | ✔ decide +kernel | own exact Fraction check of all triples (new and previous records) | New-best-known-configurations-for-Heilbronns-triangle-problem… |
| B01 | Fast matrix multiplication: rank of 4×4 over Z (49 known; 48 needs 1/2; 47 only over F₂) | PARTIAL (new): the AlphaTensor and Kauers–Moosbauer F₂ rank-47 schemes admit no rank-48 completion over Z/4 (hence Z, Z₂) by a term vanishing mod 2; plus computational facts (no flips, 72,057 rank-48 F₂ schemes do not lift) | ✔ with 6 native_decide checks (disclosed); ~31 min/file | not independently re-run (agent's Python cross-check only) | Mod-4-obstructions-for-completing-the-rank-47-F2-algorithms… |
| B08 | Conference matrix of order 118 / open SRG parameters | NO NEW RESULT (computer-only partial exclusions, not certified) | — | — | — |

## Summary
- New certified results in 9 of 10 agents (all except B08); 1 problem solved outright (B03),
  1 explicit quantitative disproof bound for a named 1981 conjecture (B10), 6 benchmark/table records
  (B02, B04, B05, B06, B07, B09), 1 obstruction result (B01). B08: no new result.
- 9 preprints in `papers/` (B08 none). Coordinator independently re-checked B02–B07, B09, B10.
- Caveats: B04/B05/B06(C₁)/B07(n=23) improvements are small; B05 and B01 rely on native_decide for large
  finite checks; B06's Hermite step and B10's realisation lemma are paper proofs (B10 refereed).
