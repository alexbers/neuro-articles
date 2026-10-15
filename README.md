# Open problems attacked by autonomous Claude agents (October 2026)

**Authors:** Claude (AI model by Anthropic) — run and submitted by Aleksandr Bersenev.

> **Not an official Anthropic publication. Not peer reviewed.** All research, problem selection,
> proofs, Lean certificates and paper texts were produced autonomously by Claude (Opus 5.5) agents running
> in Claude Code. The human operator gave the high-level instruction ("find open problems, solve them and
> certify the results in Lean, in the style of OpenAI's 2026 math release"), provided compute, and chose the
> byline and venue. Novelty claims are "to our knowledge as of the paper date"; please report errors or prior
> work via GitHub issues.

This repository contains 19 preprints with new (machine-checked) results produced in two rounds:
round 1 (2026-10-08, 15 agents, a workstation) and round 2 (2026-10-14/15, 10 agents, a 30-core compute node,
focus on better-known problems). Agents whose work produced no new result are listed in
`process/*_RESULTS.md` but have no paper here.

## Round 2 (2026-10-14/15)
| Paper | Result | Verification |
|---|---|---|
| [A kissing configuration of 12\,277 points in dimension 19](papers/round2/A-kissing-configuration-of-12277-points-in-dimension-19-October-14-2026/paper.pdf) | Kissing number τ₁₉ ≥ 12277 (was 12276) | Lean (kernel); independent exact check of all pairs |
| [A new lower bound for the cap set capacity](papers/round2/A-new-lower-bound-for-the-cap-set-capacity-October-14-2026/paper.pdf) | Cap-set capacity C ≥ 2.2203344 (FunSearch 2.2202337; X-evolve 2.2203085) | Lean (5 native_decide finite checks), re-run |
| [An improved upper bound for binary covering codes\\ of length 20 and covering radius 3](papers/round2/An-improved-upper-bound-for-binary-covering-codes-of-length-20-and-covering-radius-3-October-14-2026/paper.pdf) | K(20,3) ≤ 1984 (was 2048) | Lean (kernel); independent BFS over 2²⁰ words |
| [Mod-4 obstructions for completing the rank-47 $\F_2$ algorithms\\ for $4\times 4$ matrix multiplication](papers/round2/Mod-4-obstructions-for-completing-the-rank-47-F2-algorithms-for-4x4-matrix-multiplication-October-14-2026/paper.pdf) | The F₂ rank-47 4×4 matrix-multiplication schemes admit no rank-48 completion over Z/4 by a term vanishing mod 2 | Lean (6 native_decide checks); not independently re-run |
| [New best-known configurations for Heilbronn's triangle problem\\ in a triangle with $23$ and $35$ points](papers/round2/New-best-known-configurations-for-Heilbronns-triangle-problem-in-a-triangle-with-23-and-35-points-October-14-2026/paper.pdf) | Heilbronn in a triangle: n = 35 0.0042542725 (+1.33%), n = 23 0.0092790559 | Lean (kernel); independent exact check |
| [New certified upper bounds for the sign-uncertainty constant and the first autocorrelation constant](papers/round2/New-certified-upper-bounds-for-the-sign-uncertainty-constant-and-the-first-autocorrelation-constant-October-14-2026/paper.pdf) | Sign-uncertainty constant C_SU ≤ 48/(50π) ≈ 0.30558 (was 0.3089); C₁ ≤ 1.5027434864131 (marginal) | Lean (sign statement); independent Descartes re-check |
| [New lower bounds for hypergraph Ramsey numbers\\ from affine-invariant colourings](papers/round2/New-lower-bounds-for-hypergraph-Ramsey-numbers-from-affine-invariant-colourings-October-14-2026/paper.pdf) | R(5,5;3) ≥ 98 (was 88) and four more hypergraph Ramsey bounds | Lean (kernel); independent clique search |
| [Symmetric Hadamard matrices of orders 532 and 732](papers/round2/Symmetric-Hadamard-matrices-of-orders-532-and-732-October-14-2026/paper.pdf) | First symmetric Hadamard matrices of orders 532 and 732 | Lean (kernel), re-run; independent HHᵀ = nI check |
| [The best constant in Smale's mean value problem exceeds $1.048$](papers/round2/The-best-constant-in-Smales-mean-value-problem-exceeds-1.048-October-14-2026/paper.pdf) | Smale's mean value problem: lim K_d ≥ 1.048 (explicit quantitative failure of K = 1) | Lean (witness); paper lemmas refereed by an independent agent |

## Round 1 (2026-10-08)
| Paper | Result | Verification |
|---|---|---|
| [A balanced 13-variable Boolean function with absolute indicator 112](papers/round1/A-balanced-13-variable-Boolean-function-with-absolute-indicator-112-October-8-2026/paper.pdf) | Counterexample to the Zhang–Zheng (1995) GAC conjecture for n = 13: balanced f, deg 11, Δ_f = 112 < 128 | Lean (kernel); independent WHT/ANF re-check |
| [An explicit 6-regular graph of girth 9 on 4368 vertices](papers/round1/An-explicit-6-regular-graph-of-girth-9-on-4368-vertices-October-8-2026/paper.pdf) | First (6,9)-graph listed in the cage tables: n(6,9) ≤ 4368 | Lean (kernel); independent BFS girth check |
| [Explicit lower bounds for runs of three consecutive\\ quintic and septic residues](papers/round1/Explicit-lower-bounds-for-runs-of-three-consecutive-quintic-and-septic-residues-October-8-2026/paper.pdf) | Erdős #436: Λ(5,3) ≥ 313,714,024 and Λ(7,3) ≥ 180,317,500 (Lean core: ≥ 10⁸−1 / 10⁷−1) | Lean (one native_decide); independent sieve |
| [New four-dimensional linear codes over $\mathbb{F}_8$ and $\mathbb{F}_9$ improving Maruta's tables](papers/round1/New-four-dimensional-linear-codes-over-GF8-and-GF9-improving-Marutas-tables-October-8-2026/paper.pdf) | 191 improved entries of Maruta's n_q(4,d) tables (q = 8, 9); 29 exact values | Lean (kernel); independent min-distance check |
| [New lower bounds for line-free sets in $\mathbb{F}_7^3$ and $\mathbb{F}_{11}^3$](papers/round1/New-lower-bounds-for-line-free-sets-in-F7-3-and-F11-3-October-8-2026/paper.pdf) | r₇(F₇³) ≥ 227 (was 225), r₁₁(F₁₁³) ≥ 1010 (was 1005) | Lean (kernel); independent line check |
| [New lower bounds for multicolour van der Waerden numbers\\ from composite cyclic moduli](papers/round1/New-lower-bounds-for-multicolour-van-der-Waerden-numbers-from-composite-cyclic-moduli-October-8-2026/paper.pdf) | 16 improved lower bounds for multicolour van der Waerden numbers (known product method) | Lean (kernel), re-run |
| [New proper circulant weighing matrices\\ from a twin of the Singer construction](papers/round1/New-proper-circulant-weighing-matrices-from-a-twin-of-the-Singer-construction-October-8-2026/paper.pdf) | 6 new proper circulant weighing matrices (n = 146 … 762); conjectural twin family | Lean (kernel), re-run; independent PAF check |
| [Proof of Sun's conjecture on coprime adjacent sums\\ (OEIS A228886)](papers/round1/Proof-of-Suns-conjecture-on-coprime-adjacent-sums-OEIS-A228886-October-8-2026/paper.pdf) | Proof of Z.-W. Sun's 2013 conjecture (OEIS A228886), incl. the open even case | Lean (kernel), re-run |
| [Settling small open cases of signed difference sets](papers/round1/Settling-small-open-cases-of-signed-difference-sets-October-8-2026/paper.pdf) | Non-existence of (9,8,1)-SDS in Z₃²; 45 open SDS cases settled (26 apparently new) | Lean (kernel); independent certificate check |
| [Simple polygons whose sides lie on $n$ lines:\\ a parity obstruction and constructions](papers/round1/Simple-polygons-whose-sides-lie-on-n-lines-a-parity-obstruction-and-constructions-October-8-2026/paper.pdf) | MathOverflow 513798: M(7)=18, M(9)=33, conjecture false for n ≡ ±1 (mod 8); bound attained for n = 11, 13 | Lean (constructions only), re-run |

## What is in each paper directory
`paper.pdf`, LaTeX sources (`build/`), the agent-written problem statement in the style of OpenAI's prompts
(`PROBLEM.md`), Lean 4 certificates and their output (`lean/`), certificate data and checkers (`data/`), and a
README with the verification status (what is Lean-certified, what is paper-only) and a BibTeX entry.

## Process and verification
- `process/round1_PROMPT_TEMPLATE.md`, `process/round2_PROMPT_TEMPLATE.md`: the instructions given to the agents;
  `process/PAPER_TEMPLATE.md`: instructions for writing the papers.
- `process/round1_RESULTS.md`, `process/round2_RESULTS.md`: outcome of every agent, including failures.
- `verification/`: the coordinating agent's independent re-check scripts (exact arithmetic, written separately
  from the agents' code).
- Lean: core Lean 4.34/4.35, and Mathlib v4.35.0 where needed. Main theorems print only
  `propext, Classical.choice, Quot.sound`, except where `native_decide` is disclosed (two papers above).
- Machine-readable metadata (models, scaffold, human-involvement level, provenance) for indexing services such as
  slopXiv: `slopxiv/records.json` (Human Involvement Scale: HIS-1, "human-directed").

## License
Papers, texts and data: CC BY 4.0. Code (Lean files, scripts): MIT. See `LICENSE`.
