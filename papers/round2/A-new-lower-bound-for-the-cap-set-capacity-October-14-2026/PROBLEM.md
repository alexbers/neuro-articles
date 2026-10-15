# PROBLEM (B05): the cap-set capacity lower bound — beat the AI-search record 2.2203

## TARGET
Prove a new explicit lower bound for the cap-set capacity

    C = lim_{n→∞} r_3(F_3^n)^{1/n}   (r_3 = largest subset of F_3^n with no three distinct points on a line)

strictly larger than the best value in the literature, C ≥ 2.2203085 (X-evolve, arXiv:2508.07932, Aug 2025;
previously 2.2202337 by FunSearch, Nature 2023; 2.218021 Tyrrell 2022; 2.217389 Edel 2004).
Success = an explicit, independently verifiable certificate (finite combinatorial object + a proof that it yields
a cap set of size N in F_3^D with N^{1/D} > 2.2203085).

## DEFINITIONS
* Cap set: A ⊆ F_3^n with no solution of x+y+z=0 in A except x=y=z.
* Extendable collection (A0,A1,A2) of caps in F_3^d (Edel 2004): x,y∈A0, z∈A1∪A2 ⇒ x+y+z≠0, and
  x∈A0, y∈A1, z∈A2 ⇒ x+y+z≠0.
* Admissible set S ⊆ {0,1,2}^n (Tyrrell Def. 2.5): (pairs) for distinct s,s' there are i,j with
  s_i=0≠s'_i and s_j≠0=s'_j; (triples) for distinct s,s',s'' there is k with {s_k,s'_k,s''_k} = {0,1,2},
  {0,0,1} or {0,0,2} (as multisets).  Constant weight is NOT required.
* Extended product S(A0,A1,A2) = ∪_{s∈S} A_{s_1}×…×A_{s_n} ⊆ F_3^{dn}.  It is a cap (Edel Lemma 10 /
  Tyrrell Lemma 2.7) of size Σ_{s∈S} |A0|^{n-|s|} |A1|^{|s|} when |A1|=|A2|.
* Base: Calderbank–Fishburn collection (12,112,112) in F_3^6; middle level the recursively admissible
  Ĩ(m,m−1) gives (b0,b1)=(12·m·112^{m−1}, 112^m) in F_3^{6m}.  Bound: C ≥ (Σ_s b0^{n−|s|} b1^{|s|})^{1/(6mn)}.
* Symmetric (FunSearch) sets: coordinates in g groups of 3; a row t∈{0..6}^g with types
  000, 001, 002, 012, 021, 111, 222 expands to the product of the Z3-rotation orbits.

## STATUS AND SOURCES (checked 2026-10-14)
* Edel, Designs Codes Cryptogr. 31 (2004): 2.217389.  Tyrrell, Discrete Analysis 2023:20: 2.218021.
* Romera-Paredes et al. (FunSearch), Nature 625 (2024): I(15,10) full, A(24,17) of size 237,984 ⇒ 2.2202337
  (data: github.com/google-deepmind/funsearch/admissible_set).
* Zhai et al. (X-evolve), arXiv:2508.07932 (Aug 2025): A(21,15)=43,650, A(27,19)=1,270,863 ⇒ 2.2203085
  (priority program in github.com/zhaiyi000/x-evolve, admissible_set.ipynb).
* AlphaEvolve "Mathematical exploration and discovery at scale" (arXiv:2511.02864) does not treat cap sets.
  No later improvement found (web search Oct 2026; not in the OpenAI Oct-2026 release CONTENTS.md, not in round 1).
* Upper bound 2.7552 (Ellenberg–Gijswijt) — not targeted.

## RESEARCH DIRECTION
1. Fast C reimplementation of the symmetric greedy (FunSearch needed ~7 h per run in Python at n=24; we need 1.5 s;
   n=27: 40 s) → enables evolution strategies over priority-function parameters without an LLM.
2. Mixed-weight admissible sets: Tyrrell's definition does not require constant weight; adjacent layers w, w+1
   can be combined when the supports form an antichain.  In the bound a weight-(w+1) vector is worth b1/b0 =
   112/(12m) times a weight-w vector (2.33 for m=4).
3. Type-level reduction (rows instead of 10^6 vectors) for search and verification.
4. Other ideas tried: other base collections (SAT in F_3^4), SAT/WalkSAT for full symmetric sets, local search.

## PITFALLS
* The admissibility check on the expanded set (10^6 vectors) is infeasible directly; the type-level criterion
  must be proved correct (pairs: profiles incomparable; triples: some group whose type triple is "always good").
* Mixed weights: the size formula changes (Σ over vectors, not binomial × const); |A1|=|A2| needed.
* Don't confuse 2.22030849 (X-evolve) with rounding: improvements are in the 6th decimal.
* Float32 tie-breaking in the published greedy programs matters for reproducing published sizes.

## CERTIFICATE
Row file (types per group), independent Python verifier (P)+(T) with BAD table recomputed by brute force,
C checker, and Lean 4 statements (see README).
