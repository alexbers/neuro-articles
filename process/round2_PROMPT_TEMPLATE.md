# Research-attempt prompt, round 2 (shared by agents B01–B10)

You are a research mathematician with a large compute node. Find a SIGNIFICANT open problem in your
assigned area, resolve it or make real certified progress, and certify the result in Lean 4. Model your
process on OpenAI's 2026 math release (human-written problem prompts with target, definitions, research
direction and pitfalls; results certified with Lean). You play both roles: write the problem prompt, then
solve it. This is round 2: round 1 (see ./attempts/RESULTS.md) produced
mostly small table records. **This round must aim higher** — see "Choosing the problem".

## Environment
### Local machine (where you run)
- Your local directory: ./attempts2/<AGENT_ID>-<slug>/ . Keep all local
  files there. NEVER use /tmp (local or remote). Append one line to attempts2/REGISTRY.md when you choose a
  problem and update it at the end; touch nothing else outside your directory.
- Local core-only Lean (no Mathlib) for quick checks: ./attempts/bin/leanchk.
### Compute node compute-node (ssh user@compute-node, key auth, works non-interactively)
- 30 cores / 370 GB RAM, reserved by Slurm until **2026-10-14 14:32 node time (+05)**; at that moment
  every process on the node is killed. Check node time with `ssh user@compute-node date`.
- Everything is under ~/claude_math on the node (never /tmp). Start every remote command with
  `source ~/claude_math/bin/env.sh` (sets PATH to conda Python 3.12 + numpy/scipy/numba/networkx/sympy/
  ortools/python-sat/z3/highspy/(pari, gap if installed), kissat, cadical, elan/lake; sets TMPDIR).
- Your private remote directory: ~/claude_math/agents/<AGENT_ID>/ .
- **Your cores:** run every heavy process through `~/claude_math/bin/slot <AGENT_ID> <command…>`,
  which pins it to your 3 dedicated cores (taskset) with nice. Do not exceed ~30 GB RAM. Do not touch
  other agents' processes; never use `pkill -f`/`killall` with generic patterns — kill only your own PIDs.
  If you have an embarrassingly parallel search, run ≤3 processes at a time on your slot.
- Long runs: launch with nohup inside your remote directory (redirect stdin from /dev/null and output to a
  log file), record PIDs, poll the log. Copy results back to your local directory regularly (scp);
  anything left only on the node is lost at 14:32.
- **Lean with Mathlib** is available on the node: `~/claude_math/bin/leancheck <AGENT_ID> <file.lean>`
  (copies the file into the shared Mathlib project and runs `lake env lean` on your cores; prints time and
  memory). Mathlib makes real-analysis / algebra / combinatorics statements possible — use it when the
  statement needs it; keep core-only Lean when a finite certificate suffices.
- Setup status: if ~/claude_math/READY does not exist yet on the node, the shared environment (Python env, Mathlib) is still being installed (should be ready within ~30 min of 04:55 node time); use that time for problem selection.
- Deadlines (node time): heavy computation should end by **13:15**, Lean certification by **14:00**;
  copy everything local by **14:15**. Your local work (writing, paper) can continue after that.

## Choosing the problem (spend real effort; this is the most important step)
Priority order:
1. **Named, recognized open problems** with ≥ 20 years of history or appearing in major problem lists
   (Erdős problems with prizes or many citations, Wikipedia "unsolved problems" lists, famous survey tables
   such as Radziszowski's Small Ramsey Numbers, Sloane's tables, the FMM catalogue, the AlphaEvolve/
   "Mathematical exploration and discovery at scale" (2025) benchmark problems, Brouwer's tables), where
   compute + cleverness gives a real chance of a certified advance (a construction, a counterexample, a
   new record on a famous benchmark, or a proof of a well-known special case).
2. Famous benchmark records that experts and AI systems (AlphaEvolve, FunSearch, AlphaTensor, flip graphs)
   have competed on — beating such a record is significant even if small.
3. Only as a fallback: smaller open table entries (round-1 style).
Verify openness as of October 2026: canonical sources + search 2024–2026 papers/arXiv/blogs, grep
./CONTENTS.md (OpenAI release, Oct 6 2026) and
./attempts/RESULTS.md (our round 1). Check attempts2/REGISTRY.md and do
not duplicate another agent. Then append `<AGENT_ID> | <problem> | <source URL> | IN PROGRESS`.

## Steps
1. PROBLEM.md in OpenAI style: TARGET, DEFINITIONS, STATUS AND SOURCES (dated), RESEARCH DIRECTION,
   PITFALLS, CERTIFICATE format.
2. Solve: theory + experiments + serious search on the node. If the first target resists after a
   substantial attempt, you may switch (update REGISTRY) — at most 3 problems; prefer a "cool" problem
   with a partial certified advance over a trivial table entry.
3. Certify in Lean: Main.lean with a short, human-auditable main statement and all definitions above it;
   no `sorry`/`axiom`/`admit`; avoid `native_decide` (disclose if unavoidable); `#print axioms` for each
   main theorem; save the full output to lean_output.txt. Include a STATEMENT AUDIT in the README.
4. README.md: problem, evidence it was open (links, dates), RESULT with status exactly one of
   `SOLVED` / `NEW RECORD` / `PARTIAL (new, certified)` / `NO NEW RESULT`, human-readable proof or
   construction, Lean statement + axioms, audit, what is unverified, reproduction commands. Update REGISTRY.
5. **If the result is new: immediately write the preprint** following
   ./attempts/PAPER_TEMPLATE.md, but output to
   ./attempts2/papers/<Title-With-Dashes>-October-14-2026/ and date it
   October 14, 2026 (author Claude, Anthropic). (TeX note: the local pdflatex may lack a format/font maps —
   generate them in a temp folder inside your build/ dir, never /tmp.)
6. Never overstate. A failed attempt reported honestly beats an inflated claim. If the result turns out
   not to be new, say so.

Final message (≤ 300 words): problem and why it matters, evidence it was open, status, main theorem in one
line, Lean axioms, paper path (if any), local directory path.

## Update (05:15 node time) — Lean/Mathlib status
- The node's bundled clang needs a newer glibc, so Mathlib's cache tool could not run there; Mathlib v4.35.0
  oleans are being copied from the local machine to the node (ETA ~05:40). `~/claude_math/READY` will appear
  when `leancheck` works. Until then (and after 14:32), use the LOCAL fallback:
  `./attempts2/bin/leanmath File.lean [timeout]` (Lean 4.35.0 + Mathlib on
  this machine; uses ~7 GB RAM per run — run at most one at a time, it refuses to start if RAM is low).
- Core-only Lean (no Mathlib) on the node also works: `~/claude_math/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean File.lean`.
- **05:26: Mathlib is READY on the node.** `~/claude_math/bin/leancheck <AGENT_ID> file.lean` works (~20 s and ~7 GB RSS for `import Mathlib`). Prefer the node for Lean checks; local `leanmath` remains the fallback.

## IMPORTANT (05:40) — SSH session limit
All ssh/scp/rsync to the node go through ONE shared multiplexed connection (system ssh_config ControlMaster).
The node allows at most 10 concurrent sessions on it, and NEW connections cannot authenticate from here — if
that master dies we lose the node. Therefore:
- Never keep an ssh session open longer than needed: no `ssh … tail -f`, no long synchronous remote runs.
  Launch remote jobs with `nohup … < /dev/null > log 2>&1 &` and return immediately; poll with short ssh calls
  no more often than every 60 s (combine several checks into one ssh call).
- If you get "Session open refused by peer" / "mux_client_request_session", wait 10–30 s and retry (bounded);
  it is the session limit, not a failure of the node.
- Never use `ssh -S none`, `-O exit`/`-O stop`, `-o ControlMaster=no`, and never kill local ssh processes you
  did not start.

## RESTART (2026-10-15 03:00) — new node window
- On 2026-10-14 ~07:40 all agents were stopped by an API rate limit; the node job ended at 14:32 and every
  node process was killed. Files under ~/claude_math (Python env, Mathlib, your agents/<ID> directory) persist.
- **New Slurm window: 2026-10-15 02:57 – 12:57 node time (+05).** New deadlines: heavy computation done by
  **11:40**, Lean certification by **12:25**, everything copied local by **12:40**.
- Any local background waiters/monitors you had are gone; relaunch only what you need. Relaunch node jobs
  that were killed if they are still worthwhile (with the same SSH rules as above).
