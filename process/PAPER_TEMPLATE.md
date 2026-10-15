# Paper-writing instructions (for agents that finished with a result)

Write a preprint about your result in the style of OpenAI's 2026 math release
(see e.g. ./preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/
— build/main.tex, README.md, paper.pdf), but with **Claude as the author**.

## Output location
./attempts/papers/<Title-With-Dashes>-October-8-2026/
  paper.pdf            compiled preprint
  README.md            same format as OpenAI's README (title link, Author, Date, BibTeX)
  build/main.tex       LaTeX source (+ references.bib, sections/ if you like)
  lean/Main.lean       copy of your certified Lean file
  lean/lean_output.txt copy of the verification output (with `#print axioms` lines)
  data/                certificate data, if any (small files only)
Never use /tmp; build inside build/ (`cd build && latexmk -pdf main.tex`, pdflatex is installed;
copy the resulting PDF to ../paper.pdf; remove aux/log files afterwards).

## Front matter
- `\author{Claude\\ \small Anthropic}` ; `\date{October 8, 2026}` ; pdfauthor={Claude (Anthropic)}.
- README.md:
  ```
  # [<Title>](paper.pdf)

  **Author:** Claude (Anthropic)

  **Date:** October 8, 2026

  ## Citation

  ```bibtex
  @misc{Claude:<Title-With-Dashes>-October-8-2026,
    author = {{Claude}},
    title = {{<Title>}},
    howpublished = {Claude research preprint (unpublished, not peer reviewed)},
    year = {2026}
  }
  ```
  ```
  Add below the BibTeX a short "Verification status" list: what is Lean-certified (theorem names,
  axioms), what is paper-only, and how to reproduce (`attempts/bin/leanchk lean/Main.lean`).

## Content (concise, rigorous, honest — typically 4–12 pages)
1. Abstract: exact result, nothing more than what is proved.
2. Introduction: the problem, its origin and history with accurate citations (only sources you actually
   checked; give arXiv ids / URLs / OEIS / MathOverflow links), prior bounds, what is new here.
3. Definitions and statement of the main theorem(s).
4. Proofs / constructions: human-readable, complete. Include the explicit certificate (or a compact
   description plus where the full data file is) so a reader can verify it independently.
5. Formal verification section: the Lean statement verbatim, the definitions it depends on, the
   statement audit (why it means exactly the theorem), the `#print axioms` output, Lean version
   (4.34.1, core only, no Mathlib), run time.
6. What is NOT verified / limitations / open questions.
7. References (BibTeX or thebibliography).
Do not overstate novelty: if you could not fully rule out prior work, say "to our knowledge, as of
October 8, 2026". Do not post or upload anything anywhere.

Final message: path to the paper directory, page count, and one line on what changed vs your README.
