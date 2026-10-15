# Scripts (computational checks; not proofs)

Run everything from the paper directory (the one containing `paper.pdf`). Python 3 and a C compiler
are the only requirements.

| script | what it checks | runtime |
|---|---|---|
| `verify_constructions.py` | the four polygons in `data/polyN.json` / `lean/Main.lean` are simple, lie on the lines, the lines are in general position, n=11,13 polygons equal the alternating 2-factor G, n=7,9 polygons omit exactly one triangle | < 1 s |
| `enumerate_classes.c` | all commutation classes of reduced words of w0 (= simple wiring diagrams) for odd n ≤ 9: distribution of #components of G, parity of #A, per-cycle odd #A | n=7: 0.02 s, n=9: a few minutes |
| `enumerate_classes.py` | pure-Python version of the above for n ≤ 7 | 3 s |
| `potential_check.py` | one-step identity of the potential Φ (Lemma on #A) for all permutations and ascents, n ≤ 8 | 10 s |
| `parity_random.py` | parity of #components and per-cycle statement on random reduced words, odd n ≤ 23 | 3 s |

Outputs obtained on October 8, 2026:

```
n=5: commutation classes=62; #components distribution={1: 22, 3: 40}
n=7: commutation classes=24698; #components distribution={2: 7870, 4: 10220, 6: 6608}
n=9: commutation classes=112018190; components distribution: 2:6360134 4:35038062 6:39168090 8:23868000 10:7583904
     words with wrong #A parity=0; cycles with even #A=0
```
