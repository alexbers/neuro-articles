# Build the colouring of triples of GF(97) from the orbit description and check it is well defined.
import ast, itertools
L = open("../../papers/New-lower-bounds-for-hypergraph-Ramsey-numbers-from-affine-invariant-colourings-October-14-2026/data/describe_R553_97.txt").read().splitlines()
q = 97; g = 5
R1 = set(ast.literal_eval(L[1].split(":",1)[1])); Rg = set(ast.literal_eval(L[2].split(":",1)[1]))
sq = {(x*x) % q for x in range(1, q)}
inv = lambda x: pow(x, q-2, q)
def red_ordered(x, y, z):            # colour computed with base point x and "second" point y
    d = (y - x) % q
    if d in sq:  a = inv(d)          # a square: maps d -> 1
    else:        a = (g * inv(d)) % q  # maps d -> g (a is a square since d, g nonsquares)
    t = (a * (z - x)) % q
    return t in (R1 if d in sq else Rg)
col = {}
bad = 0
for tri in itertools.combinations(range(q), 3):
    vals = {red_ordered(*p) for p in itertools.permutations(tri)}
    if len(vals) != 1: bad += 1
    col[tri] = vals.pop()
print("inconsistent triples:", bad, "| red triples:", sum(col.values()), "of", len(col))
with open("col553.txt", "w") as f:
    for (a, b, c), v in col.items():
        if v: f.write(f"{a} {b} {c}\n")
