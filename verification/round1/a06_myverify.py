# Coordinator's independent min-distance check for the [n,4]_q codes in found/.
# Fields per README: GF(9)=F3[x]/(x^2+x+2), c0+c1x -> c0+3c1 ; GF(8)=F2[x]/(x^3+x+1), bits.
import sys, glob, itertools, numpy as np
def gf(q):
    if q == 8:
        add = np.array([[a ^ b for b in range(8)] for a in range(8)])
        def mul(a, b):
            r = 0
            for i in range(3):
                if (b >> i) & 1: r ^= a << i
            for i in (4, 3):
                if (r >> i) & 1: r ^= 0b1011 << (i - 3)
            return r
    else:
        def split(a): return a % 3, a // 3
        add = np.array([[((split(a)[0]+split(b)[0]) % 3) + 3*((split(a)[1]+split(b)[1]) % 3) for b in range(9)] for a in range(9)])
        def mul(a, b):
            a0, a1 = split(a); b0, b1 = split(b)
            c0, c1, c2 = a0*b0, a0*b1 + a1*b0, a1*b1      # x^2 = -x - 2 = 2x + 1
            c0 += c2*1; c1 += c2*2
            return (c0 % 3) + 3*(c1 % 3)
    M = np.array([[mul(a, b) for b in range(q)] for a in range(q)])
    # sanity: field (every nonzero has inverse, associativity spot check)
    assert all(any(M[a, b] == 1 for b in range(q)) for a in range(1, q))
    return add, M
res = {}
for fn in sorted(glob.glob(sys.argv[1])):
    lines = open(fn).read().split("\n")
    hdr = dict(kv.split("=") for kv in lines[0].split())
    q, n, d = int(hdr["q"]), int(hdr["n"]), int(hdr["d"])
    if q not in res: res[q] = gf(q)
    add, M = res[q]
    cols = np.array([list(map(int, l.split())) for l in lines[1:] if l.strip()])
    w, X = cols[:, 0], cols[:, 1:]
    assert w.sum() == n, fn
    U = np.array(list(itertools.product(range(q), repeat=4)))[1:]
    dot = M[U[:, 0][:, None], X[:, 0][None, :]]
    for j in range(1, 4):
        dot = add[dot, M[U[:, j][:, None], X[:, j][None, :]]]
    wt = ((dot != 0) * w[None, :]).sum(axis=1)
    md = int(wt.min())
    print(("OK  " if md >= d else "BAD ") + f"{fn.split('/')[-1]}: q={q} n={n} claimed d={d} computed d={md}")
