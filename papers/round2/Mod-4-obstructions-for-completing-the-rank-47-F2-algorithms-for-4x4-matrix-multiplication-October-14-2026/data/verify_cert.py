"""Independent verifier of a witness-cover certificate (does not use the search code).

Claim: for the F2 scheme S = (u_t, v_t, w_t) of <n,m,p>, there are no d (first-order corrections) and no
x != 0, M such that  J(d) + x (x) M = rhs  over F2, where rhs = (T - sum_t u_t (x) v_t (x) w_t)/2 mod 2 and
J(d) = sum_t (du_t (x) v_t (x) w_t + u_t (x) dv_t (x) w_t + u_t (x) v_t (x) dw_t).
Certificate: functionals l_1..l_s on F2^{A x B x C} and subspaces L_i (given by bases) such that
  (1) l_i(rhs) = 1;   (2) l_i vanishes on every column of J;   (3) for every x in L_i: sum_a x_a l_i[a,:,:] = 0;
  (4) the union of the L_i covers F2^A \ {0}.
Then (2),(1) give l_i(x (x) M) = 1 for any solution, contradicting (3) for the i with x in L_i;
for x = 0 any l_i gives the contradiction l_i(J d) = 0 != 1.
usage: python verify_cert.py scheme_f2.txt cert.json
"""
import sys, json
import numpy as np


def load_txt(path):
    toks = open(path).read().split()
    n, m, p, r = map(int, toks[:4]); vals = list(map(int, toks[4:]))
    a, b, c = n * m, m * p, n * p
    U = np.array(vals[:r * a]).reshape(r, a)
    V = np.array(vals[r * a:r * a + r * b]).reshape(r, b)
    WT = np.array(vals[r * a + r * b:]).reshape(r, p, n)   # stored as C^T (p x n)
    W = WT.transpose(0, 2, 1).reshape(r, c)                # W[t, i*p+k]
    return n, m, p, U % 2, V % 2, W % 2, U, V, W


def main():
    n, m, p, u, v, w, U, V, W = load_txt(sys.argv[1])
    cert = json.load(open(sys.argv[2]))
    DA, DB, DC = n * m, m * p, n * p
    T = np.zeros((DA, DB, DC), dtype=np.int64)
    for i in range(n):
        for j in range(m):
            for k in range(p):
                T[i * m + j, j * p + k, i * p + k] = 1
    S = np.einsum('ta,tb,tc->abc', u, v, w)
    assert ((T - S) % 2 == 0).all(), 'not a scheme over F2'
    rhs = ((T - S) // 2) % 2
    E = DA * DB * DC
    covered = np.zeros(1 << DA, dtype=bool); covered[0] = True
    for idx, wt in enumerate(cert['witnesses']):
        bits = np.unpackbits(np.frombuffer(bytes.fromhex(wt['l']), dtype=np.uint8), bitorder='little')[:E]
        l = bits.reshape(DA, DB, DC).astype(np.int64)
        assert int((l * rhs).sum()) % 2 == 1, f'witness {idx}: l(rhs) != 1'
        # columns of J: e_a (x) v_t (x) w_t ; u_t (x) e_b (x) w_t ; u_t (x) v_t (x) e_c
        c1 = np.einsum('abc,tb,tc->ta', l, v, w) % 2
        c2 = np.einsum('abc,ta,tc->tb', l, u, w) % 2
        c3 = np.einsum('abc,ta,tb->tc', l, u, v) % 2
        assert not c1.any() and not c2.any() and not c3.any(), f'witness {idx}: not orthogonal to im(J)'
        span = [0]
        for bvec in wt['basis']:
            xs = np.array([(bvec >> a) & 1 for a in range(DA)], dtype=np.int64)
            assert not (np.tensordot(xs, l, axes=(0, 0)) % 2).any(), f'witness {idx}: x not in left kernel'
            span = span + [s ^ bvec for s in span]
        covered[span] = True
    assert covered.all(), f'coverage incomplete: {int((~covered).sum())} vectors uncovered'
    print(f'CERTIFICATE OK: {len(cert["witnesses"])} witnesses cover all {(1 << DA) - 1} nonzero x; '
          f'scheme rank {len(u)}, format <{n},{m},{p}>')


if __name__ == '__main__':
    main()
