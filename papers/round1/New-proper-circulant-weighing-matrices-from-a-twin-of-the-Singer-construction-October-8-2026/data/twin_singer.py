# Standalone reconstruction of the twin-Singer CW(2(q^2+q+1), q^2) for PRIME q (pure Python).
# K = GF(q)[x]/(f), f = x^3 + f2 x^2 + f1 x + f0 primitive, alpha = x.  Point i <-> <alpha^i>, i in Z_m.
# W_c(i) = eta( N(c*T(y) - y) * T(y) ),  y = alpha^i ;  A[k] = (W_0 + W_{1/2})/2 (k even), (W_0 - W_{1/2})/2 (k odd), at i = k mod m.
import json, sys
POLY = {11: (9, 6, 10), 13: (2, 9, 12), 17: (14, 8, 7), 19: (4, 18, 2), 5: (2, 0, 3), 7: (4, 0, 3), 3: (1, 1, 2)}
def build(q):
    f0, f1, f2 = POLY[q]
    def mulx(v):  # v*(x) mod f
        a0, a1, a2 = v
        return ((-a2 * f0) % q, (a0 - a2 * f1) % q, (a1 - a2 * f2) % q)
    N = q**3 - 1; pw = []; v = (1, 0, 0)
    for _ in range(N): pw.append(v); v = mulx(v)
    assert v == (1, 0, 0) and len(set(pw)) == N        # alpha is primitive
    log = {p: i for i, p in enumerate(pw)}
    return pw, log
def construct(q):
    pw, log = build(q); N = q**3 - 1; m = q*q + q + 1
    eta = lambda t: 0 if t % q == 0 else (1 if pow(t, (q - 1)//2, q) == 1 else -1)
    def tr(i):  # Tr(alpha^i) as element of GF(q) (constant polynomial)
        s = [(pw[i][j] + pw[(i*q) % N][j] + pw[(i*q*q) % N][j]) % q for j in range(3)]
        assert s[1] == 0 and s[2] == 0; return s[0]
    def norm(v):  # N(v) = v^(m) in GF(q); v nonzero vector
        e = (log[v] * m) % N; c = pw[e]; assert c[1] == 0 and c[2] == 0; return c[0]
    def W(c2, c_num):  # c = c_num / c2  in GF(q)
        cinv = pow(c2, q - 2, q); c = (c_num * cinv) % q; out = []
        for i in range(m):
            t = tr(i)
            if t == 0: out.append(0); continue
            y = pw[i]; v = (((c*t) - y[0]) % q, (-y[1]) % q, (-y[2]) % q)
            out.append(eta(norm(v) * t))
        return out
    W0, W1 = W(1, 0), W(2, 1)
    A = [((W0[k % m] + W1[k % m])//2 if k % 2 == 0 else (W0[k % m] - W1[k % m])//2) for k in range(2*m)]
    return A
def is_cw(a, k):
    n = len(a); S = [i for i in range(n) if a[i]]; r = [0]*n
    for i in S:
        for j in S: r[(j - i) % n] += a[i]*a[j]
    return r[0] == k and not any(r[1:])
if __name__ == '__main__':
    cert = json.load(open(sys.argv[1])) if len(sys.argv) > 1 else {}
    for q in (3, 5, 7, 11, 13, 17, 19):
        A = construct(q); n = len(A)
        same = cert.get(f'cwFam{n}', {}).get('seq') == A if cert else None
        print(f'q={q}: CW({n},{q*q}) {is_cw(A, q*q)}; equals certificate cwFam{n}: {same}')
