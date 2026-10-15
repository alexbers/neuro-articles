import numpy as np

def fwht(a):
    """Unnormalized Walsh-Hadamard transform along last axis (length 2^n)."""
    a = np.array(a, dtype=np.int64, copy=True)
    shp = a.shape
    N = shp[-1]
    a = a.reshape(-1, N)
    h = 1
    while h < N:
        a = a.reshape(a.shape[0], -1, 2, h)
        x = a[:, :, 0, :].copy(); y = a[:, :, 1, :].copy()
        a[:, :, 0, :] = x + y; a[:, :, 1, :] = x - y
        a = a.reshape(a.shape[0], N)
        h *= 2
    return a.reshape(shp)

def perm_action(n, perm):
    """perm: list p with x_i -> position p[i]: (Px)_{p[i]} = x_i. returns image array of all 2^n ints."""
    xs = np.arange(1 << n, dtype=np.int64)
    out = np.zeros_like(xs)
    for i in range(n):
        out |= ((xs >> i) & 1) << perm[i]
    return out

def matrix_action(n, cols):
    """linear map given by images of basis vectors e_i -> cols[i] (int bitmask)."""
    xs = np.arange(1 << n, dtype=np.int64)
    out = np.zeros_like(xs)
    for i in range(n):
        out ^= ((xs >> i) & 1) * cols[i]
    return out

def orbits(n, gens):
    """gens: list of arrays g (images of each x). returns orbit id array and list of orbits."""
    N = 1 << n
    parent = np.arange(N, dtype=np.int64)
    def find_all(p):
        while True:
            q = p[p]
            if np.array_equal(q, p): return p
            p = q
    for g in gens:
        # union x with g[x] repeatedly via label propagation
        pass
    # label propagation: label = min over orbit
    lab = np.arange(N, dtype=np.int64)
    while True:
        new = lab.copy()
        for g in gens:
            # orbit min: lab[x] = min(lab[x], lab[g[x]]) and lab[g[x]] = min(...)
            np.minimum.at(new, g, lab)
            new = np.minimum(new, new[g])
        if np.array_equal(new, lab): break
        lab = new
    reps, oid = np.unique(lab, return_inverse=True)
    return oid, reps

def class_matrix(n, oid, k):
    """C[i][j] = sum_{x in O_i} (-1)^{u_j . x}, with u_j = representative of dual orbit j.
    Assumes dual action orbits coincide with primal orbits (true for permutation groups / orthogonal maps)."""
    N = 1 << n
    ind = np.zeros((k, N), dtype=np.int64)
    ind[oid, np.arange(N)] = 1
    F = fwht(ind)  # F[i][u]
    return F
