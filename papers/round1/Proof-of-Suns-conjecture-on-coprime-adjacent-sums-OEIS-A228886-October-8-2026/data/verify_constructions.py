#!/usr/bin/env python3
"""Independent numerical cross-check of the permutations defined in ../Main.lean
(transcribed 1:1 from the Lean definitions; Nat subtraction is truncated at 0 like in Lean).

  conjecture (1): sums coprime to n-1 and n+1   (OEIS A228886, Sun 2013)
  conjecture (2): sums coprime to 2n-1 and 2n+1 (companion conjecture, A228886 comments)

Also brute-forces A228886(n) for small n and compares with the OEIS data, to confirm that
the condition implemented here is the one counted by A228886.
Usage: python3 verify_constructions.py [N]   (default N = 3000)
"""
import sys
from math import gcd

def sub(a, b): return a - b if a >= b else 0          # Lean's truncated Nat subtraction

def oddA(n, i): return n if i == n else (i if i % 2 == 0 else sub(sub(n, 1), i))
def oddB(n, i):
    if i == 0: return 0
    if i == n: return n
    return i if i % 2 == 1 else sub(n + 1, i)
def evenA(n, i):
    m = n // 2
    if i == 0: return 0
    if i + 3 <= m: return i if i % 2 == 1 else sub(n + 1, i)
    if i == sub(m, 2): return m
    if i == sub(m, 1): return m + 3
    if i == m: return sub(m, 1)
    if i == m + 1: return m + 1
    return i if i % 2 == 0 else sub(n + 1, i)
def evenB(n, i):
    m = n // 2
    if i == 0: return 0
    if i + 1 <= m: return i if i % 2 == 1 else sub(n + 1, i)
    if i == m: return m + 1
    if i == m + 1: return sub(m, 1)
    if i == m + 2: return m + 3
    if i == m + 3: return m
    if i == m + 4: return sub(m, 3)
    return i if i % 2 == 0 else sub(n + 1, i)
SIX = [0, 1, 2, 4, 5, 3, 6]
def compA(n, i):
    if i == 0: return 0
    if i == n: return n
    return sub(n // 2, (i - 1) // 2) if i % 2 == 1 else n // 2 + i // 2
def compB(n, i):
    if i == 0: return 0
    if i == n: return n
    return n // 2 + 1 + (i - 1) // 2 if i % 2 == 1 else sub(n // 2 + 1, i // 2)
def compC(n, i):
    if i == 0: return 0
    if i + 6 <= n:
        if n % 2 == 0:
            return n // 2 + (i - 1) // 2 if i % 2 == 1 else sub(n // 2, i // 2)
        return sub(n // 2, (i - 1) // 2) if i % 2 == 1 else n // 2 + i // 2
    if i + 5 == n: return 1
    if i + 4 == n: return sub(n, 1)
    if i + 3 == n: return sub(n, 2)
    if i + 2 == n: return 2
    if i + 1 == n: return sub(n, 3)
    return n
FIVE = [0, 1, 4, 3, 2, 5]

def perm1(n):
    """the permutation used in the Lean proof of conjecture (1)"""
    if n % 2 == 1:
        return [oddB(n, i) for i in range(n + 1)] if n % 3 == 2 else [oddA(n, i) for i in range(n + 1)]
    if n == 6: return SIX[:]
    if n < 8: return None
    base = (lambda i: evenA(n, i)) if (n < 10 or n % 4 == 0) else (lambda i: evenB(n, i))
    if n % 3 == 1:
        return [sub(n, base(sub(n, i))) for i in range(n + 1)]
    return [base(i) for i in range(n + 1)]

def perm2(n):
    """the permutation used in the Lean proof of conjecture (2)"""
    if n == 2: return None
    if n % 3 == 2:
        return FIVE[:] if n < 8 else [compC(n, i) for i in range(n + 1)]
    return [compA(n, i) for i in range(n + 1)] if n % 2 == 0 else [compB(n, i) for i in range(n + 1)]

def ok(n, P, A, B):
    if P is None or len(P) != n + 1 or sorted(P) != list(range(n + 1)): return False
    if P[0] != 0 or P[-1] != n: return False
    return all(gcd(P[i] + P[(i + 1) % (n + 1)], A) == 1 and gcd(P[i] + P[(i + 1) % (n + 1)], B) == 1
               for i in range(n + 1))

def count(n, A, B):
    """brute force number of valid permutations (A228886 when A, B = n-1, n+1)"""
    good = lambda s: gcd(s, A) == 1 and gcd(s, B) == 1
    if not good(n): return 0
    used = [False] * (n + 1); used[0] = used[n] = True
    c = 0
    def dfs(v, k):
        nonlocal c
        if k == n:
            c += good(v + n); return
        for w in range(1, n):
            if not used[w] and good(v + w):
                used[w] = True; dfs(w, k + 1); used[w] = False
    dfs(0, 1)
    return c

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    oeis = [1, 0, 1, 0, 1, 8, 3, 24, 78, 1164, 34]          # A228886(1..11)
    bf = [count(n, n - 1, n + 1) for n in range(1, 12)]
    print("A228886(1..11) brute force:", bf, "matches OEIS:", bf == oeis)
    print("companion counts n=1..11:", [count(n, 2 * n - 1, 2 * n + 1) for n in range(1, 12)])
    bad1 = [n for n in range(1, N + 1) if n not in (2, 4) and not ok(n, perm1(n), n - 1, n + 1)]
    bad2 = [n for n in range(1, N + 1) if n != 2 and not ok(n, perm2(n), 2 * n - 1, 2 * n + 1)]
    print(f"conjecture (1): failures for 1 <= n <= {N}, n != 2,4:", bad1)
    print(f"conjecture (2): failures for 1 <= n <= {N}, n != 2:", bad2)
