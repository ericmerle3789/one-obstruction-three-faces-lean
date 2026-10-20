"""Lagarias 1990, Red Team pass 2: the second inequality of (4.13) (p. 51) and the count of normal windows in the
proof of Theorem 4.2 (p. 48). Deterministic."""
from fractions import Fraction
from itertools import product
from math import gcd


def S(beta, L):
    """sum_{n=1}^{floor(beta*L)} 2^n/n, exact, with L = log2 x."""
    return sum(Fraction(2**n, n) for n in range(1, int(beta * L) + 1))


L = 100
for beta in (Fraction(1, 2), Fraction(1), Fraction(2)):
    s = S(beta, L)
    P = Fraction(2 * 2**int(beta * L), L)
    good = Fraction(2 * 2**int(beta * L), 1) / (beta * L)
    print("beta=%s x=2^%d: S/P = %.4f | S/(2x^b/(b log2 x)) = %.4f | (S-P)/x^(1/2) = %.3e"
          % (beta, L, float(s / P), float(s / good), float((s - P) / 2**(L // 2))))


def N(v):
    return sum(v[j] * 2**j * 3**sum(v[j + 1:]) for j in range(len(v)))


w, M = (1, 1), 7
print("M=7, m=1, w=11: N(110) mod 7 =", N(w + (0,)) % M, "| N(111) mod 7 =", N(w + (1,)) % M)

worst = {}
for n in range(2, 10):
    for m in range(1, 4):
        if m > n:
            continue
        for M in range(2 * n * n * 2**m, 4 * n * n * 2**m):
            if gcd(M, 6) != 1:
                continue
            wins = [u for u in product((0, 1), repeat=m) if N(u) <= M]
            for l in range(0, n - m + 1):
                for a in product((0, 1), repeat=l):
                    for b in product((0, 1), repeat=n - l - m):
                        cnt = {}
                        for u in wins:
                            r = N(a + u + b) % M
                            cnt[r] = cnt.get(r, 0) + 1
                        c = max(cnt.values())
                        if c > worst.get(m, (0,))[0]:
                            worst[m] = (c, n, M, l, a, b)
for m in sorted(worst):
    print("m=%d: max normal windows in one class = %d, first at n=%d M=%d l=%d w=%s w~=%s" % ((m,) + worst[m]))
