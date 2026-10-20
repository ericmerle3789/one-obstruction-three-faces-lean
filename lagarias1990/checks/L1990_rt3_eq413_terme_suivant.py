"""Lagarias 1990, Red Team pass 3: (4.13), p. 51, the size of the correction to sum_{n <= beta log2 x} 2^n/n.
Deterministic (exact rationals)."""
from fractions import Fraction


def S(N):
    return sum(Fraction(2**n, n) for n in range(1, N + 1))


for beta in (Fraction(1, 2), Fraction(1), Fraction(11, 10), Fraction(2)):
    for L in (100, 200, 400):
        N = int(beta * L)                       # floor(beta * log2 x)
        s = S(N)
        xb = Fraction(2) ** N if beta * L == N else None
        G = 2 * xb / (beta * L)                 # 2 x^beta / (beta log2 x)
        P = 2 * xb / L                          # printed main term 2 x^beta / log2 x
        half = Fraction(2) ** (N // 2)          # x^(beta/2) (N even here)
        print("beta=%s x=2^%d: (S-G)/x^(b/2) = %.3e | (S-G)(b log2 x)^2/(2x^b) = %.4f | S<P: %s"
              % (beta, L, float((s - G) / half), float((s - G) * (beta * L) ** 2 / (2 * xb)), s < P))
