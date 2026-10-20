"""Lagarias 1990, Red Team pass 4: checks of the slips kept in README (pp. 34, 37, 39, 44). Deterministic."""
from fractions import Fraction
from itertools import product
from math import gcd


def N(v):
    return sum(v[j] * 2**j * 3**sum(v[j + 1:]) for j in range(len(v)))


def T(x):
    """The 3x+1 map on rationals with odd denominator: parity of the numerator."""
    return (3 * x + 1) / 2 if x.numerator % 2 else x / 2


def x_of(v):
    """x(v) = N(v)/D(v), D(v) = 2^n - 3^{#1} (Theorem 2.1)."""
    return Fraction(N(v), 2**len(v) - 3**sum(v))


# P1: p. 44, k_m/2 >= (2^{5n} - 2^n)/(3^n - 2^n) with m = 4n
cases = fails = fails2 = cases_odd = 0
for n in range(1, 15):
    for v in product((0, 1), repeat=n):
        l = sum(v)
        D = 2**n - 3**l
        if l == 0 or D <= 0:
            continue
        G0 = gcd(N(v), D)
        km = Fraction(2**(5 * n) - 3**l, G0)
        cases += 1
        cases_odd += v[0] == 1
        fails += not (km / 2 >= Fraction(2**(5 * n) - 2**n, 3**n - 2**n))
        fails2 += not (2 * G0 <= 3**n - 2**n)
print("P1 cases (D>0, l>=1, n<=14):", cases, "| with v_0 = 1:", cases_odd, "| failures k_m/2:", fails,
      "| failures 2G0 <= 3^n-2^n:", fails2)

# P2: p. 44, the denominator k_m of x(v 0^m)
v, m = (1, 0, 0), 4
w = v + (0,) * m
print("P2 x(100 0^4) =", x_of(w), "| (2^{n+m}-3^l)/G_m =", (2**7 - 3) // gcd(N(w), 2**7 - 3),
      "| printed (2^m-3^l)/G_0 =", (2**m - 3) // gcd(N(v), 2**3 - 3))

# P3: p. 37, exponent of 3 in the denominator
ok_period = ok_neq = True
for n in range(1, 11):
    for v in product((0, 1), repeat=n):
        k1 = sum(v)
        if k1 == 0:
            continue
        x = x_of(v)
        y = x
        for i in range(n):
            ok_period &= (y.numerator % 2) == v[i]
            y = T(y)
        ok_period &= (y == x)
        if N(v) != 0 and 2**n != 3**(k1 - 1):
            ok_neq &= x != Fraction(N(v), 2**n - 3**(k1 - 1))
print("P3 x(v) = N/(2^n - 3^{k+1}) is the T-periodic point with parity word v (n<=10):", ok_period,
      "| differs from N/(2^n - 3^k):", ok_neq)

# P4: p. 39, sign of delta
v = (1,)
D = 2 - 3
print("P4 v=1: D =", D, "gcd =", gcd(N(v), D), "D/(N,D) =", D // gcd(N(v), D), "| x(v) =", x_of(v),
      "reduced denominator", x_of(v).denominator)

# P5: p. 44, N(v) even
v = (0, 0, 1)
x = x_of(v)
cyc, y = [], 4
for _ in range(3):
    cyc.append(y)
    y = (3 * y + 5) // 2 if y % 2 else y // 2
print("P5 v=001: x(v) =", x, "N(v) =", N(v), "| T_5 orbit of 4:", cyc, "back to 4:", y == 4,
      "gcd(4,5) =", gcd(4, 5), "| some p<=20 with 2^p = 1 mod 4:", any(pow(2, p, 4) == 1 for p in range(1, 21)))

# P6: p. 34, k = 5
print("P6 x(100) =", x_of((1, 0, 0)), "| 5 mod 6 =", 5 % 6)
