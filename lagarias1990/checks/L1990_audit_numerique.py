"""Numerical audit of Lagarias, Acta Arith. 56 (1990) 33-53 (tables and constants).
Deterministic. Predictions: L1990_audit_numerique.predictions.md (written before the run)."""
from fractions import Fraction
from math import comb, gcd, log, log2, floor
from itertools import product


def N(v):  # (2.7b)
    n = len(v)
    return sum(v[j] * 2**j * 3**sum(v[j + 1:]) for j in range(n))


def D(v):  # (2.7a)
    return 2**len(v) - 3**sum(v)


def x(v):
    return Fraction(N(v), D(v))


def T(q):  # 3x+1 on Q_(2), parity of the numerator
    return q / 2 if q.numerator % 2 == 0 else (3 * q + 1) / 2


def mobius(n):
    r, p, m = 1, 2, n
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            r = -r
        p += 1
    return -r if m > 1 else r


def I(n):
    return sum(mobius(d) * 2**(n // d) for d in range(1, n + 1) if n % d == 0) // n


print("== P1 Table 2.1")
tab21 = [2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335, 630, 1161, 2182, 4080, 7710, 14532, 27594, 52377]
bad = [n for n in range(1, 21) if I(n) != tab21[n - 1]]
print("mismatches:", bad, "| sum_{d|n} d I(d) = 2^n for n<=20:",
      all(sum(d * I(d) for d in range(1, n + 1) if n % d == 0) == 2**n for n in range(1, 21)))

print("== P2 Table 2.2")
tab22 = {"1": (-1, 1), "0": (0, 1), "10": (1, 1), "110": (-5, 1), "100": (1, 5),
         "1110": (-19, 11), "1100": (5, 7), "1000": (1, 13),
         "11110": (-65, 49), "11100": (19, 5), "11010": (23, 5), "11000": (5, 23), "10100": (7, 23), "10000": (1, 29),
         "111110": (-211, 179), "111100": (-65, 17), "111010": (-73, 17), "111000": (19, 37), "110100": (23, 37),
         "110010": (31, 37), "110000": (1, 11), "101000": (7, 55), "100000": (1, 61)}
expected = set()
for n in range(1, 7):
    for v in product("01", repeat=n):
        s = "".join(v)
        rots = {s[i:] + s[:i] for i in range(n)}
        if len(rots) == n:
            expected.add(max(rots))
ok = True
for s, (a, b) in tab22.items():
    v = [int(c) for c in s]
    if x(v) != Fraction(a, b):
        ok = False
        print("  value mismatch", s, x(v), (a, b))
    # check periodicity with the right parity vector (Theorem 2.1)
    q, par = x(v), []
    for _ in range(len(v)):
        par.append(q.numerator % 2)
        q = T(q)
    if q != x(v) or par != v:
        ok = False
        print("  Thm 2.1 fails on", s)
print("rows:", len(tab22), "| complete list of lex-max primitive words:", expected == set(tab22),
      "| all values and Thm 2.1 OK:", ok)
print("rows with gcd(N,D)>1:", [(s, D([int(c) for c in s]), x([int(c) for c in s]).denominator)
                                for s in tab22 if gcd(N([int(c) for c in s]), D([int(c) for c in s])) > 1
                                and N([int(c) for c in s]) != 0])


def Tk(k, n):
    return (3 * n + k) // 2 if n % 2 else n // 2


def on_cycle(k, n0, cap=10**6):
    seen, n = set(), n0
    for _ in range(cap):
        seen.add(n)
        n = Tk(k, n)
        if n == n0:
            return len(seen)
        if n in seen:
            return 0
    return None


print("== P3 Table 3.1")
tab31 = [(1, 1, 2), (5, 1, 3), (7, 5, 4), (11, 1, 6), (13, 1, 4), (17, 1, 7), (19, 5, 11), (23, 5, 5), (25, 7, 16),
         (29, 1, 5), (31, 13, 23), (35, 7, 3), (37, 19, 6), (41, 1, 20), (43, 1, 11), (47, 5, 18), (49, 25, 38),
         (53, 103, 29), (55, 1, 12), (59, 1, 28), (61, 1, 6), (65, 19, 24), (67, 17, 30), (71, 29, 10), (73, 19, 60),
         (77, 1, 38), (79, 1, 44), (83, 65, 24), (85, 7, 100), (89, 17, 17), (91, 1, 48), (95, 1, 72), (97, 1, 18),
         (101, 7, 14), (103, 5, 21), (107, 1, 106), (109, 19, 52), (113, 1, 29), (115, 13, 27), (119, 1, 75),
         (121, 5, 44), (125, 1, 7), (127, 1, 37), (131, 13, 26), (133, 11, 36), (137, 1, 14), (139, 11, 136),
         (143, 7, 140), (145, 1, 10), (149, 19, 59)]
assert [r[0] for r in tab31] == [k for k in range(1, 150) if k % 6 in (1, 5)]
good, unknown = 0, []
for k, n0p, Lp in tab31:
    n0 = 1
    while True:
        if gcd(n0, k) == 1:
            r = on_cycle(k, n0)
            if r is None:
                unknown.append((k, n0))
            elif r > 0:
                break
        n0 += 1
    if (n0, r) == (n0p, Lp):
        good += 1
    else:
        print("  row mismatch k=%d: printed (%d,%d), computed (%d,%d)" % (k, n0p, Lp, n0, r))
print("rows exact: %d/50 | undecided trajectories: %s" % (good, unknown))


def cycle_vector(k, n0):
    v, n = [], n0
    while True:
        v.append(n % 2)
        n = Tk(k, n)
        if n == n0:
            return v


print("== P5 p.41 min_l |2^n-3^l| / 2^n")
for n in (85, 107, 139, 100, 106, 136):
    print("  n=%d: %.4f" % (n, min(abs(2**n - 3**l) for l in range(n + 1)) / 2**n))
for k, n0 in ((85, 7), (107, 1), (139, 11)):
    v = cycle_vector(k, n0)
    g = gcd(N(v), D(v))
    print("  k=%d: period %d, l=%d, D>0: %s, x(v)=n0/k: %s, log10 gcd(N,D) = %.1f" % (
        k, len(v), sum(v), D(v) > 0, x(v) == Fraction(n0, k), log(g, 10)))

print("== P4 constants")
phi = 1 / log2(3)
H = -phi * log2(phi) - (1 - phi) * log2(1 - phi)
ac = (1 - H) / (2 - H)
print("  phi=%.6f H(phi)=%.6f alpha_c=%.7f beta_c=1/(1-alpha_c)=%.6f 2-H=%.6f" % (phi, H, ac, 1 / (1 - ac), 2 - H))

print("== P6 necklaces with n ones, length 2n, vs n^-1 C(2n,n)")


def phi_e(d):
    return sum(1 for i in range(1, d + 1) if gcd(i, d) == 1)


for n in (1, 2, 3, 4, 5, 10, 20, 40):
    c = sum(phi_e(d) * comb(2 * n // d, n // d) for d in range(1, n + 1) if n % d == 0) // (2 * n)
    print("  n=%d: classes=%d, C(2n,n)/n=%.1f, ratio=%.4f" % (n, c, comb(2 * n, n) / n, c / (comb(2 * n, n) / n)))

print("== P7 (4.4)")
print("  printed sum == 3(3^n-2^n) for n<=30:", all(sum(2**j * 3**(n - j) for j in range(n)) == 3 * (3**n - 2**n) for n in range(1, 31)),
      "| corrected sum == 3^n-2^n:", all(sum(2**j * 3**(n - 1 - j) for j in range(n)) == 3**n - 2**n for n in range(1, 31)))

print("== P8 example 5/(2^m-9)")
okm = all((x([1, 1] + [0] * (m - 2)) == Fraction(5, 2**m - 9)) and
          ((gcd(5, 2**m - 9) == 1) == (m % 4 != 2)) for m in range(4, 60))
lit = all((gcd(5, 2**(m + 2) - 9) == 1) == (m % 4 != 0) for m in range(2, 60))
print("  length-m reading consistent:", okm, "| literal 1^2 0^m gives condition m != 0 mod 4:", lit)

print("== P9 Z(d,k) invariance and sign")
print("  k=9, n=1: T_9(1) =", Tk(9, 1), "gcd =", gcd(Tk(9, 1), 9))
inv = all(gcd(Tk(k, n), k) == gcd(n, k) for k in range(1, 200) if k % 6 in (1, 5) for n in range(-500, 501))
sign = all(Tk(k, n) == -Tk(-k, -n) for k in range(1, 50, 2) for n in range(-50, 51))
lit_sign = all(Tk(k, n) == Tk(-k, -n) for k in range(1, 50, 2) for n in range(-50, 51))
print("  invariance for k = +-1 mod 6:", inv, "| T_k(n) = -T_{-k}(-n):", sign, "| printed T_k(n) = T_{-k}(-n):", lit_sign)

print("== P10", 2**4 + 3, 2**2 + 2 * 3 + 3**2)

print("== P11 Theorem 3.1 constants")
print("  (125/64) ln3 / 3 = %.4f ; 0.99*4/5 = %.4f" % (125 / 64 * log(3) / 3, 0.99 * 4 / 5))
print("  c_max(a=ln2) = %.4f ; c_max(a=0.92129) = %.4f" % ((3 * log(2) / log(3))**(1 / 3), (3 * 0.92129 / log(3))**(1 / 3)))

print("== P12 Theorem 3.5")
ok12 = True
for n in range(1, 13):
    for v in product((0, 1), repeat=n):
        q = x(list(v))
        if q < 0 and (q > -1 or (q == -1) != all(v)):
            ok12 = False
print("  x(v)<0 => x(v)<=-1, equality iff v=1^n (n<=12):", ok12)

print("== P13 Theorem 4.1")
fails_final = fails_corr = fails_printed = 0
first_printed = None
for n in range(1, 13):
    nums = [N(list(v)) for v in product((0, 1), repeat=n)]
    for M in range(2, 201):
        if M % 3 == 0:
            continue
        cnt = {}
        for a in nums:
            cnt[a % M] = cnt.get(a % M, 0) + 1
        F = max(cnt.values())
        m = 0
        while 3**(m + 1) <= M and m + 1 <= n:
            m += 1
        final = n + 1 if M > 3**n else 2 * n * 2**n / M**phi
        if F > final + 1e-9:
            fails_final += 1
        if M < 3**n and F > (m + 1) * 2**(n - m):
            fails_corr += 1
        if M < 3**n and F > m * 2**(n - m):
            fails_printed += 1
            first_printed = first_printed or (n, M, F, m)
print("  final bound failures:", fails_final, "| corrected (m+1)2^(n-m) failures:", fails_corr,
      "| printed m*2^(n-m) failures:", fails_printed, "first:", first_printed)
