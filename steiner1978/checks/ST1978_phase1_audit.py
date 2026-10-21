#!/usr/bin/env python3
"""ST1978 phase 1 (formaliste, 21/10/2026) — Steiner 1978, numerical audit before the Lean formalisation.

Davison's equation (2^(k+l) - 3^k) h = 2^l - 1 (Lagarias 1999, entry 158). Exact integer arithmetic, except P6
(mpmath, 60 digits) and P7 (float log 2, margins are large). Deterministic output.
"""
import mpmath

KMAX = 20000
A = 1584962500721156181453738943947816508759  # log2(3) * 10^39, truncated
B = 10 ** 39


def bitlen3(k):
    return (3 ** k).bit_length()


# P1, P2, P4
p1_hold, p1_next_fail, p2_hold, p4_bad = [], [], [], []
t = 1
for k in range(1, KMAX + 1):
    t *= 3
    pk = 1 << k
    Lk = t.bit_length()
    if k * A // B + 1 != Lk:
        p4_bad.append(k)
    if ((1 << Lk) - t) * (pk - 1) <= t - pk:
        p1_hold.append(k)
    if not (((1 << (Lk + 1)) - t) > t):
        p1_next_fail.append(k)
    E = t - (1 << (Lk - 1))
    if E > 0 and E * (pk + 1) <= t - pk:
        p2_hold.append(k)
print("P1  k <= %d with the positive inequality at L = Lk : %s" % (KMAX, p1_hold))
print("P1  k with 2^(Lk+1) - 3^k <= 3^k : %s" % p1_next_fail)
print("P2  k <= %d with the negative inequality at L = Lk - 1 : %s" % (KMAX, p2_hold))
print("P4  k <= %d with k*A//B + 1 != bit_length(3^k) : %s" % (KMAX, p4_bad))

# P3
sols = []
for k in range(1, 41):
    for l in range(0, 41):
        D = 2 ** (k + l) - 3 ** k
        R = 2 ** l - 1
        if D == 0:
            if R == 0:
                sols.append((k, l, "any"))
            continue
        if R % D == 0:
            sols.append((k, l, R // D))
nontriv = [s for s in sols if s[1] != 0]
print("P3  solutions with k <= 40, 1 <= l <= 40 : %s" % nontriv)
print("P3  solutions with l = 0 have h = 0 : %s" % all(s[2] == 0 for s in sols if s[1] == 0))

# P5
last14 = max(k for k in range(1, 2000) if 2 ** k - 1 < (2 * k) ** 14)
mpmath.mp.dps = 60
last133 = max(k for k in range(1, 2000) if mpmath.mpf(2) ** k - 1 < mpmath.mpf(bitlen3(k)) ** mpmath.mpf("13.3"))
print("P5  largest k with 2^k - 1 < (2k)^14 : %d" % last14)
print("P5  largest k with 2^k - 1 < Lk^13.3 : %d" % last133)

# P6 (corroboration only)
l2, l3 = mpmath.log(2), mpmath.log(3)
best = None
for H in range(2, 3001):
    # H = |u1| >= |u2|: u2 nearest to -u1 log2/log3; H = |u2| >= |u1|: u1 nearest to -u2 log3/log2 (then |u1| > |u2| unless small)
    cands = []
    for u1 in (H, -H):
        for u2 in (mpmath.floor(-u1 * l2 / l3), mpmath.ceil(-u1 * l2 / l3)):
            if abs(u2) <= H:
                cands.append((u1, int(u2)))
    for u2 in (H, -H):
        for u1 in (mpmath.floor(-u2 * l3 / l2), mpmath.ceil(-u2 * l3 / l2)):
            if abs(u1) <= H:
                cands.append((int(u1), u2))
    for u1, u2 in cands:
        if max(abs(u1), abs(u2)) != H:
            continue
        v = abs(u1 * l2 + u2 * l3) * mpmath.mpf(H) ** mpmath.mpf("13.3")
        if best is None or v < best[0]:
            best = (v, H, u1, u2)
print("P6  min |u1 log2 + u2 log3| * H^13.3 over 2 <= H <= 3000 : %s at H = %d, (u1, u2) = (%d, %d)"
      % (mpmath.nstr(best[0], 6), best[1], best[2], best[3]))

# P7
import math
p7 = [k for k in range(1, 201) if not (2 * k < (2 ** k - 1) * math.log(2))]
print("P7  k <= 200 with 2k >= (2^k - 1) ln 2 : %s" % p7)
