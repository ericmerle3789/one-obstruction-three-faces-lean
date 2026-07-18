#!/usr/bin/env python3
# test_REQ-MATH-007_campagne_HR.py — ARES session 3
# CAMPAGNE MULTI-PERIODES pour tester l'hypothese H_R (rigidite d'equidistribution) :
# pour p = 4..23, top-2 n par fenetre d'echelle (delta < 0.05), crash c in {1,2} :
#   - u = (R_0 mod q)/q : si H_R est saine, u doit etre ~Uniform(0,1) sur la famille,
#     et JAMAIS 0 (0 = un cycle staircase existe !)
#   - gcd(q, R_r) invariant par rotation (consequence de la recurrence REQ-MATH-006)
#   - alignement du fantome 2-adique au crash (quand s_crash impair, c=1)
# Test d'uniformite : Kolmogorov-Smirnov grossier (seuil 1.36/sqrt(N) a ~5%).
import math
from mpmath import mp, mpf, log
mp.dps = 40
L = log(3)/log(2)

def rotations_R(m, s):
    p = len(m); out = []
    for r in range(p):
        ms = m[r:] + m[:r]; ss = s[r:] + s[:r]
        sig = [ss[t] + ms[(t+1) % p] for t in range(p)]
        Mafter = [0]*p; acc = 0
        for t in range(p-1, -1, -1):
            Mafter[t] = acc; acc += ms[t]
        tot, Spre = 0, 0
        for t in range(p):
            tot += 3**Mafter[t] * 2**Spre * (2**ss[t] - 1)
            Spre += sig[t]
        out.append(tot)
    return out

def build_profile(p, n, c):
    K = (3**n).bit_length(); S = K - n
    w = [mpf(L)**j for j in range(p-1)]
    tw = sum(w); target = [x*(n-c)/tw for x in w]
    ms, Tprev, run = [], 0, mpf(0)
    for j in range(p-1):
        run += target[j]
        Tj = int(run + mpf('0.5'))
        ms.append(max(1, Tj - Tprev)); Tprev = Tj
    ms[-1] += (n-c) - sum(ms)
    ms.append(c)
    ss = [1]*(p-1) + [S-(p-1)]
    return ms, ss, K, S

# candidats n par fenetre (delta < 0.05), n <= 60000
cands = []
p3 = 1
for nn in range(1, 60001):
    p3 *= 3
    K = p3.bit_length()
    delta = K - nn*L
    if delta < mpf('0.05'):
        cands.append((nn, float(delta)))

print(f"{'p':>3} {'n':>6} {'c':>2} {'gamma':>7} {'minlog2(R/q)':>12} {'u=(R0 mod q)/q':>15} {'gcd inv?':>8} {'ghost':>6}")
us = []
ghost_ok, ghost_n = 0, 0
for p in range(4, 24):
    lo = float(L**(p - mpf('0.6'))); hi = float(L**(p + mpf('0.6')))
    inwin = sorted([x for x in cands if lo <= x[0] <= hi], key=lambda x: x[1])[:2]
    for (n, d) in inwin:
        for c in (1, 2):
            ms, ss, K, S = build_profile(p, n, c)
            if ss[-1] < 1 or min(ms) < 1 or ms[-2] <= c:
                continue
            q = 2**K - 3**n
            Rs = rotations_R(ms, ss)
            minlog = min(float(log(mpf(R)/mpf(q))/log(2)) for R in Rs)
            u = (Rs[0] % q) / q
            us.append(u)
            g = [math.gcd(q, Rs[r]) for r in (0, len(Rs)//2, len(Rs)-1)]
            ginv = all(x == g[0] for x in g)
            gh = "-"
            if c == 1 and ss[-1] % 2 == 1:
                ghost_n += 1
                B = ss[-1] + 12
                w2 = (Rs[-1] * pow(q, -1, 2**B)) % 2**B
                val = 3**ms[-1] * w2 - 1
                v2 = (val & -val).bit_length() - 1 if val != 0 else -1
                ok = (v2 == ss[-1]); ghost_ok += ok
                gh = "OK" if ok else f"v2={v2}"
            gamma = float(-log(1 - mpf(3)**n / mpf(2)**K)/log(2))
            print(f"{p:>3} {n:>6} {c:>2} {gamma:>7.2f} {minlog:>12.2f} {u:>15.6f} {str(ginv):>8} {gh:>6}")

print(f"\nN = {len(us)} instances | u = 0 rencontre (cycle !) : {sum(1 for x in us if x == 0)} fois")
us_sorted = sorted(us)
ks = max(abs((i+1)/len(us_sorted) - x) for i, x in enumerate(us_sorted))
seuil = 1.36/math.sqrt(len(us_sorted))
print(f"Kolmogorov-Smirnov vs Uniform(0,1) : D = {ks:.4f} ; seuil 5% ~ {seuil:.4f} ; uniforme plausible ? {ks < seuil}")
print(f"Fantome 2-adique aligne : {ghost_ok}/{ghost_n} instances testees")
print(f"min(u) = {min(us):.6f} ; max(u) = {max(us):.6f}")
raise SystemExit(0)
