#!/usr/bin/env python3
# run_132 — L-A1 against Halbeisen–Hungerbühler 1997 (round 20). Recorded in the lab as D041 (labtrace id=374,
# 2026-10-19; predictions frozen beforehand: run_132.predictions.md). Checks, on 3,000 random block profiles with q
# of either sign: (P1) HH's phi of the parity word equals 2^{m_0} R_0 - q (R_0 from cycles.md 12.6.1, unreduced q);
# (P2) HH eq. (13) letter by letter; (P3) HH Lemma 9, eq. (15): gcd(q, phi(t)) is one number over all letter
# rotations, and it equals gcd(q, R_r) over the block rotations (L-A1's corollary); (P4) L-A1's recurrence is the
# Terras step on cycle numerators composed over a block; (P5) HH eq. (4) holds for phi and for W0 = 2^{m_0} R_0 =
# phi + q (the cocycle of ContentDescent.lean, L-A4). Output: run_132_output.txt (12,000 checks, 0 failures).
# Body below unchanged.
"""D041 — L-A1 face à Halbeisen–Hungerbühler 1997 (et le cocycle de L-A4). Entiers exacts, graine fixe."""
import random
from math import gcd

NCHK = [0, 0]
def check(c, lab):
    NCHK[0] += 1
    if not c:
        NCHK[1] += 1; print("  ECHEC :", lab)
    return c

def phi(w):                       # HH (2) : ϕ({})=0, ϕ(s0)=ϕ(s), ϕ(s1)=3ϕ(s)+2^{l(s)}
    v = 0
    for i, b in enumerate(w):
        if b: v = 3 * v + (1 << i)
    return v

def word(ms, ss):
    w = []
    for m, s in zip(ms, ss): w += [1] * m + [0] * s
    return w

def R_def(ms, ss, r):             # cycles.md 12.6.1
    p = len(ms); m = [ms[(r+i) % p] for i in range(p)]; s = [ss[(r+i) % p] for i in range(p)]
    S = [0] * p
    for t in range(1, p): S[t] = S[t-1] + s[t-1] + m[t]
    tot, pw = 0, 1
    for t in range(p-1, -1, -1):
        tot += (pw << (S[t] + s[t])) - (pw << S[t]); pw *= 3 ** m[t]
    return tot

rng = random.Random(1997)
nprof = 0; cocy_phi = cocy_W = 0
for it in range(3000):
    p = rng.randint(1, 6)
    ms = [rng.randint(1, 6) for _ in range(p)]; ss = [rng.randint(1, 6) for _ in range(p)]
    n, K = sum(ms), sum(ms) + sum(ss)
    q = (1 << K) - 3 ** n                       # signe quelconque
    if q == 0: continue
    nprof += 1
    w = word(ms, ss); l = len(w)
    # P1
    check(phi(w) == (R_def(ms, ss, 0) << ms[0]) - q, f"P1 it{it}")
    # P2 : HH (13), rotation à droite ρ(s) = (s_l, s_1..s_{l-1})
    rots = [w[k:] + w[:k] for k in range(l)]
    ok = True
    for t in rots:
        rt = [t[-1]] + t[:-1]
        if t[-1] == 0: ok &= phi(rt) == 2 * phi(t)
        else:          ok &= 3 * phi(rt) == 2 * phi(t) + 3 ** n - (1 << l)
    check(ok, f"P2 it{it}")
    # P3 : HH Lemme 9 (15) et corollaire de L-A1
    gl = {gcd(q, phi(t)) for t in rots}
    gb = {gcd(q, R_def(ms, ss, r)) for r in range(p)}
    check(len(gl) == 1 and gl == gb and gl == {gcd(phi(w), q)}, f"P3 it{it}")
    # P4 : récurrence L-A1 = (13) composée à l'envers (pas de Terras sur numérateurs N, x = N/q)
    ok = True
    for r in range(p):
        N = (R_def(ms, ss, r) << ms[r]) - q      # numérateur du début du bloc r
        for _ in range(ms[r]): N = (3 * N + q) // 2 if (3 * N + q) % 2 == 0 else None
        for _ in range(ss[r]): N = N // 2 if N is not None and N % 2 == 0 else None
        Rn = R_def(ms, ss, (r + 1) % p)
        ok &= N is not None and N == (Rn << ms[(r + 1) % p]) - q
        sig = ss[r] + ms[(r + 1) % p]
        ok &= (Rn << sig) == 3 ** ms[r] * R_def(ms, ss, r) + ((1 << ss[r]) - 1) * q
    check(ok, f"P4 it{it}")
    # P5 : concaténation HH (4) sur une coupe aux frontières de blocs ; W0 := 2^{m0} R0 = ϕ + q
    if p >= 2:
        c = rng.randint(1, p - 1)
        u, v = word(ms[:c], ss[:c]), word(ms[c:], ss[c:])
        nu, nv = sum(ms[:c]), sum(ms[c:])
        if phi(u + v) == 3 ** nv * phi(u) + (1 << len(u)) * phi(v): cocy_phi += 1
        W = lambda a, b: (R_def(a, b, 0) << a[0])
        if W(ms, ss) == 3 ** nv * W(ms[:c], ss[:c]) + (1 << len(u)) * W(ms[c:], ss[c:]): cocy_W += 1
print(f"{nprof} profils (q des deux signes) ; P1-P4 contrôlés ci-dessus")
print(f"P5 : HH (4) sur ϕ : {cocy_phi} succès ; même loi sur W0 = 2^m0 R0 : {cocy_W} succès (sur les profils p ≥ 2)")
print(f"TOTAL : {NCHK[0]} contrôles, {NCHK[1]} échec(s)")
