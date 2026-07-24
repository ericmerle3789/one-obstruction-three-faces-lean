#!/usr/bin/env python3
# test_REQ-MATH-013_rigidite_strate_sans3.py — ARES (creuser la fissure, 2026-07-24, v2)
#
# QUESTION : dans la STRATE "sans souffle de trois" (s_t TOUS IMPAIRS => aucun facteur
# (2^{s_t}-1) n'apporte de 3), le DESACCORD u = dist(R_0 mod q, 0)/q (=0 ssi cycle) est-il
# RIGIDE (borne loin de 0) ? Clef : a n fixe, S=bit_length(3^n)-n et q=2^(S+n)-3^n sont FIXES ;
# seul le DECOUPAGE (m,s) fait bouger R_0. On demande donc : le decoupage de la strate peut-il
# amener R_0 mod q jusqu'a 0 (cycle), et jusqu'ou frole-t-il ? Strate vs general.
# ENUMERATION COMPLETE pour les petits n (decisif), echantillon dense sinon.
# v2 corrige la Mesure 2 de v1 (regime non-accorde q<0 / artefact gros q) apres auto-RED TEAM.
import math, random, itertools
from mpmath import mp, mpf, log
mp.dps = 60
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

def R0(m, s):
    p = len(m)
    sig = [s[t] + m[(t+1) % p] for t in range(p)]
    Mafter = [0]*p; acc = 0
    for t in range(p-1, -1, -1):
        Mafter[t] = acc; acc += m[t]
    tot, Spre = 0, 0
    for t in range(p):
        tot += 3**Mafter[t] * 2**Spre * (2**s[t] - 1); Spre += sig[t]
    return tot

def build_profile(p, n):
    K = (3**n).bit_length(); S = K - n
    w = [mpf(L)**j for j in range(p-1)]; tw = sum(w)
    target = [x*(n-1)/tw for x in w]
    ms, Tprev, run = [], 0, mpf(0)
    for j in range(p-1):
        run += target[j]; Tj = int(run + mpf('0.5'))
        ms.append(max(1, Tj - Tprev)); Tprev = Tj
    ms[-1] += (n-1) - sum(ms); ms.append(1)
    ss = [1]*(p-1) + [S-(p-1)]
    return ms, ss, K, S

# ---- generateurs de decoupages ----
def comps_positive(total, parts):        # compositions de total en `parts` entiers >=1
    for cuts in itertools.combinations(range(1, total), parts-1):
        pts = [0]+list(cuts)+[total]
        yield [pts[i+1]-pts[i] for i in range(parts)]
def comps_odd(S, parts):                 # compositions de S en `parts` entiers IMPAIRS >=1
    A = (S-parts)//2                      # s_i=2a_i+1, sum a_i=A, a_i>=0
    if A < 0 or (S-parts) % 2: return
    for bars in itertools.combinations(range(A+parts-1), parts-1):
        pts = [-1]+list(bars)+[A+parts-1]
        a = [pts[i+1]-pts[i]-1 for i in range(parts)]
        yield [2*x+1 for x in a]
def rand_comp_positive(total, parts):
    cuts = sorted(random.sample(range(1, total), parts-1))
    pts = [0]+cuts+[total]; return [pts[i+1]-pts[i] for i in range(parts)]
def rand_comp_odd(S, parts):
    A = (S-parts)//2
    if A < 0 or (S-parts) % 2: return None
    a = [0]*parts
    for _ in range(A): a[random.randrange(parts)] += 1
    return [2*x+1 for x in a]

# ===================== CANARIS =====================
print("=== CANARIS ===")
c1 = all(((2**s - 1) % 3 == 0) == (s % 2 == 0) for s in range(1, 30))
print(f"C1  3|(2^s-1) <=> s pair : {c1}")
m7 = [4,7,9,15,23,35,1]; n7 = sum(m7); K7 = (3**n7).bit_length(); S7 = K7 - n7
s7 = [1]*6 + [S7-6]; q7 = 2**K7 - 3**n7
d7 = [round(min(R % q7, q7-(R % q7))/q7, 2) for R in rotations_R(m7, s7)]
c2 = (d7 == [0.17,0.41,0.47,0.34,0.42,0.05,0.48])
print(f"C2  p=7 distances {d7} : {c2}")
c3 = all(x % 2 == 1 for x in s7)
print(f"C3  p=7 dans la strate (s7 tous impairs) : {c3}")
# C4 : R0 (une rotation) == rotations_R[0]  (coherence des deux implementations)
c4 = (R0(m7, s7) == rotations_R(m7, s7)[0])
print(f"C4  R0() coherent avec rotations_R[0] : {c4}")
if not (c1 and c2 and c3 and c4):
    print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# ===================== MESURE 1 : staircase naturel le long de la grille =====================
print("=== MESURE 1 : staircase n=round(L^p), p=4..22 — frolement min_r u_r et sa vitesse ===")
print(f"{'p':>3} {'n':>7} {'strate?':>8} {'bits(q)':>8} {'min_r u_r':>12} {'log2(min u)':>11}")
prev = None
for p in range(4, 23):
    n = int(round(float(mpf(L)**p)))
    ms, ss, K, S = build_profile(p, n)
    if S-(p-1) < 1 or min(ms) < 1: continue
    q = 2**K - 3**n
    if q <= 0: continue
    us = [min(R % q, q-(R % q))/q for R in rotations_R(ms, ss)]
    mu = min(us)
    print(f"{p:>3} {n:>7} {str(all(x%2==1 for x in ss)):>8} {q.bit_length():>8} {mu:>12.6f} {math.log2(mu) if mu>0 else 0:>11.2f}")
print("  (min_r u_r decroit ~ regulierement : le staircase FROLE de plus en plus pres, en proportion.)")

# ===================== MESURE 2 : a q FIXE, la strate peut-elle atteindre / approcher R_0=0 ? =====================
print("\n=== MESURE 2 : q fixe ; STRATE (s impairs) vs GENERAL (s quelconques) ; cycle atteint ? inf du frolement ? ===")
print(f"{'n':>4} {'p':>3} {'bits(q)':>8} {'mode':>10} {'#profils':>10} {'cycles(u=0)':>12} {'inf u':>12} {'gcd>1 %':>8} {'max gcd':>10}")
CAP = 400000
for n in [5, 8, 12, 17, 25, 40, 63]:
    K = (3**n).bit_length(); S = K - n; q = 2**K - 3**n
    # choisir p : <= min(6,S,n), meme parite que S (pour que des s impairs existent), maximal
    p = None
    for cand in range(min(6, S, n), 1, -1):
        if (S - cand) % 2 == 0:
            p = cand; break
    if p is None: continue
    n_odd = math.comb((S-p)//2 + p-1, p-1)         # nb de decoupages s impairs
    n_gen = math.comb(S-1, p-1)                     # nb de decoupages s quelconques
    n_m   = math.comb(n-1, p-1)                     # nb de decoupages m
    for mode, s_count, s_gen, s_rand in [("STRATE", n_odd, comps_odd, rand_comp_odd),
                                         ("GENERAL", n_gen, comps_positive, lambda S,p: rand_comp_positive(S,p))]:
        total = n_m * s_count
        infu, cycles, gcd_gt1, maxg, seen = 1.0, 0, 0, 1, 0
        if total <= CAP:                            # ENUMERATION COMPLETE
            for ms in comps_positive(n, p):
                for ss in s_gen(S, p):
                    r = R0(ms, ss); mres = r % q
                    d = min(mres, q-mres)/q
                    g = math.gcd(q, r)
                    infu = min(infu, d); cycles += (mres == 0)
                    gcd_gt1 += (g > 1); maxg = max(maxg, g); seen += 1
            tag = f"{seen} (enum)"
        else:                                       # ECHANTILLON dense
            N = 60000
            for _ in range(N):
                ms = rand_comp_positive(n, p); ss = s_rand(S, p)
                if ss is None: continue
                r = R0(ms, ss); mres = r % q
                d = min(mres, q-mres)/q; g = math.gcd(q, r)
                infu = min(infu, d); cycles += (mres == 0)
                gcd_gt1 += (g > 1); maxg = max(maxg, g); seen += 1
            tag = f"{seen} (ech.)"
        print(f"{n:>4} {p:>3} {q.bit_length():>8} {mode:>10} {tag:>10} {cycles:>12} {infu:>12.6f} {100*gcd_gt1/max(seen,1):>7.1f}% {maxg:>10}")

print("\n=== LECTURE ===")
print("* cycles(u=0) : 0 partout attendu (sinon on aurait trouve un cycle non trivial !).")
print("* inf u : si la STRATE reste NETTEMENT au-dessus du GENERAL (frole moins bien) => indice de RIGIDITE.")
print("  si strate ~ general (meme inf, ~0 aux grands q par densite d'echantillon) => la fissure n'aide pas seule.")
print("* gcd>1 / max gcd : signature multiplicative propre a la strate (obstruction de type L-A2) ?")
raise SystemExit(0)
