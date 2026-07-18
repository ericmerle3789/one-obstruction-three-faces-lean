#!/usr/bin/env python3
# test_REQ-MATH-009_transfer_spectrum.py — ARES session 4
# L'OPERATEUR DE TRANSFERT AU NIVEAU DES CLASSES (section AEH du paper Macindoe, §6) :
#  1. Implementation independante (two-key) de la carte reduite F (Definition 2.1 du paper).
#     CANARIS : F(1,1)=(1,1) ; le bloc de x=7 : F(R(7)) == R(13) avec exit 13 (calcul manuel
#     de la trajectoire 7->11->17->13 fait par la definition, verifie ici par la machine).
#  2. Orbites reelles (graines ~2^50, seed fixe, cut anti-bottom-regime) -> matrice de
#     transfert empirique sur les 8 classes (omega mod 8, d mod 2) -> SPECTRE + trou spectral.
#  3. Two-key des DEUX valeurs exactes publiees par Macindoe (§6) :
#     de (1, odd) : d_next = 1 TOUJOURS ; de (5, odd) : P(d_next pair) = 2/3.
#  4. P(s=j) = 2^{-j} ; derive par step ~ log2(3/4) = -0.415 bits.
#  5. RED TEAM integre : sensibilite au cut (2^20 vs 2^30) ; N et erreurs binomiales ;
#     ET l'aveu structurel : tout ceci concerne les orbites GENERIQUES (AEH) — aucune
#     consequence directe pour les cycles (gap distributionnel -> ponctuel).
import random, math

def v2(x): return (x & -x).bit_length() - 1
def v3(x):
    a = 0
    while x % 3 == 0: x //= 3; a += 1
    return a

def R(x):  # projection : x impair -> etat (omega, d)
    u = x + 1; m = v2(u); u >>= m
    a = v3(u)
    return (u // 3**a, m + a)

def F(w, d):  # carte reduite (Def 2.1) ; retourne (etat suivant, exit value, s)
    A = 3**d * w - 1
    s = v2(A)
    xexit = A >> s
    C = A + (1 << s)
    sig = v2(C); C >>= sig
    a = v3(C)
    return (C // 3**a, (sig - s) + a), xexit, s, a

# --- CANARIS ---
st, xe, _, _ = F(1, 1)
c1 = (st == (1, 1) and xe == 1)
st7 = R(7)                      # 7+1=8=2^3 -> (1,3)
stn, xe7, s7, _ = F(*st7)
c2 = (st7 == (1, 3) and xe7 == 13 and stn == R(13))   # bloc de 7 : exit 13
print(f"CANARI F(1,1)=(1,1) : {c1} | bloc de 7 -> exit 13, etat R(13) : {c2}")
if not (c1 and c2): raise SystemExit(1)

# --- ORBITES ---
# drift par BLOC normalise par E[d] mesure (chaque bloc contient d steps de l'odd map T,
# au sens : d = m + a et le bloc consomme m steps ; on normalise par sum(d) — MAJORANT de
# sum(m), donc la derive par step est un majorant en valeur absolue ; note honnete en sortie)
random.seed(20260717)
def run2(cut_bits, n_seeds=3000, seed_bits=50, max_blocks=5000):
    cut = 1 << cut_bits
    cls = lambda w, d: (w % 8, d % 2)
    trans = {}; sdist = {}; c_1odd = [0, 0]; c_5odd = [0, 0]
    sum_logblock = 0.0; sum_m = 0; nblocks = 0
    for _ in range(n_seeds):
        x = random.getrandbits(seed_bits) | 1
        u = x + 1; mm = v2(u); a_in = v3(u >> mm)   # absorption entrante du 1er etat
        st = R(x)
        prev_exit = None
        for _ in range(max_blocks):
            (w, d) = st
            nxt, xexit, s, a_out = F(w, d)
            if xexit < (1 << 10): break
            if xexit >= cut:
                a = cls(w, d); b = cls(*nxt)
                trans[(a, b)] = trans.get((a, b), 0) + 1
                sdist[s] = sdist.get(s, 0) + 1
                if a == (1, 1): c_1odd[0] += 1; c_1odd[1] += (nxt[1] == 1)
                if a == (5, 1): c_5odd[0] += 1; c_5odd[1] += (nxt[1] % 2 == 0)
                if prev_exit:
                    sum_logblock += math.log2(xexit / prev_exit); sum_m += (d - a_in); nblocks += 1
            prev_exit = xexit
            a_in = a_out
            st = nxt
    return trans, sdist, c_1odd, c_5odd, sum_logblock, sum_m, nblocks

CLS = [(w, p) for w in (1, 3, 5, 7) for p in (0, 1)]
def analyse(cut_bits):
    trans, sdist, c1o, c5o, slb, sm, nb = run2(cut_bits)
    N = sum(trans.values())
    # matrice
    M = [[0.0]*8 for _ in range(8)]
    for i, a in enumerate(CLS):
        row = sum(v for (x, y), v in trans.items() if x == a)
        for j, b in enumerate(CLS):
            M[i][j] = trans.get((a, b), 0) / row if row else 0.0
    # spectre
    import numpy as np
    ev = sorted(np.abs(np.linalg.eigvals(np.array(M))), reverse=True)
    gap = 1 - ev[1]
    # stats
    p_d1 = c1o[1]/c1o[0] if c1o[0] else float('nan')
    p_ev = c5o[1]/c5o[0] if c5o[0] else float('nan')
    err5 = 1.96*math.sqrt(p_ev*(1-p_ev)/c5o[0]) if c5o[0] else 0
    drift_per_step = slb/sm if sm else float('nan')
    print(f"\n--- cut = 2^{cut_bits} : N = {N} transitions ---")
    print(f"|lambda| tries : {[round(float(x),4) for x in ev[:4]]}  => TROU SPECTRAL 1-|l2| = {gap:.4f}")
    print(f"(1,odd) -> d_next=1 : {c1o[1]}/{c1o[0]} = {p_d1:.4f}  (Macindoe exact : 1.0)")
    print(f"(5,odd) -> d_next pair : {p_ev:.4f} +- {err5:.4f}  (Macindoe exact : 2/3 = 0.6667)")
    ss = sum(sdist.values())
    obs = [sdist.get(j, 0)/ss for j in range(1, 6)]
    print(f"P(s=j) obs : {[round(o,4) for o in obs]} vs theorie {[round(2.0**-j,4) for j in range(1,6)]}")
    print(f"derive par step T (normalisee par le vrai m) : {drift_per_step:.4f} bits (theorie log2(3/4) = {math.log2(3/4):.4f})")
    return gap, p_d1, p_ev

g1, pd1a, pev_a = analyse(20)
g2, pd1b, pev_b = analyse(30)   # RED TEAM : sensibilite au cut
stable = abs(g1 - g2) < 0.03 and pd1a == 1.0 and pd1b == 1.0 and abs(pev_a - 2/3) < 0.02 and abs(pev_b - 2/3) < 0.03
print(f"\nRED TEAM sensibilite : gap stable (|{g1:.4f}-{g2:.4f}|<0.03) et valeurs exactes tenues aux 2 cuts ? {stable}")
print("PORTEE (aveu structurel) : ceci mesure la face GENERIQUE (AEH). Un trou spectral ne dit")
print("RIEN des orbites exceptionnelles : les cycles vivent dans le gap distributionnel->ponctuel.")
raise SystemExit(0 if stable else 1)
