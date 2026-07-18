#!/usr/bin/env python3
# test_REQ-MATH-004_scissors_race.py — ARES Regles 1/5
#
# LA COURSE DES CISEAUX :
#   k_min(X0) = borne INFERIEURE de longueur de cycle (mecanisme Crandall + convergents),
#               formule documentee papier Merle §6.1 : k > (3/2) min(q_j, 2 n0/(q_j+q_{j+1})) ;
#               on prend k_min(X0) = max_j (3/2) min(q_j, 2 X0/(q_j+q_{j+1})).
#   k_max(X0,c) = borne SUPERIEURE conditionnelle de la chaine Product Bound :
#               (k^{c+1}+k)/3 < X0  =>  k_max ~ (3 X0)^{1/(c+1)}.
# QUESTION : quand X0 (la verification computationnelle) monte, la fenetre
#            (k_max, k_min) se FERME-t-elle ou s'OUVRE-t-elle ?
# SANITY : a X0 = 2^71, k_min(Crandall brut) doit etre du meme ordre que
#          Hercher Cor.29 (1.375e11) — Hercher rafine Crandall, il doit faire mieux.
from mpmath import mp, mpf, log, floor
# dps=800 : necessaire pour 160 quotients partiels fiables (perte ~2*log10(q_k) digits) ;
# la v1 du script (90 quotients, dps=120) tronquait la liste => artefact alpha->0 a X0>=2^300.
mp.dps = 800
L = log(3)/log(2)

A = []; x = L
for i in range(160):
    a = int(floor(x)); A.append(a); x = 1/(x - a)
H = [0, 1]; Q = [1, 0]; qs = []
for a in A:
    H.append(a*H[-1] + H[-2]); Q.append(a*Q[-1] + Q[-2])
    qs.append(Q[-1])

def kmin(X0):
    best = mpf(0)
    for j in range(len(qs) - 1):
        v = mpf(3)/2 * min(mpf(qs[j]), 2*X0/(qs[j] + qs[j+1]))
        if v > best:
            best = v
    return best

def kmax(X0, c):
    return (3*X0)**(mpf(1)/(c+1))

print("=== SANITY (X0 = 2^71 ~ Barina) ===")
X71 = mpf(2)**71
print(f"k_min Crandall-brut = {float(kmin(X71)):.4g} ; Hercher (rafine) = 1.375e11 ; "
      f"meme ordre ? ratio = {float(mpf('1.375e11')/kmin(X71)):.2f}")

print("\n=== LA COURSE (c = 2 : reve diophantien ; c = 5.125 : Salikhov reel) ===")
print(f"{'X0':>7} | {'k_min':>11} | {'k_max c=2':>11} | {'k_max c=5.125':>13} | {'k_min/k_max(c=2)':>16}")
prev = None
for e in [71, 100, 150, 200, 300, 400]:
    X0 = mpf(2)**e
    a_ = kmin(X0); b2 = kmax(X0, mpf(2)); b5 = kmax(X0, mpf('5.125'))
    line = f"2^{e:<5} | {float(a_):11.4g} | {float(b2):11.4g} | {float(b5):13.4g} | {float(a_/b2):16.4g}"
    print(line)
    if prev is not None:
        alpha = (log(a_) - log(prev[0])) / (log(X0) - log(prev[1]))
        print(f"        pente locale alpha = dln(k_min)/dln(X0) = {float(alpha):.3f}  (attendu ~0.5)")
    prev = (a_, X0)

print("\nLECTURE : k_min croit ~ X0^(1/2) ; k_max croit au mieux ~ X0^(1/3) (c=2).")
print("La fenetre s'OUVRE quand la verification progresse. La tenaille classique perd la course.")
raise SystemExit(0)
