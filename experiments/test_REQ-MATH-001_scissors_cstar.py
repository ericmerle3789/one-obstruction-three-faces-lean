#!/usr/bin/env python3
# test_REQ-MATH-001_scissors_cstar.py — ARES Regles 1/5 (zero calcul mental, sandbox execute)
#
# QUESTION : la chaine Product Bound  m <= (k^{c+1}+k)/3  (papier Merle §5.2)
# peut-elle UN JOUR fermer la fenetre [k <= K_Hercher] avec une verification type Barina X0,
# quel que soit le progres diophantien sur l'exposant effectif c ?
#
# SOURCES LOCALES (Regle 2 — corpus papier Merle, collatz-conditional-cycles/paper/v2):
#   X0  = 2075 * 2^60      (Barina 2025, §6.1 table)
#   K_H = 1.375e11         (Hercher 2023 Cor. 29, §6.1 ; K coincide avec k du papier)
#   chaine m <= (k^{c+1}+k)/3 : §5.2 "Numerical corroboration"
# CANARIS : retrouver k_max(c=6)=1322 et k_max(c=5.125)=3693 (valeurs documentees §5.2).
from mpmath import mp, mpf, ln
mp.dps = 60

# DEUX seuils rapportes :
#   X0_paper  = 2^71 : calibration des valeurs documentees 1322/3693 (papier §5.2)
#   X0_barina = 2075*2^60 = 2^71.019 : la verification Barina exacte (§6.1)
X0_paper  = mpf(2)**71
X0_barina = mpf(2075) * mpf(2)**60
X0 = X0_paper          # canaris calibres papier ; c* recalcule avec les deux ensuite
KH = mpf('1.375e11')

def kmax(c):
    """plus grand k entier avec (k^{c+1}+k)/3 < X0 (bisection, monotone)."""
    lo, hi = 1, 10**40
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if (mpf(mid)**(c+1) + mid)/3 < X0:
            lo = mid
        else:
            hi = mid - 1
    return lo

print("=== CANARIS (valeurs documentees papier Merle §5.2) ===")
k6 = kmax(mpf(6));      print(f"c=6.000  -> k_max = {k6}   (attendu 1322)")
k5 = kmax(mpf('5.125')); print(f"c=5.125  -> k_max = {k5}   (attendu 3693)")
canary_ok = (k6 == 1322 and k5 == 3693)
print(f"CANARIS: {'PASS' if canary_ok else 'FAIL'}")

print("\n=== BALAYAGE : k_max(c) pour c decroissant ===")
for c in ['5.117', '4', '3', '2.5', '2']:
    print(f"c={c:>6} -> k_max = {kmax(mpf(c))}")

print("\n=== c* : exposant qui serait NECESSAIRE pour fermer la fenetre actuelle ===")
# (KH^{c*+1} + KH)/3 = X0  =>  c* = ln(3*X0 - KH)/ln(KH) - 1
cstar = ln(3*X0_paper - KH)/ln(KH) - 1
cstar_b = ln(3*X0_barina - KH)/ln(KH) - 1
print(f"c* (X0=2^71)       = {cstar}")
print(f"c* (X0=2075*2^60)  = {cstar_b}")
print(f"c* < 2 ? {cstar < 2} / {cstar_b < 2}")
print("Rappel (Dirichlet, approximation rationnelle) : tout irrationnel a une infinite")
print("d'approximations |xi - p/q| < 1/q^2, donc AUCUNE mesure d'irrationalite effective")
print("c < 2 n'existe pour aucun irrationnel. c* < 2 => chaine INFERMABLE meme au 'reve'.")

print("\n=== Deficit au 'reve diophantien' c = 2 (mesure optimale possible) ===")
k2 = kmax(mpf(2))
print(f"k_max(c=2) = {k2}  vs  K_Hercher = {KH}")
print(f"facteur manquant sur k : {KH/mpf(k2)}")
X0req = (KH**3 + KH)/3
print(f"X0 requis pour fermer a c=2 : 2^{ln(X0req)/ln(2)}  (Barina actuel : 2^{ln(X0)/ln(2)})")
print(f"facteur de calcul manquant : 2^{(ln(X0req)-ln(X0))/ln(2)}")

print(f"\nEXIT-CRITERION: canaris {'PASS' if canary_ok else 'FAIL'}")
raise SystemExit(0 if canary_ok else 1)
