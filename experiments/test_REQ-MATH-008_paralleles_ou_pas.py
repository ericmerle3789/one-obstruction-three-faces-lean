#!/usr/bin/env python3
# test_REQ-MATH-008_paralleles_ou_pas.py — ARES
# QUESTION (Eric) : les deux "tours" (puissances de 2 et de 3) sont-elles PARALLELES ?
# Test : la distance minimale (en echelle log2) entre une puissance de 2 et une puissance
#        de 3 est-elle CONSTANTE (=> paralleles) ou DECROIT-elle vers 0 (=> approche, pas
#        paralleles) ? Les meilleurs frolements sont aux convergents h_k/q_k de L=log2(3).
# CANARI : premiers frolements = (8 vs 9) puis (256 vs 243).
from mpmath import mp, mpf, log, floor
mp.dps = 80
L = log(3)/log(2)

# convergents de L
A = []; x = L
for _ in range(30):
    a = int(floor(x)); A.append(a); x = 1/(x - a)
H = [0, 1]; Q = [1, 0]; conv = []
for a in A:
    H.append(a*H[-1] + H[-2]); Q.append(a*Q[-1] + Q[-2])
    conv.append((H[-1], Q[-1]))

print(f"{'2^h':>8} {'3^q':>8} | {'ecart en log2 = |h - q*L|':>26} | {'strictement > 0 ?':>18}")
prev = None
rows = []
for (h, q) in conv[:12]:
    if q == 0: continue
    gap = abs(mpf(h) - mpf(q)*L)     # distance verticale sur l'echelle log2
    rows.append((h, q, gap))
    decreasing = "" if prev is None else ("  (v decroit)" if gap < prev else "  !! REMONTE")
    print(f"  2^{h:<5} 3^{q:<5} | {float(gap):26.12f} | {'oui' if gap>0 else 'NON=contact!':>18}{decreasing}")
    prev = gap

# canari
c8_9 = (rows[2][0] == 3 and rows[2][1] == 2)      # 2^3=8, 3^2=9
c256_243 = (rows[3][0] == 8 and rows[3][1] == 5)  # 2^8=256, 3^5=243
print(f"\nCANARI frolements (8 vs 9) et (256 vs 243) : {'PASS' if (c8_9 and c256_243) else 'FAIL'}")

# le point : monotone decroissante, jamais nulle
gaps = [float(g) for (_,_,g) in rows]
strict_decr = all(gaps[i] < gaps[i-1] for i in range(1, len(gaps)))
never_zero = all(g > 0 for g in gaps)
print(f"distance minimale STRICTEMENT decroissante ? {strict_decr}")
print(f"distance minimale JAMAIS nulle (jamais 2^h = 3^q) ? {never_zero}")
print(f"gap au 12e frolement = {gaps[-1]:.2e}  (tend vers 0)")
print()
print("VERDICT : les tours ne sont PAS paralleles (distance non constante, -> 0).")
print("Elles s'approchent arbitrairement pres SANS jamais se toucher : approche asymptotique,")
print("comme 1/n -> 0. La non-rencontre (irrationalite de L) est ELEMENTAIRE et deja acquise ;")
print("le vrai objet a demontrer est la VITESSE d'approche (mesure d'irrationalite = delta8),")
print("car un cycle a besoin d'un frolement 'assez bon', pas d'un contact.")
raise SystemExit(0 if (c8_9 and c256_243 and strict_decr and never_zero) else 1)
