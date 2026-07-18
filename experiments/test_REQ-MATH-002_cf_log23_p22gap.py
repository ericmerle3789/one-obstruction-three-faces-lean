#!/usr/bin/env python3
# test_REQ-MATH-002_cf_log23_p22gap.py — ARES Regles 1/5
#
# OBJET :
#  (a) fraction continue de L = log2(3), quotients partiels + convergents,
#      avec CERTIFICATION EXACTE en entiers (signe de h - qL == signe de 2^h - 3^q) ;
#  (b) la matiere premiere des staircases : les n tels que delta(n) := ceil(nL) - nL
#      est minuscule (q = 2^K - 3^n relativement petit => gamma grand) ;
#      SOURCE DE VERITE = FORCE BRUTE EXACTE via bit_length (aucun flottant pour K) ;
#  (c) le "trou" de p = 22 : fenetres n ~ L^p pour p = 19..25, meilleurs delta disponibles.
#
# Claims externes a recouper (repo Macindoe, cycles.md 12.8.6.1) :
#   41 et 306 denominateurs de convergents ; 94 = 53+41 et 971 = 665+306 semiconvergents.
from mpmath import mp, mpf, log, floor
mp.dps = 120
L = log(3)/log(2)

# (a) CF + convergents
A = []
x = L
for i in range(40):
    a = int(floor(x)); A.append(a); x = 1/(x - a)
H = [0, 1]; Q = [1, 0]
conv = []
for a in A:
    H.append(a*H[-1] + H[-2]); Q.append(a*Q[-1] + Q[-2])
    conv.append((H[-1], Q[-1]))

print("=== (a) CF de log2(3) ===")
print("quotients partiels a_k:", A[:24])
print("denominateurs q_k     :", [q for _, q in conv[:20]])
# certification entiere limitee a q <= 10^6 (au-dela, 3^q devient gigantesque : inutile ici,
# notre analyse force-brute s'arrete a n <= 140000)
certif = [(h, q) for (h, q) in conv if q <= 10**6]
signs = []
for (h, q) in certif:
    s = 1 if (1 << h) > 3**q else -1   # comparaison ENTIERE exacte 2^h vs 3^q
    signs.append(s)
alt_ok = all(signs[i] != signs[i-1] for i in range(1, len(signs)))
print(f"alternance des signes certifiee en entiers exacts (sur {len(certif)} convergents, q<=1e6):", alt_ok)
print("cote '+' (2^h > 3^q, i.e. h - qL > 0, i.e. {qL} proche de 1^-):",
      [q for i, (h, q) in enumerate(certif) if signs[i] > 0])

qd = [q for _, q in conv]
print("\nRecoupement claims Macindoe: 41 conv?", 41 in qd, "| 306 conv?", 306 in qd,
      "| 53 conv?", 53 in qd, "| 665 conv?", 665 in qd)

# (b) records exacts de delta(n) par force brute, n <= 140000 (couvre p<=25)
NMAX = 140000
print(f"\n=== (b) n 'utiles au staircase' (delta petit), force brute exacte n<={NMAX} ===")
mp.dps = 40
L60 = log(3)/log(2)
thr = mpf('0.05')
cands = []
p3 = 1
for n in range(1, NMAX + 1):
    p3 *= 3
    K = p3.bit_length()          # K = ceil(n*L) EXACT (3^n jamais puissance de 2)
    delta = K - n*L60            # in (0,1) ; erreur mpf ~ 1e-38, negligeable
    if delta < thr:
        gam = -log(1 - mpf(2)**(-delta))/log(2)
        cands.append((n, float(delta), float(gam)))
print(f"{len(cands)} valeurs n<={NMAX} avec delta < 0.05 :")
for n, d, g in cands:
    print(f"  n={n:6d}  delta={d:.6f}  gamma_plafond={g:6.2f}")

# (c) fenetres par periode p : n ~ L^p (fenetre multiplicative [L^{p-0.6}, L^{p+0.6}])
print("\n=== (c) meilleurs delta disponibles par fenetre de periode p ===")
for p in range(19, 26):
    lo = float(L60**(p - mpf('0.6'))); hi = float(L60**(p + mpf('0.6')))
    inwin = [c for c in cands if lo <= c[0] <= hi]
    inwin.sort(key=lambda c: c[1])
    top = [(c[0], round(c[1], 5), round(c[2], 2)) for c in inwin[:3]]
    print(f"p={p:2d}  fenetre n=[{lo:7.0f},{hi:7.0f}]  cible L^p={float(L60**p):8.0f}  "
          f"meilleurs (n, delta, gamma): {top if top else 'AUCUN CANDIDAT delta<0.05'}")

print("\nEXIT-CRITERION: alternance certifiee =", alt_ok)
raise SystemExit(0 if alt_ok else 1)
