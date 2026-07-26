#!/usr/bin/env python3
# test_REQ-MATH-043_seuils_constante_prouvee.py — ARES
# ECRIT LE 2026-07-26, retroactivement : OUT_REQ-MATH-043.txt avait ete depose SANS son
# script (releve par Macindoe, audit round 10). Ce fichier reproduit la sortie deposee.
#
# OBJET : les seuils de L-A7 doivent citer LA CONSTANTE PROUVEE (1/13, DeficitLemma), pas
# la constante asymptotique c_gen. On rejoue la methode de REQ-MATH-035 (exhibition de C0 +
# croisements L1/L2) a l'exposant re-source 13.3 (Rhin 1987 via Simons-de Weger Lemme 12),
# sous LES DEUX constantes, et on mesure l'ecart.
#   borne(n) = -c*n + p*log2(n) + C0 ,  C0 EXHIBE = max_n (Rbest(n) + c*n - p*log2 n)
#   L1 "par echelle"   : plus petit n tel que borne(m) < 0 pour tout m >= n
#   L2 "queue cumulee" : plus petit n tel que somme_{m>n} 2^borne(m) < 1
#
# PREDICTIONS AVANT MESURE (= la sortie deposee, a reproduire au chiffre pres) :
#  P1 c_gen  : C0 = -14.949 , L1 = 1596 , L2 = 1661 , queue(n>600) = 3.863e+19
#  P2 1/13   : C0 = -14.954 , L1 = 1655 , L2 = 1722 , queue(n>600) = 1.096e+20
#  P3 la constante prouvee est ~3% sous c_gen ; l'effet sur les seuils reste modere (<5%).
import math
C_GEN = 0.0793186
C_LEAN = 1.0/13.0
P_EXP = 13.3                      # Rhin 1987, via Simons-de Weger Lemme 12
NMAX = 4000

def log2C(a, b):
    if b < 0 or b > a: return float('-inf')
    return (math.lgamma(a+1) - math.lgamma(b+1) - math.lgamma(a-b+1)) / math.log(2)
def log2_big(x):
    e = x.bit_length() - 53
    return (e + math.log2(x >> e)) if e > 0 else math.log2(x)

print("=== CANARI : les ancres exactes de REQ-MATH-035 ===")
q5 = (1 << 8) - 3**5; q7 = (1 << 12) - 3**7
ok = (q5 == 13 and q7 == 1909)
print(f"  n=5 K=8 q={q5} (att. 13) ; n=7 K=12 q={q7} (att. 1909) : {ok}")
if not ok: raise SystemExit(1)

# R_best exact par echelle (meilleure cellule nord) — identique a REQ-MATH-035
Rbest = {}
pow3 = 9
for n in range(2, NMAX+1):
    if n > 2: pow3 *= 3
    Smax = int(0.5849625*n) + 3
    best = -1e18
    for S in range(1, Smax+1):
        K = n + S; q = (1 << K) - pow3
        if q <= 0: continue
        R = log2C(n+S-2, n-1) - log2_big(q)
        if R > best: best = R
    if best > -1e17: Rbest[n] = best
print(f"  R_best calcule sur {len(Rbest)} echelles (n<=4000)")
print("CANARIS: PASS\n")

def analyse(c, p=P_EXP):
    C0 = max(Rbest[n] + c*n - p*math.log2(n) for n in Rbest)
    f = lambda n: -c*n + p*math.log2(n) + C0
    L1 = next((n for n in range(2, NMAX+1)
               if f(n) < 0 and all(f(m) < 0 for m in range(n, min(n+50, NMAX+1)))), None)
    L2 = next((n for n in range(2, NMAX+1)
               if sum(2.0**f(m) for m in range(n+1, NMAX+1) if f(m) > -300) < 1.0), None)
    tail600 = sum(2.0**f(m) for m in range(601, NMAX+1) if f(m) > -300)
    viol = sum(1 for n in Rbest if Rbest[n] > f(n) + 1e-9)
    return C0, L1, L2, tail600, viol

print(f"c_gen (asymptotique, non prouve en Lean) = {C_GEN:.7f}")
print(f"c prouve en Lean (1/13)                  = {C_LEAN:.7f}   (ecart {C_GEN-C_LEAN:.5f})")
print()
print(f"   {'constante':>13} {'C0 exhibe':>10} {'croisement/echelle':>19} {'queue<1':>9} {'queue n>600':>13}")
res = {}
for nom, c in (("c_gen", C_GEN), ("1/13 (prouve)", C_LEAN)):
    C0, L1, L2, t6, viol = analyse(c)
    res[nom] = (C0, L1, L2, t6, viol)
    print(f"   {nom:>13} {C0:>10.3f} {L1:>19d} {L2:>9d} {t6:>13.3e}")

print()
print("LECTURE : la constante prouvee (1/13) est ~3% plus faible que c_gen ; l'effet sur")
print("les seuils est modere. Les chiffres de L-A7 doivent citer LA CONSTANTE PROUVEE.")

print("\n=== CONTROLE DES PREDICTIONS (reproduction de OUT_REQ-MATH-043.txt) ===")
att = {"c_gen": (-14.949, 1596, 1661, 3.863e19), "1/13 (prouve)": (-14.954, 1655, 1722, 1.096e20)}
allok = True
for nom, (C0a, L1a, L2a, t6a) in att.items():
    C0, L1, L2, t6, viol = res[nom]
    c_ok = abs(C0 - C0a) < 5e-4; l1_ok = L1 == L1a; l2_ok = L2 == L2a
    t_ok = abs(t6/t6a - 1) < 2e-3
    allok &= c_ok and l1_ok and l2_ok and t_ok
    print(f"  {nom:>13} : C0 {C0:.3f} vs {C0a} {'OK' if c_ok else 'X'} | "
          f"L1 {L1} vs {L1a} {'OK' if l1_ok else 'X'} | L2 {L2} vs {L2a} {'OK' if l2_ok else 'X'} | "
          f"queue {t6:.3e} vs {t6a:.3e} {'OK' if t_ok else 'X'} | violations borne<exact : {viol}")
print(f"\nVERDICT : {'REPRODUCTION EXACTE DE LA SORTIE DEPOSEE' if allok else 'ECART — a examiner'}")
raise SystemExit(0 if allok else 1)
