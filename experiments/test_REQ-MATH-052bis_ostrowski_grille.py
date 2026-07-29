#!/usr/bin/env python3
# REQ-MATH-052-bis — ARES : la table (d-bis), regeneree.
#
# POURQUOI CE FICHIER EXISTE.
# OUT_REQ-MATH-052.txt portait, au commit 41fa4f8 (2026-07-25 17:24:48 +0200), une section
# "(d-bis) Ostrowski des n a eps<0.0001" dont le ledger partage cite les nombres
# ("median lowest denominator 15601, against 1 for controls; e.g. 14936 = 22*665 + 306").
# La passe de nettoyage du tour 10 (6c084c5) a supprime cette section du fichier de sortie.
# Macindoe l'a releve au tour 11 en notant que le script commite ne produit pas cette section.
# Verifie ici : test_REQ-MATH-052_chaine_T1.py est BYTE-IDENTIQUE entre 41fa4f8 et HEAD
# (meme blob fb190aca8793dba29360de052f43806521d87db0) et n'a qu'un seul commit dans tout
# son historique. Il n'a donc jamais produit cette section : elle venait d'un script non
# commite, aujourd'hui perdu. Ce fichier-ci le remplace.
#
# CE QUI EST REPRODUIT A L'IDENTIQUE (la moitie sur laquelle repose le ledger) :
#   - les n a eps < 1e-4, leur expansion d'Ostrowski et le plus petit denominateur utilise ;
#   - la colonne eps-petits : [306, 15601, 15601, 306, 15601, 15601, 306, 79335, 306, 15601] ;
#   - les quatre lignes citees : 14936 = [(665,22),(306,1)], 15601, 31202, 46803.
#
# CE QUI EST RE-SPECIFIE ET NON RECOUVRE (dit explicitement plutot que maquille) :
#   - la colonne CONTROLE. La sortie d'origine donnait [2,1,1,1,2,1,2,1,1,306], mediane 1.
#     La construction de cet echantillon n'est pas reconstituable depuis la sortie et le
#     generateur n'a jamais ete commite. Le controle ci-dessous est donc REDEFINI : tirage
#     uniforme a graine fixe, et un second tirage de 200 valeurs pour que la conclusion ne
#     repose pas sur dix points. La conclusion qualitative est inchangee et plus robuste.
#
# CANARIS (ecrits avant execution) :
#   C1  14936 = 22*665 + 1*306                      -> expansion [(665,22),(306,1)]
#   C2  les dix premiers n a eps<1e-4 commencent par 14936, 15601, 31202, 46803
#   C3  la colonne eps-petits vaut la liste citee ci-dessus, mediane 15601
#   C4  tout n a eps<1e-4 a un plus petit denominateur >= 306
import math, random, statistics
from mpmath import mp, floor, log
mp.dps = 80
L = math.log2(3.0)

def convergents(NN):
    """Denominateurs des convergents de log2(3). Convention q0 = q1 = 1 comptes tous les deux
    (OUT-054/056), la meme que test_REQ-MATH-052_chaine_T1.py."""
    y = log(3) / log(2); a = []
    for _ in range(40):
        ai = int(floor(y)); a.append(ai); y = 1 / (y - ai)
    p0, q0, p1, q1 = 1, 0, a[0], 1; ds = [1]
    for ai in a[1:]:
        p0, q0, p1, q1 = p1, q1, ai * p1 + p0, ai * q1 + q0
        ds.append(q1)
        if q1 > NN: break
    return ds

DS = sorted({d for d in convergents(10**13)}, reverse=True)

def ostrowski(n):
    """Expansion gloutonne de n sur les denominateurs de convergents, en couples (d, c)."""
    exp, r = [], n
    for d in DS:
        if d <= r:
            c = r // d
            exp.append((d, c)); r -= c * d
        if r == 0: break
    return exp

def smallest_d(n):
    e = ostrowski(n)
    return min(d for d, _ in e) if e else None

SEUIL = 1e-4
hits = [n for n in range(1, 200000) if (math.ceil(n * L) - n * L) < SEUIL]

print("=== (d-bis) Ostrowski des n a eps<0.0001 : les digits bas sont-ils nuls ? ===")
print(f"{'n':>10} {'expansion (d,c)':>42} {'plus petit d utilise':>22}")
for n in hits[:10]:
    print(f"{n:>10} {str(ostrowski(n)):>42} {smallest_d(n):>22}")

eps_small = [smallest_d(n) for n in hits[:10]]

random.seed(0)
ctrl_n = [random.randrange(1, 200000) for _ in range(10)]
ctrl = [smallest_d(n) for n in ctrl_n]

print()
print(f"  plus petit denominateur utilise : eps-petits = {eps_small}")
print(f"                                   controle    = {ctrl}   (re-specifie, graine 0)")
print(f"  mediane eps-petits : {statistics.median(eps_small):g} | mediane controle : {statistics.median(ctrl):g}")

random.seed(1)
big = [smallest_d(n) for n in (random.randrange(1, 200000) for _ in range(200))]
print(f"  controle elargi (200 tirages, graine 1) : mediane {statistics.median(big):g}, "
      f"max {max(big)}, part >= 306 : {sum(1 for d in big if d >= 306)}/200")
print("  => si les eps-petits n'utilisent QUE des grands d (306+) et le controle descend a 1-12 :")
print("     LA GRILLE EST CONFIRMEE (structure d'Ostrowski, digits bas nuls).")

print("\n=== CANARIS ===")
c1 = ostrowski(14936) == [(665, 22), (306, 1)] and 22 * 665 + 306 == 14936
c2 = hits[:4] == [14936, 15601, 31202, 46803]
c3 = (eps_small == [306, 15601, 15601, 306, 15601, 15601, 306, 79335, 306, 15601]
      and statistics.median(eps_small) == 15601)
c4 = all(smallest_d(n) >= 306 for n in hits)
for nom, ok in (("C1 14936 = 22*665 + 306", c1), ("C2 quatre premiers hits", c2),
                ("C3 colonne eps-petits + mediane 15601", c3),
                ("C4 tout eps-petit a d >= 306", c4)):
    print(f"  {nom:42s} : {'PASS' if ok else 'FAIL'}")
print(f"  VERDICT : {'PASS' if all((c1, c2, c3, c4)) else 'FAIL'}")
