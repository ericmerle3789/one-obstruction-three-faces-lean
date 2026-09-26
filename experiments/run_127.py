#!/usr/bin/env python3
# =============================================================================================
# run_127 — THE CORRECTED run_048 ("BRECHE-048 corrige"), RECOVERED. Header added 2026-09-26; nothing
# below the rule is changed: it is byte-for-byte the lab file D010_run048_corrige_recupere.py
# (sha256 73a64dd8231af269...), i.e. that file's own three-line recovery note, then the recovered code.
#
# What it is. On 2026-08-05 at 20:33:56Z, 44 s after writing run_048.py (the version whose canary C3
# fires), the working session ran a corrected version of it from standard input (`python3 - <<'PY'`).
# That code was never saved as a file; its output was archived as OUT_BRECHE-048.txt and fingerprinted
# the same day (EMPREINTES.txt l.102: fbcd923987a75419). The code was recovered verbatim from the
# session record on 2026-09-25. Re-run, its output is byte-identical to the archive and to that
# fingerprint (see run_127_output.txt; sha256 fbcd923987a75419...).
#
# Scope, corrected (round 17 §1): the bounded search closes simple cycles of length L <= 11
# (a path is extended only while len(ch) < 11), not <= 12; within that bound it is exhaustive
# (run_128). The k = 6 rows undercount by one: the key "sorted vertex set" merges two distinct
# non-realised faulty cycles (run_129). The P5 "hors connus" entries -10 and -136 are the even members
# of the known cycles {-5,-7,-10} and {-17,...,-136}; the 'connus' list held odd members only.
# Round-14 retraction of this figure: corrected in rounds/R17-merle.md §1 of the shared repository.
# =============================================================================================
# D010 — BRECHE-048 CORRIGE, recupere le 2026-09-25 depuis le transcript de la session 'Recherche Pilier'
# (commande du 2026-08-05T20:33:56Z : code execute sur l'entree standard, jamais enregistre comme fichier ;
# sa sortie a ete archivee dans Collatz-LAB-LOCAL/breche/resultats/OUT_BRECHE-048.txt). Aucune ligne modifiee ci-dessous.
# BRECHE-048 (corrige) — L'OBSTRUCTION EST-ELLE REELLE, OU UN FANTOME ?
#
# BUG ATTRAPE PAR LE CANARI C3 : je composais le mot A L'ENVERS, ce qui donne la valeur en un
# AUTRE point du cycle. Le mot (montee, descente) doit donner x=1 ; il donnait 2 (l'autre
# element du cycle {1,2}). CORRECTIF : composition FORWARD, y -> a*y + c accumule dans l'ordre.
from math import log2
from fractions import Fraction

def rationnel(bits, p):
    """x tel que le mot ramene x sur lui-meme : x = a x + c, donc x = c/(1-a)"""
    a = Fraction(1); c = Fraction(0)
    for b in bits:                       # ORDRE DU MOT, pas l'inverse
        if b: a, c = a*p/2, (c*p+1)/2
        else: a, c = a/2, c/2
    if a == 1: return None
    return c/(1-a)

def graphe(k, p):
    M = 1 << k; ar=[]
    for r in range(2*M):
        u = r % M
        if r % 2 == 1: ar.append((u, ((p*r+1)//2) % M, 1))
        else:          ar.append((u, (r//2) % M, 0))
    return M, ar

def cycles_fautifs(k, p, Lmax=11):
    M, ar = graphe(k, p)
    succ = {}
    for u,v,b in ar: succ.setdefault(u, []).append((v,b))
    seuil = 1/log2(p); trouves = {}
    for start in range(M):
        pile = [(start, [start], [])]; n = 0
        while pile and n < 3000:
            u, ch, bits = pile.pop(); n += 1
            for v, b in succ.get(u, []):
                if v == start:
                    L = len(ch); j = sum(bits)+b
                    if j/L > seuil:
                        trouves.setdefault(tuple(sorted(ch)), (ch, bits+[b], L, j))
                elif v not in ch and len(ch) < Lmax:
                    pile.append((v, ch+[v], bits+[b]))
        if len(trouves) > 600: break
    return trouves, seuil

print("="*94); print("CANARIS (apres correctif)"); print("="*94)
c1 = rationnel([1], 3) == Fraction(-1)
c2 = rationnel([1], 5) == Fraction(-1,3)
c3 = rationnel([1,0], 3) == Fraction(1)                     # cycle {1,2} : x=1
c4 = rationnel([1,0,1,0,0,1,0,0,1,0,0], 3) is not None      # mot de -17 : 7 montees / 11 pas
c5 = rationnel([1], 7) == Fraction(-1,5)
for nom, ok, v in (("C1 boucle p=3 -> -1", c1, rationnel([1],3)),
                   ("C2 boucle p=5 -> -1/3", c2, rationnel([1],5)),
                   ("C3 (montee,descente) -> 1", c3, rationnel([1,0],3)),
                   ("C4 mot long calculable", c4, rationnel([1,0,1,0,0,1,0,0,1,0,0],3)),
                   ("C5 boucle p=7 -> -1/5", c5, rationnel([1],7))):
    print(f"  {nom:30s} : {'PASS' if ok else 'FAIL'}   {v}")
assert c1 and c2 and c3 and c4 and c5, "canaris en echec"

print("\n" + "="*94)
print("P1/P2 — LA BOUCLE DU §95 SE REALISE-T-ELLE EN ENTIER ?")
print("="*94)
print(f"  {'p':>4} {'x = 1/(2-p)':>14} {'entier ?':>12} {'realisation':>30}")
for p in (3,5,7,9,11,13):
    x = rationnel([1], p); est = (x.denominator == 1)
    real = "cycle negatif trivial {-1}" if (est and p==3) else ("*** FANTOME ***" if not est else "?")
    print(f"  {p:>4} {str(x):>14} {('OUI' if est else 'non'):>12} {real:>30}")

print("\n" + "="*94)
print("P3/P4 *** LE TEST *** COMBIEN DE CYCLES FAUTIFS SONT DES FANTOMES ?")
print("="*94)
print(f"  {'p':>4} {'k':>4} {'cycles fautifs':>16} {'realises en entiers':>21} {'part fantome':>14}")
REELS = {}
for p in (3, 5, 7):
    for k in (6, 8, 10):
        tr, s = cycles_fautifs(k, p)
        reels = []
        for cle,(ch,bits,L,j) in tr.items():
            x = rationnel(bits, p)
            if x is not None and x.denominator == 1: reels.append(int(x))
        REELS[(p,k)] = sorted(set(reels))
        n = len(tr)
        print(f"  {p:>4} {k:>4} {n:>16} {len(set(reels)):>21} {(n-len(set(reels)))/max(n,1):>13.1%}")

print("\n" + "="*94)
print("P5 — CONTROLE : LES ENTIERS TROUVES SONT-ILS LES CYCLES CONNUS ?")
print("="*94)
connus3 = {1, -1, -5, -7, -17, -25, -37, -55, -41, -61, -91}
for (p,k), R in sorted(REELS.items()):
    if p == 3:
        inc = [v for v in R if v not in connus3]
        print(f"  p=3 k={k:>3} : {R}")
        print(f"           hors connus : {inc if inc else 'AUCUN'}")
print()
for (p,k), R in sorted(REELS.items()):
    if p != 3 and k == 10:
        print(f"  p={p} k={k} : entiers obtenus {R[:12]}")

print("\n" + "="*94)
print("LE POINT")
print("="*94)
print("  Le graphe des restes contient des cycles SANS REALISATION ENTIERE. La methode du §80")
print("  ne peut pas les distinguer des vrais : elle voit un obstacle la ou il n'y a personne.")
print("  *** C'est pourquoi aucune fonction de Lyapunov modulo 2^k ne peut exister — non pas")
print("  parce que Collatz est faux, mais parce que Z/2^k a PLUS de cycles que Z. ***")
