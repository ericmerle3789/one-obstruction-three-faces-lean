#!/usr/bin/env python3
# =============================================================================================
# run_129 — THE KEY-MERGE CHECK for run_127 (lab file S1_2_fusion_cle_sommets.py, sha256
# 2c66ca42f25abadb..., unchanged below the rule; header added 2026-09-26). run_127 keys each cycle by
# its SORTED VERTEX SET. Two distinct cycles with the same windows in a different cyclic order collide.
# F1/F4: among faulty cycles with L <= 11 the only collision is at k = 6: 01011101111 / 01011110111
# (L = 11, j = 8), neither realised, so the k = 6 rows of run_127 are one short (64/217/266, not
# 63/216/265). F2/F3: counting all simple cycles, k = 6 has 2 collisions at L = 11 -- the second pair,
# 00001000101 / 00001010001 (j = 3), was named by the lab's referee (RT-1); it is faulty for no p <= 7
# and changes no row. No collision for L <= k (proved), none at k = 8 before L = 14, none at k = 10
# before L = 17: the (7, 8) figure 330 is exact.
# =============================================================================================
# S1_2 — fusions de la cle « ensemble trie des sommets » (D010) dans G(p,k) ~ de Bruijn B(2,k). A2 Mots, S1, 2026-09-25.
# Independant de S1_1 (code recopie de mes propres fonctions, pas de D010). Arithmetique exacte. Sortie deterministe.
from fractions import Fraction
import sys

def T(p, x): return (p * x + 1) // 2 if x % 2 else x // 2
def numer(w, p):
    N = 0
    for i, b in enumerate(w):
        if b: N = p * N + (1 << i)
    return N
def lyndon_words(n):
    res = []; w = [-1]
    while w:
        w[-1] += 1; m = len(w)
        if m == n: res.append(tuple(w))
        while len(w) < n: w.append(w[len(w) - m])
        while w and w[-1] == 1: w.pop()
    return res
def windows(w, k):
    L = len(w); ww = list(w) * ((k + L - 1) // L + 1)
    return [tuple(ww[i:i + k]) for i in range(L)]
def pref(p, u, k):
    out = []; x = u
    for _ in range(k): out.append(x & 1); x = T(p, x)
    return tuple(out)

# canaris a la main
c = [("Lyndon(4) = 0001,0011,0111", lyndon_words(4) == [(0,0,0,1),(0,0,1,1),(0,1,1,1)]),
     ("fenetres('01', k=3) = 010,101", windows((0,1), 3) == [(0,1,0),(1,0,1)]),
     ("x_w('10',p=5) = -1", Fraction(numer((1,0),5), 4-5) == -1)]
for n, ok in c: print(f"  canari {n:32s} : {'PASS' if ok else 'FAIL'}")
if not all(ok for _, ok in c): sys.exit("canari en echec")

LMAX = 22
LYN = {L: lyndon_words(L) for L in range(1, LMAX + 1)}
print("\nF1/F4 — paires fusionnees par la cle 'ensemble des sommets', fautifs, L <= 11")
for p in (3, 5, 7):
    for k in (6, 8, 10):
        M = 1 << k; inv = {pref(p, u, k): u for u in range(M)}
        keys = {}
        for L in range(1, 12):
            for w in LYN[L]:
                W = windows(w, k)
                if len(set(W)) == L and p ** sum(w) > (1 << L):
                    keys.setdefault(tuple(sorted(inv[x] for x in W)), []).append(w)
        for key, ws in keys.items():
            if len(ws) > 1:
                desc = []
                for w in ws:
                    L = len(w); j = sum(w); x = Fraction(numer(w, p), (1 << L) - p ** j)
                    desc.append(f"{''.join(map(str, w))} (L={L}, j={j}, x_w={x}, entier={x.denominator == 1})")
                print(f"  p={p} k={k:2d} : " + "  |  ".join(desc))
print("\nF2/F3 — nombre de fusions (tous cycles simples, fautifs ou non) par L ; la structure ne depend pas de p (p=3 utilise)")
for k in (6, 8, 10):
    M = 1 << k; inv = {pref(3, u, k): u for u in range(M)}
    row = []; first = None; nearL = 0
    for L in range(1, LMAX + 1):
        keys = {}
        for w in LYN[L]:
            W = windows(w, k)
            if len(set(W)) == L: keys.setdefault(frozenset(inv[x] for x in W), []).append(w)
        f = sum(len(v) - 1 for v in keys.values())
        if L <= k: nearL += f
        if f and first is None: first = L
        row.append(f"{L}:{f}")
    print(f"  k={k:2d} : fusions L<=k = {nearL} ; premiere L avec fusion = {first} ; par L : " + " ".join(row))
