#!/usr/bin/env python3
# =============================================================================================
# run_128 — INDEPENDENT RE-ENUMERATION of the run_127 census (lab file S1_1_r01_graphe_restes.py,
# sha256 ec7167ac7358decf..., written 2026-09-25 without importing or copying run_127's code; it reads
# only run_127's OUTPUT, to compare the tables). Header added 2026-09-26.
#
# Object: the two-lift residue graph G(p,k) of the Terras map T_p on Z/2^k; it is the de Bruijn graph
# B(2,k) under u -> first k parity bits (Terras 1976 / Lagarias 1985, same proof for odd p), so its simple
# cycles are the primitive necklaces whose L cyclic k-bit windows are distinct. A cycle is "faulty" when
# p^j > 2^L and "realised" when x_w = N_w/(2^L - p^j) is an integer. Counts by Lyndon words (Duval/FKM),
# cross-checked against a canonical DFS for L <= 12; extension to L <= 22.
#
# ONE CHANGE from the lab file, and only one: its two lines
#     LAB = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
#     D010_OUT = os.path.join(LAB, "calculs", "directeur", "out", "D010_run048_corrige_recupere__run0015.txt")
# are replaced by the single line
#     D010_OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "run_127_output.txt")
# (run_127_output.txt is byte-identical to that lab output). The printed output is unchanged
# (sha256 0ab949d78cdb6fe9...). Runtime about 35 s. Its P4 prediction is printed TOMBEE on purpose:
# it predicted no key merge, and the k = 6 merge is the finding (see run_129).
# =============================================================================================
# S1_1 — R01 : graphe des restes a deux relevements (carte de Terras T_p), recensement independant.
# Agent A2 « Mots », LABO-COLLATZ, seance 1 (2026-09-25).
# Ecrit sans importer ni copier D010 : seule la SORTIE archivee de D010 (id=15) est relue, pour comparer les tableaux.
# Arithmetique exacte (int, Fraction) pour toute decision d'integralite / de divisibilite. Sortie deterministe.
from fractions import Fraction
from math import log2
import re, sys, os

D010_OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "run_127_output.txt")

def T(p, x):
    return (p * x + 1) // 2 if x % 2 else x // 2      # exact : p*x+1 pair quand x impair

def numer(word, p):
    """N_w tel que T^L(x) = (p^j x + N_w)/2^L le long du mot ; x_w = N_w / (2^L - p^j)."""
    N = 0
    for i, b in enumerate(word):
        if b: N = p * N + (1 << i)
    return N

def xw(word, p):
    L = len(word); j = sum(word); d = (1 << L) - p ** j
    return Fraction(numer(word, p), d)

def succ_list(p, k):
    M = 1 << k
    return [[T(p, u) % M, T(p, u + M) % M] for u in range(M)]   # ordre des relevements r = u puis r = u + M

def pref(p, u, k):
    """k premiers bits de parite de l'orbite de u (u >= 0) : depend seulement de u mod 2^k."""
    out = []; x = u
    for _ in range(k):
        out.append(x & 1); x = T(p, x)
    return tuple(out)

# ---------------------------------------------------------------- CANARIS (calcules a la main)
print("=" * 90); print("CANARIS"); print("=" * 90)
can = [
    ("T_3(-5) = -7",                         T(3, -5) == -7),
    ("T_7(1) = 4",                           T(7, 1) == 4),
    ("x_w('1', p=3) = -1",                   xw((1,), 3) == -1),
    ("x_w('10', p=3) = 1  (cycle {1,2})",    xw((1, 0), 3) == 1),
    ("x_w('110', p=3) = -5 (cycle -5,-7,-10)", xw((1, 1, 0), 3) == -5),
    ("x_w('1', p=7) = -1/5",                 xw((1,), 7) == Fraction(-1, 5)),
    ("x_w('10', p=5) = -1 (cycle {-1,-2})",  xw((1, 0), 5) == -1),
    ("succ(1) dans G(3,3) = [2, 6]",         succ_list(3, 3)[1] == [2, 6]),
    ("pref(p=3, u=5, k=3) = (1,0,0)",        pref(3, 5, 3) == (1, 0, 0)),
]
for nom, ok in can: print(f"  {nom:42s} : {'PASS' if ok else 'FAIL'}")
if not all(ok for _, ok in can): sys.exit("canari en echec")

# ---------------------------------------------------------------- mots de Lyndon (algorithme de Duval / FKM)
def lyndon_words(n):
    """tous les mots de Lyndon binaires de longueur exactement n (ordre lexicographique)."""
    res = []; w = [-1]
    while w:
        w[-1] += 1
        m = len(w)
        if m == n: res.append(tuple(w))
        while len(w) < n: w.append(w[len(w) - m])
        while w and w[-1] == 1: w.pop()
    return res

LYN_CAN = [len(lyndon_words(n)) for n in range(1, 9)]
ok = LYN_CAN == [2, 1, 2, 3, 6, 9, 18, 30]
print(f"  {'nb Lyndon L=1..8 = 2,1,2,3,6,9,18,30':42s} : {'PASS' if ok else 'FAIL'} {LYN_CAN}")
if not ok: sys.exit("canari Lyndon en echec")

PS = (3, 5, 7); KS = (6, 8, 10); LMAX_EXT = 22

# ---------------------------------------------------------------- P3 : isomorphisme avec de Bruijn B(2,k)
print("\n" + "=" * 90); print("P3 — G(p,k) ~ de Bruijn B(2,k) par u -> k premiers bits de parite"); print("=" * 90)
INV = {}   # (p,k) -> dict mot_k -> u
p3_ok = True
for p in PS:
    for k in KS:
        M = 1 << k; S = succ_list(p, k)
        P = [pref(p, u, k) for u in range(M)]
        bij = len(set(P)) == M
        arcs = all(P[v][:k - 1] == P[u][1:] for u in range(M) for v in S[u])
        last = all({P[S[u][0]][k - 1], P[S[u][1]][k - 1]} == {0, 1} for u in range(M))
        bitpar = all(P[u][0] == (u & 1) for u in range(M))
        good = bij and arcs and last and bitpar
        p3_ok &= good
        INV[(p, k)] = {P[u]: u for u in range(M)}
        print(f"  p={p} k={k:2d} : bijection={bij} arcs_decalage={arcs} deux_bits_finals={last} bit=parite={bitpar}")
print(f"  P3 : {'TENUE' if p3_ok else 'TOMBEE'}")
# p-independance : les 3 graphes, transportes sur B(2,k), sont le meme graphe (celui de de Bruijn) ; on le constate aussi
for k in KS:
    same = all(INV[(3, k)].keys() == INV[(p, k)].keys() for p in PS)
    print(f"  k={k:2d} : memes etiquettes de sommets pour p=3,5,7 : {same}")

# ---------------------------------------------------------------- P2/P4 : reimplementation de l'exploration bornee de D010
print("\n" + "=" * 90); print("P2/P4 — exploration bornee (semantique lue dans D010, code reecrit)"); print("=" * 90)
def bounded(p, k, Lmax=11, cap=3000, stop=600):
    M = 1 << k; S = succ_list(p, k); seuil = 1 / log2(p)
    found = {}; maxpops = 0; capbit = 0; Lseen = 0; stops = 0; float_vs_exact = 0
    for start in range(M):
        pile = [(start, [start], [])]; n = 0
        while pile and n < cap:
            u, ch, bits = pile.pop(); n += 1
            for v in S[u]:
                b = u & 1
                if v == start:
                    L = len(ch); j = sum(bits) + b
                    if (j / L > seuil) != (p ** j > (1 << L)): float_vs_exact += 1
                    if j / L > seuil:
                        found.setdefault(tuple(sorted(ch)), (list(ch), bits + [b], L, j))
                        Lseen = max(Lseen, L)
                elif v not in ch and len(ch) < Lmax:
                    pile.append((v, ch + [v], bits + [b]))
        if pile: capbit += 1
        maxpops = max(maxpops, n)
        if len(found) > stop: stops = 1; break
    reels = set()
    for ch, bits, L, j in found.values():
        x = xw(tuple(bits), p)
        if x.denominator == 1: reels.add(int(x))
    # nombre de cycles DISTINCTS (a rotation pres) derriere les cles « ensemble de sommets »
    return found, reels, dict(maxpops=maxpops, capbit=capbit, Lseen=Lseen, stops=stops, fve=float_vs_exact)

d010 = {}
with open(D010_OUT) as f:
    for line in f:
        m = re.match(r"^\s+([357])\s+(6|8|10)\s+(\d+)\s+(\d+)\s+[\d.]+%\s*$", line)
        if m: d010[(int(m[1]), int(m[2]))] = (int(m[3]), int(m[4]))
print(f"  lignes lues dans la sortie D010 (id=15) : {len(d010)}")
print(f"  {'p':>2} {'k':>3} | {'moi fautifs':>11} {'moi reels':>9} | {'D010':>11} | {'max depil.':>10} {'plafond mord':>12} {'L max vu':>8} {'arret600':>8} {'float!=exact':>12}")
p2_ok = True; p4_ok = True; BOUND = {}
for p in PS:
    for k in KS:
        found, reels, st = bounded(p, k)
        BOUND[(p, k)] = (found, reels)
        same = d010.get((p, k)) == (len(found), len(reels))
        p2_ok &= same
        p4_ok &= (st["maxpops"] <= 2047 and st["capbit"] == 0 and st["stops"] == 0 and st["Lseen"] <= 11)
        print(f"  {p:>2} {k:>3} | {len(found):>11} {len(reels):>9} | {str(d010.get((p, k))):>11} | {st['maxpops']:>10} {st['capbit']:>12} {st['Lseen']:>8} {st['stops']:>8} {st['fve']:>12}"
              f"   reels={sorted(reels)}")
print(f"  P2 (9/9 lignes identiques a D010) : {'TENUE' if p2_ok else 'TOMBEE'}")

# ---------------------------------------------------------------- P5 : deux recensements exhaustifs, L <= 12
print("\n" + "=" * 90); print("P5 — exhaustif L <= 12 : DFS canonique (graphe) contre colliers (mots)"); print("=" * 90)
def dfs_canonical(p, k, Lmax):
    """tous les cycles simples de longueur <= Lmax, chacun une fois (depart = sommet minimal)."""
    M = 1 << k; S = succ_list(p, k); out = []
    for s in range(M):
        pile = [(s, (s,))]
        while pile:
            u, ch = pile.pop()
            for v in S[u]:
                if v == s: out.append(ch)
                elif v > s and v not in ch and len(ch) < Lmax: pile.append((v, ch + (v,)))
    return out

def rot_min(seq):
    i = seq.index(min(seq)); return tuple(seq[i:] + seq[:i])

def windows(w, k):
    L = len(w); ww = w * ((k + L - 1) // L + 1)
    return [tuple(ww[i:i + k]) for i in range(L)]

LYN = {L: lyndon_words(L) for L in range(1, LMAX_EXT + 1)}
print("  nb de mots de Lyndon par L : " + " ".join(f"{L}:{len(LYN[L])}" for L in range(1, LMAX_EXT + 1)))

def necklace_cycles(p, k, Lmax):
    """cycles simples obtenus par les mots : mot primitif dont les L fenetres cycliques de k bits sont distinctes."""
    inv = INV[(p, k)]; out = {}
    for L in range(1, Lmax + 1):
        for w in LYN[L]:
            W = windows(list(w), k)
            if len(set(W)) == L:
                out[w] = tuple(inv[x] for x in W)
    return out

p5_ok = True; lyn_eq_ok = True
for p in PS:
    for k in KS:
        A = {rot_min(list(c)) for c in dfs_canonical(p, k, 12)}
        NC = necklace_cycles(p, k, 12)
        B = {rot_min(list(c)) for c in NC.values()}
        eq = (A == B) and len(A) == len(NC)
        p5_ok &= eq
        lk = all(sum(1 for w in NC if len(w) == L) == len(LYN[L]) for L in range(1, k + 1))
        lyn_eq_ok &= lk
        byL = {}
        for c in A: byL[len(c)] = byL.get(len(c), 0) + 1
        print(f"  p={p} k={k:2d} : DFS={len(A):6d}  colliers={len(B):6d}  egaux={eq}  (L<=k : cycles = Lyndon : {lk})  par L : "
              + " ".join(f"{L}:{byL.get(L, 0)}" for L in range(1, 13)))
print(f"  P5 : {'TENUE' if (p5_ok and lyn_eq_ok) else 'TOMBEE'}")

# P4 : fusions de cles « ensemble de sommets » (deux cycles distincts, meme ensemble) parmi les fautifs L <= 11
print("\n  P4 — fusions possibles par la cle 'ensemble trie des sommets' (fautifs, L <= 11), et exhaustivite :")
for p in PS:
    for k in KS:
        NC = necklace_cycles(p, k, 11)
        faut = {w: c for w, c in NC.items() if p ** sum(w) > (1 << len(w))}
        keys = {}
        for w, c in faut.items(): keys.setdefault(tuple(sorted(c)), []).append(w)
        fus = sum(len(v) - 1 for v in keys.values())
        found, _ = BOUND[(p, k)]
        exh = set(keys) == set(found)
        p4_ok &= (fus == 0 and exh)
        print(f"  p={p} k={k:2d} : fautifs exhaustifs L<=11 = {len(faut):4d} ; cles distinctes = {len(keys):4d} ; fusions = {fus} ; "
              f"memes cles que l'exploration bornee : {exh}")
print(f"  P4 : {'TENUE' if p4_ok else 'TOMBEE'}")

# ---------------------------------------------------------------- P6/P7/P8/P9 : au-dela, L <= 22 ; parite ; controles
print("\n" + "=" * 90); print(f"P6-P9 — colliers jusqu'a L = {LMAX_EXT} : fautifs, realises, test 2-adique, controle 'composition inversee'"); print("=" * 90)
p6_ok = True; p9_ok = True
REAL = {}
TAB = {}
for k in KS:
    M = 1 << k
    inv3 = INV[(3, k)]
    # la structure (ensemble des mots simples) ne depend pas de p (P3) ; on garde le sommet de chaque p pour le test 2-adique
    simple = {}
    for L in range(1, LMAX_EXT + 1):
        for w in LYN[L]:
            W = windows(list(w), k)
            if len(set(W)) == L: simple[w] = W
    for p in PS:
        inv = INV[(p, k)]
        cnt = {}; real = []; bad2 = 0; badpar = 0; rev_fail = 0
        for w, W in simple.items():
            L = len(w); j = sum(w); d = (1 << L) - p ** j
            N = numer(w, p)
            u0 = inv[W[0]]
            if (N * pow(d % M, -1, M)) % M != u0: bad2 += 1               # x_w = N/d reduit mod 2^k == sommet de depart
            wr = tuple(reversed(w)); Nr = numer(wr, p)
            if (Nr * pow(d % M, -1, M)) % M != u0: rev_fail += 1           # controle negatif (bug C3)
            if p ** j > (1 << L):
                band = "L<=11" if L <= 11 else ("L=12" if L == 12 else "13..22")
                cnt[band] = cnt.get(band, 0) + 1
                if N % d == 0:
                    x = N // d
                    y = x; okp = True
                    for b in w:
                        if (y & 1) != b: okp = False
                        y = T(p, y)
                    if y != x: okp = False
                    if not okp: badpar += 1
                    real.append((L, j, x, x))
        p6_ok &= (bad2 == 0 and badpar == 0)
        p9_ok &= (rev_fail > 0)
        REAL[(p, k)] = real
        TAB[(p, k)] = cnt
        tot = sum(cnt.values())
        print(f"  p={p} k={k:2d} : fautifs L<=11={cnt.get('L<=11', 0):5d}  L=12={cnt.get('L=12', 0):5d}  L=13..22={cnt.get('13..22', 0):8d}  total={tot:8d} | "
              f"realises={len(real)} {[(L, j, x) for (L, j, x, _) in real]} | ecarts 2-adiques={bad2} parite={badpar} | inverse echoue={rev_fail}")
print(f"  P6 (0 ecart 2-adique, 0 ecart de parite) : {'TENUE' if p6_ok else 'TOMBEE'}")
print(f"  P9 (la composition inversee echoue au moins une fois a chaque (p,k)) : {'TENUE' if p9_ok else 'TOMBEE'}")
p7a = TAB[(7, 8)] and sum(TAB[(7, 8)].values()) > 10000
p7b = all(len(REAL[(7, k)]) == 0 for k in KS)
print(f"  P7 : fautifs p=7 k=8 L<=22 > 10000 : {p7a} ; 0 realise a p=7 pour L<=22 : {p7b}")
p8 = all(len([1 for (L, j, x, _) in REAL[(3, k)] if L <= 11]) == 3 for k in KS)
p8b = all(len(REAL[(3, k)]) == 3 for k in KS)
p8c = all(len([1 for (L, j, x, _) in REAL[(5, k)] if L <= 11]) == 1 for k in KS)
print(f"  P8 : p=3 realises L<=11 = 3 aux trois k : {p8} ; exactement 3 jusqu'a L=22 : {p8b} ; p=5 realises L<=11 = 1 : {p8c}")

# ---------------------------------------------------------------- P10 : recherche directe d'orbites entieres (sans mots)
print("\n" + "=" * 90); print("P10 — orbites entieres de T_p depuis x in [-200000, -1] (|x| <= 10^40, <= 2000 pas)"); print("=" * 90)
BIG = 10 ** 40
for p in PS:
    status = {}          # valeur -> 'esc' (echappe) ou id de cycle
    cycles = {}
    for x0 in range(-1, -200001, -1):
        if x0 in status: continue
        path = []; pos = {}; x = x0; res = None
        for _ in range(2000):
            if x in status: res = status[x]; break
            if x in pos:
                cyc = path[pos[x]:]; key = min(cyc); cycles[key] = len(cyc); res = ("cyc", key); break
            if abs(x) > BIG: res = "esc"; break
            pos[x] = len(path); path.append(x); x = T(p, x)
        if res is None: res = "long"
        for y in path:
            if abs(y) <= 10 ** 6: status[y] = res      # memo borne (memoire) ; ne change pas les cycles trouves
    nlong = sum(1 for v in status.values() if v == "long")
    desc = []
    for key in sorted(cycles, reverse=True):
        L = cycles[key]; y = key; w = []
        for _ in range(L): w.append(y & 1); y = T(p, y)
        desc.append(f"cycle min={key} L={L} j={sum(w)} fautif={p ** sum(w) > (1 << L)}")
    print(f"  p={p} : {len(cycles)} cycle(s) ; valeurs marquees 'long' (ni cycle ni echappement en 2000 pas) : {nlong}")
    for s in desc: print("     " + s)

print("\n" + "=" * 90); print("BILAN DES PREDICTIONS"); print("=" * 90)
for nom, ok in (("P2", p2_ok), ("P3", p3_ok), ("P4", p4_ok), ("P5", p5_ok and lyn_eq_ok), ("P6", p6_ok),
                ("P7a", p7a), ("P7b", p7b), ("P8", p8 and p8b and p8c), ("P9", p9_ok)):
    print(f"  {nom:4s} : {'TENUE' if ok else 'TOMBEE'}")
print("  P1 : canaris passes (sinon arret plus haut). P10 : a lire dans le tableau ci-dessus.")
