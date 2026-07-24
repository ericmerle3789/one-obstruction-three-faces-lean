#!/usr/bin/env python3
# test_REQ-MATH-033_autopsie_ombre.py — ARES (autopsie de l'unique anomalie : mecanisme ou coincidence ?)
# HYPOTHESE MECANISME : dans une cellule, les exposants (M_t<=n, S_t<=K, s_t<=S) sont PETITS.
# Si l est GRAND devant eux (ord_l(2), ord_l(3) >> n,K), les puissances 3^M, 2^S, 2^s-1 ne prennent
# que peu de valeurs => R0 mod l est CONFINE dans un petit ensemble, et 0 peut etre manque.
# => vraie obstruction locale, mais qui S'ETEINT quand n grandit (les exposants couvrent tout).
# PREDICTIONS : P1 residus distincts de R0 mod 101 dans (6,14) << 101. P2 le taux de couverture
# (residus atteints / l) croit avec n et tend vers 1 => mecanisme a portee FINIE.
import math, itertools
def R0(ms,ss):
    p=len(ms); sig=[ss[t]+ms[(t+1)%p] for t in range(p)]
    Ma=[0]*p; acc=0
    for t in range(p-1,-1,-1): Ma[t]=acc; acc+=ms[t]
    tot,Sp=0,0
    for t in range(p): tot+=3**Ma[t]*2**Sp*(2**ss[t]-1); Sp+=sig[t]
    return tot
def comps(total,parts):
    if parts==1: yield (total,); return
    for cuts in itertools.combinations(range(1,total),parts-1):
        pts=(0,)+cuts+(total,); yield tuple(pts[i+1]-pts[i] for i in range(parts))
print("=== P1 : CONFINEMENT des residus dans la cellule anomale (6,14), l=101 ===")
n,S=6,8; res=set(); cnt=0
for p in range(1,min(n,S)+1):
    for ms in comps(n,p):
        for ss in comps(S,p):
            res.add(R0(ms,ss)%101); cnt+=1
print(f"  mots={cnt} | residus DISTINCTS mod 101 = {len(res)} / 101  (couverture {100*len(res)/101:.0f}%)")
print(f"  0 est-il atteint ? {0 in res}   -> {'CONFINEMENT CONFIRME (P1)' if len(res)<101 else 'pas de confinement'}")
print("\n=== P2 : la couverture croit-elle avec n ? (mecanisme a portee finie ?) ===")
print(f"  {'n':>3} {'S':>3} {'l':>5} {'mots':>7} {'residus/l':>10} {'0 atteint':>10}")
for (n,S,l) in [(6,8,101),(8,8,101),(10,8,101),(12,8,101),(6,12,101),(6,8,31),(8,10,31),(6,8,13)]:
    res=set(); cnt=0
    for p in range(1,min(n,S)+1):
        for ms in comps(n,p):
            for ss in comps(S,p):
                res.add(R0(ms,ss)%l); cnt+=1
                if cnt>400000: break
    print(f"  {n:>3} {S:>3} {l:>5} {cnt:>7} {len(res)/l:>10.2f} {str(0 in res):>10}")
print("\n=== LECTURE ===")
print("Si la couverture -> 1 quand n grandit : l'ombre est REELLE mais s'eteint (portee finie),")
print("comme tous nos outils finis. Si elle reste < 1 : obstruction locale persistante = vraie piste.")
