#!/usr/bin/env python3
# REQ-MATH-046 — ARES : synthese DIRIGEE PAR LE BUT d'une fonction de Lyapunov
# CRITERE (REQ-045) : il faut mu/sigma >= 0.3316 pour egaler le comptage c_gen=0.0793186 bit/pas.
# On remonte depuis le critere :
#  P1 : que donne la fonction la plus simple, log2 x ?  (dlog2x = log2 3 - v, v geometrique)
#  P2 : c_gen EST-IL le taux de grande deviation EXACT de log2 x ?  (unification des 2 moities)
#  P3 : des corrections 2-adiques (v2(x+1), qui gouverne les runs v=1) ameliorent-elles mu/sigma ?
import math, random
random.seed(20260725)
L=math.log2(3.0); C_GEN=0.0793186
def T(x):
    y=3*x+1; v=(y&-y).bit_length()-1
    return y>>v, v
def v2(m):
    return (m&-m).bit_length()-1 if m else 99
print("=== CANARIS ===")
c1 = T(3)==(5,1) and T(1)==(1,2) and T(5)==(1,4)
c2 = (v2(4)==2 and v2(8)==3 and v2(3+1)==2)
print(f"  T(3)=(5,1),T(1)=(1,2),T(5)=(1,4) : {c1} | v2 ok : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

print("=== P1 : mu/sigma de log2 x (theorie puis mesure) ===")
mu_th = 2-L; s_th = math.sqrt(2.0)
print(f"  theorie : E[v]=2, Var[v]=2  ->  mu={mu_th:.4f}, sigma={s_th:.4f}, mu/sigma={mu_th/s_th:.4f}")
N=200000; d=[]
for _ in range(N):
    x=random.randrange(1<<30,1<<60)|1
    y,v=T(x); d.append(math.log2(y)-math.log2(x))
mu=-sum(d)/N; s2=sum((z+mu)**2 for z in d)/N
print(f"  mesure  : mu={mu:.4f}, sigma={s2**.5:.4f}, mu/sigma={mu/s2**.5:.4f}   (critere 0.3316)")
print(f"  -> log2 x atteint {100*(mu/s2**.5)/0.3316:.0f}% du critere  (V3 : 14%)")

print("\n=== P2 : c_gen est-il le taux de grande deviation EXACT de log2 x ? ===")
# v geometrique P(v=j)=2^-j ; cycle exige moyenne(v) = L au lieu de 2
# taux exact I(L) = sup_t [ t*L - log2 E[2^{t v}] ]  (en bits)
def logMGF(t):   # log2 E[2^{t v}] , E = sum_j 2^-j 2^{t j}
    r=2.0**(t-1)
    if r>=1: return float('inf')
    return math.log2(r/(1-r))
best=-1e9; targ=None
tt=-4.0
while tt<0.99:
    val=tt*L-logMGF(tt)
    if val>best: best=val; targ=tt
    tt+=0.0001
print(f"  taux exact I(log2 3) = {best:.7f} bit/pas   (atteint a t={targ:.3f})")
print(f"  c_gen                = {C_GEN:.7f} bit/pas")
print(f"  ecart = {abs(best-C_GEN):.2e}  ->  {'IDENTIQUES : les deux moities sont le MEME objet' if abs(best-C_GEN)<1e-5 else 'differents'}")
print(f"  (approx gaussienne, pour comparaison : {mu_th**2/(2*s_th**2)/math.log(2):.4f} — sous-estime)")

print("\n=== P3 : corrections 2-adiques — une famille testee mecaniquement ===")
print(f"  {'candidate V(x)':>34} {'mu':>9} {'sigma':>9} {'mu/sigma':>10} {'vs critere':>11}")
def test(f,lab,N=120000):
    dd=[]
    for _ in range(N):
        x=random.randrange(1<<30,1<<60)|1
        y,v=T(x)
        dd.append(f(y)-f(x))
    m=-sum(dd)/N; ss=(sum((z+m)**2 for z in dd)/N)**.5
    print(f"  {lab:>34} {m:>9.4f} {ss:>9.4f} {m/ss:>10.4f} {100*(m/ss)/0.3316:>10.0f}%")
    return m/ss
test(lambda x: math.log2(x), "log2 x")
for c in (0.3,0.585,1.0,2.0):
    test(lambda x,c=c: math.log2(x)+c*v2(x+1), f"log2 x + {c}*v2(x+1)")
for c in (0.5,1.0):
    test(lambda x,c=c: math.log2(x)-c*v2(x+1), f"log2 x - {c}*v2(x+1)")
test(lambda x: math.log2(x)+0.585*v2(x+1)-0.415*v2(x-1), "log2 x +.585 v2(x+1) -.415 v2(x-1)")
print("\n=== LECTURE ===")
print("Si aucune correction ne depasse log2 x seul : la fonction optimale EST log2 x, son taux")
print("EST c_gen, et nous l'avons DEJA prouve (marginTarget). La synthese inverse boucle sur")
print("l'acquis — ce qui est un resultat, pas un echec : elle dit que la marge est OPTIMALE.")
