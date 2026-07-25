#!/usr/bin/env python3
# REQ-MATH-045 — ARES : V3 (Walsh-Hadamard pondere, Merle) comme fonction de Lyapunov pour les CYCLES
# V3(n) = sum_k k*|bhat_k|, bhat = Walsh-Hadamard des bits de n, L = ceil(log2 n).
# LOGIQUE POUR LES CYCLES : autour d'une boucle, TOUTE fonction somme a 0. Si E[dV3] = -mu < 0
# avec variance s^2, un cycle de longueur n exige une DEVIATION de +mu*n -> proba ~ exp(-mu^2 n/(2 s^2)).
# => taux exponentiel INDEPENDANT de notre comptage (c_gen). Lequel est le plus fort ?
# PREDICTIONS : P1 R^2(V3, log2 n) tres faible (~0.008, reproduit le dépôt) ; P2 derive negative ;
#   P3 le taux de grande deviation de V3 est comparable ou superieur a c_gen=0.0793 bit/pas.
import math, random
random.seed(20260725)
def walsh(v):
    n=len(v); h=1; a=v[:]
    while h<n:
        for i in range(0,n,h*2):
            for j in range(i,i+h):
                x,y=a[j],a[j+h]; a[j]=x+y; a[j+h]=x-y
        h*=2
    return a
def V3(n):
    if n<=0: return 0.0
    L=max(1,n.bit_length())
    Lp=1<<(L-1).bit_length() if L>1 else 1     # padding puissance de 2
    bits=[(n>>i)&1 for i in range(L)]+[0]*(Lp-L)
    bh=walsh(bits)
    return sum(k*abs(bh[k]) for k in range(len(bh)))
def T(x):
    y=3*x+1; v=(y&-y).bit_length()-1
    return y>>v, v
print("=== CANARIS ===")
c1 = V3(1)>=0 and V3(0)==0
# cycle trivial 1 -> 1 : somme des dV3 doit etre EXACTEMENT 0
x=1; s=0.0
for _ in range(1):
    y,_v=T(x); s+=V3(y)-V3(x); x=y
c2 = (x==1 and abs(s)<1e-12)
print(f"  V3 definie : {c1} | cycle trivial : somme dV3 = {s:.1e} (doit etre 0) : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
print("=== P1 : V3 est-elle independante de la taille ? (R^2 avec log2 n) ===")
N=20000
xs=[]; ys=[]
for _ in range(N):
    n=random.randrange(1<<25,1<<55)|1
    xs.append(math.log2(n)); ys.append(V3(n))
mx=sum(xs)/N; my=sum(ys)/N
cov=sum((a-mx)*(b-my) for a,b in zip(xs,ys))/N
vx=sum((a-mx)**2 for a in xs)/N; vy=sum((b-my)**2 for b in ys)/N
R2=(cov*cov)/(vx*vy) if vx*vy>0 else 0
print(f"  R^2(V3, log2 n) = {R2:.4f}   (dépôt annonce ~0.008)   moyenne V3={my:.1f}, ecart-type={vy**.5:.1f}")
print("\n=== P2/P3 : derive et taux de grande deviation de V3 par pas impair ===")
d=[]
for _ in range(N):
    n=random.randrange(1<<25,1<<55)|1
    y,_v=T(n)
    d.append(V3(y)-V3(n))
mu=sum(d)/len(d); s2=sum((z-mu)**2 for z in d)/len(d)
print(f"  E[dV3] = {mu:+.3f}   ecart-type = {s2**.5:.3f}")
rate = (mu*mu)/(2*s2)/math.log(2) if s2>0 else 0     # bits par pas (gaussien)
print(f"  taux de grande deviation (gaussien) = {rate:.4f} bit/pas")
print(f"  a comparer a c_gen = 0.0793 bit/pas  ->  rapport = {rate/0.0793186:.1f}x")
print("\n=== RED TEAM : la queue est-elle gaussienne ? (sinon le taux est illusoire) ===")
d.sort()
for q in (0.001,0.01,0.5,0.99,0.999):
    i=int(q*(len(d)-1)); z=(d[i]-mu)/s2**.5
    print(f"  quantile {q:>6}: dV3 = {d[i]:>8.1f}  (z = {z:+.2f})")
import statistics
k4=sum((z-mu)**4 for z in d)/len(d)/(s2**2)
print(f"  kurtosis = {k4:.2f} (gaussienne = 3.0)  -> {'QUEUE LOURDE : taux gaussien NON valide' if k4>4 else 'compatible gaussien'}")
