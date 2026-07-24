#!/usr/bin/env python3
# test_REQ-MATH-025_filtre_realisabilite.py — ARES (le dernier verrou de la loterie calibree)
# QUESTION : gain formel (q | B) => VRAI cycle (orbite reelle suit le mot, revient) ?
# PREDICTION (mecanisme : le point fixe 2-adique x=B/q suit TOUJOURS l'itineraire du mot —
#  l'identite "fantome" de LENTILLE3) : filtre = 1 exactement. Donc lambda_formel = lambda_reel
#  et le residu nord 0.005 est deja l'esperance de VRAIS cycles.
#  (a) les 18 hits du recensement : orbite reelle verifiee pas a pas (sigma + retour). 18/18 attendu.
#  (b) fantome dans le cadre classique : 300 mots aleatoires, x = B*q^{-1} mod 2^B suit le sigma du mot.
import math, random
random.seed(20260724)
def beta(m): return 3**m - 2**m
def B_of(ms, ss):
    p=len(ms); n=sum(ms); B=0; Kp=0; Ma=n
    for t in range(p):
        Ma-=ms[t]; B+=3**Ma*2**Kp*beta(ms[t]); Kp+=ms[t]+ss[t]
    return B
def sigma_of(ms, ss):
    sig=[]
    for m,s in zip(ms,ss): sig += [1]*(m-1) + [s+1]
    return sig
def run_orbit(x, nsteps):
    """vraie carte : x impair -> (3x+1)/2^v ; renvoie (sigmas, x_final)"""
    sig=[]
    for _ in range(nsteps):
        y=3*x+1; v=(y & -y).bit_length()-1
        sig.append(v); x=y>>v
    return sig, x
# (a) LES 18 HITS DU RECENSEMENT
print("=== (a) realisabilite des 18 hits (orbite reelle exacte) ===")
hits=[]
for j in range(2,10):  hits.append(([1]*j,[1]*j))          # trivial^j
for j in range(2,8):   hits.append(([2]*j,[1]*j))          # (-5)^j
hits += [([4,3],[1,3]), ([3,4],[3,1]), ([4,3,4,3],[1,3,1,3]), ([3,4,3,4],[3,1,3,1])]
ok=0
for ms,ss in hits:
    n=sum(ms); K=n+sum(ss); q=2**K-3**n; B=B_of(ms,ss)
    assert B % abs(q)==0
    x=B//q
    sig,xf=run_orbit(x,n)
    good = (sig==sigma_of(ms,ss)) and (xf==x) and (x%2!=0)
    ok+=good
    if not good: print(f"  ECHEC : {ms}|{ss} x={x} sig_reel={sig} sig_mot={sigma_of(ms,ss)}")
print(f"  hits reellement realises : {ok}/{len(hits)} (x impair, sigma exact, retour exact)")
# (b) LE FANTOME DANS LE CADRE CLASSIQUE
print("\n=== (b) fantome 2-adique : x = B*q^-1 mod 2^Bits suit-il le sigma du mot ? (300 mots) ===")
okg=0; N=300
for _ in range(N):
    p=random.randint(1,5)
    ms=[random.randint(1,6) for _ in range(p)]; ss=[random.randint(1,6) for _ in range(p)]
    n=sum(ms); K=n+sum(ss); q=2**K-3**n; B=B_of(ms,ss)
    Bits=K+64+n
    x=(B*pow(q,-1,2**Bits))%2**Bits
    sig=[]
    okrun=True
    xx=x; marge=Bits
    for _ in range(n):
        y=(3*xx+1)%2**marge
        if y==0: okrun=False; break
        v=(y & -y).bit_length()-1
        if v>=marge-8: okrun=False; break
        sig.append(v); xx=(y>>v)%2**(marge-v); marge-=v
    okg += okrun and (sig==sigma_of(ms,ss))
print(f"  itineraires fantomes conformes au mot : {okg}/{N}")
print("\n=== VERDICT ===")
print("Si (a)=18/18 et (b)=300/300 : FILTRE = 1 (gain formel => vrai cycle, parite et valuations")
print("automatiques via le point fixe 2-adique). La loterie calibree est donc DIRECTEMENT l'esperance")
print("de vrais cycles : residu nord ~0.005 confirme sans correction.")
raise SystemExit(0 if (ok==len(hits) and okg==N) else 1)
