#!/usr/bin/env python3
# REQ-MATH-037 — ARES : le gamma du Junction Theorem (Merle 2026) EST le c_gen de Macindoe.
# Junction: log2 d - log2 C >= (S-1)*gamma, gamma = 1 - h(1/log2 3)   [par unite de S]
# L-A7   : margin(n) >= c_gen*n,            c_gen = L - L log2 L + (L-1) log2(L-1)  [par unite de n]
# TEST : gamma * log2(3) == c_gen exactement ?  (S ~ n*log2 3)
from mpmath import mp, mpf, log
mp.dps=50
L=log(3)/log(2)
def h(x): return -x*log(x)/log(2)-(1-x)*log(1-x)/log(2)
gamma=1-h(1/L); c=L-L*log(L)/log(2)+(L-1)*log(L-1)/log(2)
assert abs(c-mpf('0.0793186'))<mpf('1e-6'), "canari c_gen"
print("gamma =",mp.nstr(gamma,12)," gamma*L =",mp.nstr(gamma*L,12)," c_gen =",mp.nstr(c,12))
print("ecart =",mp.nstr(abs(gamma*L-c),6))
print("IDENTITE:", abs(gamma*L-c)<mpf('1e-40'))
