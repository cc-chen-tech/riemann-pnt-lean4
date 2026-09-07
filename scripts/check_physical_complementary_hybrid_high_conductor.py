"""Finite guards ONLY: these do not prove the analytic hybrid bound."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
import random


@lru_cache(None)
def mu(n):
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


@lru_cache(None)
def divs(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


def transformed(e, n, q, m, mutation=None):
    """Return signed full IE total, never reimpose an expanded original mask."""
    h = gcd(e, m)
    a, z0 = e // h, m // h
    total = 0
    for f in divs(gcd(n, q)):
        x, y0 = n // f, q // f
        for l in divs(gcd(y0, z0)):
            y, z = y0 // l, z0 // l
            masks = [gcd(h, a), gcd(f, l), gcd(f*l, h*a),
                     gcd(x, f*h*a), gcd(y, f*l*h*a)]
            if mutation != 'drop_z_f':
                masks.append(gcd(z, f*a))
            else:
                masks.append(gcd(z, a))
            if mutation == 'add_x_l':
                masks.append(gcd(x, l))
            if mutation == 'add_z_h':
                masks.append(gcd(z, h))
            if any(g != 1 for g in masks):
                continue
            mf = 1 if mutation == 'drop_mu_f' else mu(f)
            ml = mu(l) if mutation == 'mu_l_not_square' else mu(l)**2
            total += mu(h)*mu(a)*mf*mu(x)*mu(y)*ml
    return total


def exact_ie_guards():
    checked = 0
    failures = Counter()
    examples = {}
    mutations = ('drop_mu_f', 'mu_l_not_square', 'add_x_l',
                 'add_z_h', 'drop_z_f')
    for e in range(1, 20):
        if not mu(e):
            continue
        for n in range(1, 25):
            for q in range(1, 23):
                if gcd(e, n*q) != 1:
                    continue
                for m in range(1, 14):
                    lhs = mu(e)*mu(n)*mu(q)*(gcd(n,q)==1)*(gcd(m,q)==1)
                    rhs = transformed(e,n,q,m)
                    assert lhs == rhs, (e,n,q,m,lhs,rhs)
                    checked += 1
                    for mutation in mutations:
                        if transformed(e,n,q,m,mutation) != lhs:
                            failures[mutation] += 1
                            examples.setdefault(mutation, (e,n,q,m))
    assert all(failures[m] > 0 for m in mutations), failures
    return checked, dict(failures), examples


def mapping_guards():
    count = 0
    seen_h_nonunit = False
    seen_x_l_nonunit = False
    # Inspect nonzero terms of the COMPLETE expansion, not just original
    # surviving tuples. The latter would incorrectly hide IE cancellation.
    for h,a,f,l in ((2,3,1,1), (1,5,1,2), (3,2,5,1),
                    (1,1,2,3), (5,6,7,1), (1,7,2,3)):
        if gcd(h,a)*gcd(f,l)*gcd(f*l,h*a) != 1:
            continue
        for x in range(1,15):
            for y in range(1,12):
                for z in range(1,10):
                    if (gcd(x,f*h*a),gcd(y,f*l*h*a),gcd(z,f*a)) != (1,1,1):
                        continue
                    if not mu(x)*mu(y):
                        continue
                    for w in range(1,10):
                        if (y*w-x*z) % a:
                            continue
                        e,n,q,m,k = h*a,f*x,f*l*y,h*l*z,h*w
                        v = f*l*(y*w-x*z)//a
                        if v == 0:
                            continue
                        assert gcd(e,m) == h
                        assert k % h == 0
                        assert gcd(w,a) == 1
                        assert n*m+e*v == q*k
                        assert F(q*k,n*m) == F(y*w,x*z)
                        assert v == (q*k-n*m)//e
                        seen_h_nonunit |= gcd(z,h)>1
                        seen_x_l_nonunit |= gcd(x,l)>1
                        count += 1
    assert seen_h_nonunit and seen_x_l_nonunit
    # Before expanding masks, (v,q)=1 is exactly (m,q)=1 on the relation.
    equivalences = 0
    for e in (1,2,3,5,6,7,10,15):
        for q in (1,2,3,5,6,7,10,15):
            if gcd(e,q)>1:
                continue
            for n in range(1,18):
                if gcd(n,e*q)>1:
                    continue
                for m in range(1,13):
                    h=gcd(e,m)
                    for k in range(1,12):
                        if (q*k-n*m)%e:
                            continue
                        v=(q*k-n*m)//e
                        assert k%h==0
                        assert (gcd(v,q)==1)==(gcd(m,q)==1)
                        equivalences += 1
    return count, equivalences


def cost_guards():
    rng=random.Random(20260831)
    for _ in range(640):
        R,Q,M,h,f,l,j,ph,Lam,T,tau = [F(rng.randrange(1,25)) for i in range(11)]
        K=R*M/Q
        A=R/f
        B=Q/(f*l)
        Z=M/(h*l)
        Xw=K/h
        D=Lam*tau*h*j/K
        N=B*Z*D
        assert A*Z==B*Xw
        assert N==Q**2*Lam*tau*j/(f*l*l*R)
        pref2=(Q*K)**2/(h*h*j*j*ph*ph*Lam**3*T*T*tau)
        reduced2=(Q*Q*K)**2/(h*h*f*f*l*l*ph*ph*Lam*Lam*T*T*j)
        assert pref2*A*N==reduced2
        H=Lam*Lam*tau
        terms2=[
            (Q*Q*K*Lam*tau)**2/(h*h*f*f*l*l*ph*ph*T*T*j),
            (Q*Q*K)**2*R*tau/(h*h*f**3*l*l*ph*ph*T*T*j),
            (Q**3*K*tau)**2*Lam/(h*h*f**3*l**4*ph*ph*T*T*R),
            (Q**3*K)**2*tau/(h*h*f**4*l**4*ph*ph*T*T*Lam)]
        assert terms2==[reduced2*H*H,reduced2*A*H,
                        reduced2*H*N,reduced2*A*N]
    return 640


def exponent_guards():
    eta=F(6,5)
    zeta=F(1,5)
    assert [F(1),2-eta,F(5,2)-F(3,2)*eta,
            F(7,2)-2*eta-zeta/2]==[1,F(4,5),F(7,10),1]
    assert F(7,2)-2*eta==F(11,10)
    for n in range(105,151):
        eta=F(n,100)
        # Scale identities after summing the four positive bounds.
        r=s=F(3); m=F(1,2); q=s-eta
        outer=1-r-s-m
        costs=[r+m+s,q+r+m+(r-1)/2,
               2*q+m+(r+eta)/2,2*q+r+m-F(1,2)]
        assert [outer+c for c in costs]==[1,2-eta,
                        F(5,2)-F(3,2)*eta,F(7,2)-2*eta]
    return 48


if __name__=='__main__':
    ie, mutations, witnesses=exact_ie_guards()
    mapping, equiv=mapping_guards()
    costs=cost_guards()
    exponents=exponent_guards()
    print({'double_IE':ie, 'mapped_terms':mapping, 'unit_equivalence':equiv,
           'exact_squared_costs':costs, 'exponent_guards':exponents})
    print({'expected_mutation_failures':mutations,'witnesses':witnesses})
    print('PASS: finite identities and algebra only; analytic CH5/CH8 NOT certified.')
