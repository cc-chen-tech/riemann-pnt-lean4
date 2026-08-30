"""Finite physical Type/Poisson/Ramanujan ledger with literal normalizations.

The finite Fourier sums below are exact algebraic models, evaluated in
floating point. They do not prove analytic tails, kernel separation, or
the coupled-kernel estimate. No squarefree mask is inserted on a split
parent: its nonsquarefree allocations must cancel in the full identity.
"""

import cmath
from fractions import Fraction as F
from math import ceil, floor, gcd, pi

from scripts.mwkf_mobius_type_identity import divisors, mobius


def restricted_type_ledger(n, q):
    """mu(n) 1_(n,q)=1 = 1_n=1 - sum_(A*b=n) mu(A)(1-1_b=1*1_(A,q)=1)."""
    if n < 1 or q < 1:
        raise ValueError("positive integer n and q required")
    terms = tuple((A, n//A, -mobius(A)) for A in divisors(n)
                  if mobius(A) and not (n == A and gcd(A, q) == 1))
    return {"direct": mobius(n)*int(gcd(n, q) == 1), "terms": terms,
            "reassembled": int(n == 1) + sum(term[2] for term in terms)}


def restricted_smooth_ledger(n, Q):
    """Expand mu(n)1_(n,Q)=1 using every Q-smooth divisor, including powers."""
    if n < 1 or Q < 1:
        raise ValueError("positive integer n and Q required")
    terms = []
    for r in divisors(n):
        rest = r
        while gcd(rest, Q) > 1:
            rest //= gcd(rest, Q)
        if rest == 1:
            terms.append((r, n//r, mobius(n//r)))
    return {"terms": tuple(terms), "sum": sum(term[2] for term in terms)}


def cofactor_count_bound(D, r, M):
    """Exact harmonic sum and a positive bound for all c, with endpoints."""
    D, r, M = map(F, (D, r, M))
    if D <= 0 or r <= 0 or M < 0:
        raise ValueError("positive D,r and nonnegative M required")
    value = sum((1/(r*n) for n in range(max(1, ceil(D/r)), floor(2*D/r)+1)), F(0))
    bound = 2/r if r <= 2*D else F(0)
    return {"harmonic_sum": value, "harmonic_bound": bound,
            "all_c_bound": bound*(1+2*M/D)}


def ramanujan_divisor_coefficient(s, A, m, k, l):
    """mu(s)c_s(inverse(A)*m+k*l)/s^2, with no density approximation."""
    if s < 1 or mobius(s) == 0 or gcd(A, s) != 1:
        raise ValueError("squarefree positive s and (A,s)=1 required")
    return sum((F(mobius(d), d)*F(mobius(s//d)**2, (s//d)**2)
                for d in divisors(s) if (m+A*k*l) % d == 0), F(0))


def finite_type_ramanujan(s, q, entry, h_weights, delta_weights, *, R, S, H, L):
    """Compare a literal signed entry sum with three finite transforms.

    s is a fixed squarefree modulus. entry, h_weights and delta_weights
    are finite dictionaries of integer positions to arbitrary complex
    weights. R,S,H,L normalize Fourier coefficients, not integer cutoffs.
    All m,k,l residues, including zero, are retained. The m=0 residue of
    this finite cyclic model is not an isolated continuous Poisson mode.

    The returned extra_inverse_S deliberately applies the *incorrect*
    HL/S prefactor to the unaveraged divisor sum for a regression witness.
    Runtime is polynomial in the small fixture modulus, not suitable for
    analytic-scale enumeration.
    """
    if s < 2 or q < 1 or mobius(s) == 0 or min(R, S, H, L) <= 0:
        raise ValueError("squarefree s>=2, positive q and scales required")
    if any(not isinstance(n, int) or n < 1 for n in entry):
        raise ValueError("entry positions must be positive integers")

    def phase(n):
        return cmath.exp(2j*pi*(n % s)/s)

    def shift_sum(inverse):
        return sum(u*v*phase(-h*d*inverse) for h, u in h_weights.items()
                   for d, v in delta_weights.items())

    gate = int(gcd(s, q) == 1)
    units = [x for x in range(s) if gcd(x, s) == 1]
    ramanujan = [sum(phase(n*x) for x in units) for n in range(s)]
    hhat = [sum(u*phase(-k*h) for h, u in h_weights.items())/H for k in range(s)]
    dhat = [sum(v*phase(-l*d) for d, v in delta_weights.items())/L for l in range(s)]
    direct = gate*mobius(s)*sum(mobius(n)*w*shift_sum(pow(n, -1, s))
                               for n, w in entry.items() if gcd(n, s*q) == 1)
    boundary = gate*mobius(s)*entry.get(1, 0)*shift_sum(1)
    type_sum, first, second, cofactor = 0j, 0j, 0j, 0j
    for A in range(1, max(entry, default=0)+1):
        if mobius(A) == 0 or gcd(A, s) != 1:
            continue
        inverse_A = pow(A, -1, s)
        b_weights = {n//A: w for n, w in entry.items() if n % A == 0
                     and not (n == A and gcd(A, q) == 1)}
        type_sum -= gate*mobius(s)*mobius(A)*sum(
            w*shift_sum(pow(A*b, -1, s)) for b, w in b_weights.items() if gcd(b, s) == 1)
        E = R/A
        bhat = [sum(w*phase(-m*b) for b, w in b_weights.items())/E for m in range(s)]
        for m in range(s):
            first -= gate*mobius(s)*R*mobius(A)/A/s*bhat[m]*sum(
                u*v*sum(phase(inverse_A*m*x-h*d*pow(x, -1, s)) for x in units)
                for h, u in h_weights.items() for d, v in delta_weights.items())
            for k in range(s):
                for l in range(s):
                    coefficient = gate*mobius(A)/A*bhat[m]*hhat[k]*dhat[l]
                    second -= R*H*L*coefficient*mobius(s)/s**2*ramanujan[(inverse_A*m+k*l) % s]
                    divisor_coefficient = ramanujan_divisor_coefficient(s, A, m, k, l)
                    cofactor += coefficient*divisor_coefficient
    return {"direct": direct, "boundary": boundary, "type_sum": boundary+type_sum,
            "kloosterman_sum": boundary+first, "ramanujan_sum": boundary+second,
            "divisor_cofactor": cofactor, "divisor_sum": boundary-R*H*L*cofactor,
            "extra_inverse_S": boundary-R*H*L/S*cofactor}
