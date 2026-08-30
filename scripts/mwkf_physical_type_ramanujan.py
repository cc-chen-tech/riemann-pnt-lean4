"""Finite physical Type/Poisson/Ramanujan ledger with literal normalizations.

The finite Fourier sums below are exact algebraic models, evaluated in
floating point. They do not prove analytic tails, kernel separation, or
the coupled-kernel estimate. No squarefree mask is inserted on a split
parent: its nonsquarefree allocations must cancel in the full identity.
"""

import cmath
from fractions import Fraction as F
from math import ceil, floor, gcd, lcm, pi

from scripts.mwkf_mobius_type_identity import divisors, mobius, split_mobius_identity


def smooth_kappa_packet(K, alpha, profile, profile_hat, radius):
    """Finite [1,2]-supported kappa sum and a centered Poisson truncation.

    The caller supplies a Fourier pair and must bound the omitted tail.
    This function neither checks smoothness nor asserts an analytic identity.
    The physical general-support statement is SK6 in the research note.
    """
    K, alpha, radius = map(F, (K, alpha, radius))
    if K <= 0 or radius < 1:
        raise ValueError("K>0 and dual radius>=1 required")
    samples = tuple((k, F(k)/K) for k in range(ceil(K), floor(2*K)+1))
    direct = sum(profile(x)*cmath.exp(2j*pi*float(alpha*k)) for k, x in samples)
    terms = {j: K*profile_hat(K*(j-alpha))
             for j in range(ceil(alpha-radius), floor(alpha+radius)+1)}
    return {"samples": samples, "direct": direct, "dual_terms": terms,
            "dual_truncated": sum(terms.values()), "zero": terms.get(0, 0),
            "nonzero": sum(value for j, value in terms.items() if j)}


def kappa_resonance_band(As, ds, ks, ls, width, *, e=1, q=1):
    """SK11 divisor enumeration, retaining literal IC2 coprimality masks.

    Rows are (A,d,k,l,j,residual), j!=0, residual=j*d-A*k*l. Integer
    endpoints and signed k,l remain; n+residual=0 is never factored.
    All parent rows remain, including zero Mobius weights.
    """
    As, ds, ks, ls = map(tuple, (As, ds, ks, ls))
    width = F(width)
    if (width < 0 or any(not isinstance(n, int) or n < 1 for n in (*As, *ds, e, q))
            or any(not isinstance(n, int) or n == 0 for n in (*ks, *ls))
            or any(len(set(values)) != len(values) for values in (As, ds, ks, ls))):
        raise ValueError("distinct integer axes, positive A,d,e,q, nonzero k,l and width>=0 required")
    dset = set(ds)
    rows = []
    for A in As:
        if gcd(e, A*q) != 1:
            continue
        for k in ks:
            for l in ls:
                n = A*k*l
                for r in range(-floor(width), floor(width)+1):
                    if n+r == 0:
                        continue
                    for d in divisors(abs(n+r)):
                        if d in dset and gcd(d, A*e*q) == 1:
                            rows.append((A, d, k, l, (n+r)//d, r))
    return tuple(sorted(rows))


def kappa_resonance_type_totals(rows, weight, cutoffs_a, cutoffs_d):
    """All nine signed SK18 sectors, with the SK17 physical 1/d weight.

    The supplied weight is evaluated on the unchanged full incidence row;
    it may retain labels via a closure. No norm or centering is asserted.
    """
    if any(not isinstance(n, int) or n < 1 for n in (*cutoffs_a, *cutoffs_d)):
        raise ValueError("positive integer Type cutoffs required")
    ua, va = cutoffs_a
    ud, vd = cutoffs_d

    def sectors(n, u, v):
        if n <= u:
            return (mobius(n), 0, 0)
        _, first, second = split_mobius_identity(n, cutoff_u=u, cutoff_v=v)
        return (0, -first, -second)

    names = ("small", "I", "II")
    totals = {f"{a}/{d}": F(0) for a in names for d in names}
    direct = F(0)
    for row in rows:
        A, d, k, l, j, r = row
        if min(A, d) < 1 or not k*l*j or j*d-A*k*l != r:
            raise ValueError("literal nonzero-j resonance row required")
        value = weight(row)*F(1, d)
        direct += mobius(A)*mobius(d)*value
        for name_a, wa in zip(names, sectors(A, ua, va)):
            for name_d, wd in zip(names, sectors(d, ud, vd)):
                totals[f"{name_a}/{name_d}"] += wa*wd*value
    return {"direct": direct, "sectors": totals}


def smooth_kappa_scales(R, S, H, L, K, e, K1, K2):
    """Exact SK1/SK13 scale ledger, not a certificate of kernel hypotheses."""
    R, S, H, L, K, e, K1, K2 = map(F, (R, S, H, L, K, e, K1, K2))
    if min(R, S, H, L, K, e, K1, K2) < 1:
        raise ValueError("all scales>=1 required")
    X, D, P = R/(e*K), S/e, K1*K2
    if min(X, D) < 1:
        raise ValueError("X=R/(eK)>=1,D=S/e>=1 required")
    C, rho = H*L/(R*e), H*L*P/S**2
    return {"X": X, "D": D, "P": P, "C": C, "rho": rho,
            "Z": R*P/S, "Y": X*P/D, "Delta": D/K,
            "nonzero_bound_scale": rho*(D**2/K+D), "zero_bound_scale": rho*D**2}


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


def inverse_c_lattice(R, A, e, d, Z, profile):
    """Finite sample side of inverse-c Poisson for entry support [1,2].

    Z denotes A*k*l. This routine evaluates only the finite sample side;
    it neither truncates an infinite Fourier sum nor estimates its tail.
    Poisson equality additionally requires the profile's regularity.
    """
    R, A, e, d, Z = map(F, (R, A, e, d, Z))
    if min(R, A, e, d) <= 0:
        raise ValueError("positive R,A,e,d required")
    jacobian = A*e/R
    samples = tuple((k, k*jacobian)
                    for k in range(max(1, ceil(1/jacobian)), floor(2/jacobian)+1))
    value = float(jacobian)*sum(profile(x)*cmath.exp(2j*pi*float((k*Z/d) % 1))
                                for k, x in samples)
    return {"jacobian": jacobian, "samples": samples, "value": value}


def inverse_c_allocation_ledger(r, s, q):
    """All signed (e,A,kappa) allocations at r=kappa*A*e, s=e*d.

    The integer-one endpoint is separate. Terms omit zero Mobius weights
    but never delete a nonzero allocation merely because r is not squarefree.
    """
    if min(r, s, q) < 1 or mobius(s) == 0 or gcd(s, q) != 1:
        raise ValueError("positive r,s,q, squarefree s and (s,q)=1 required")
    terms = tuple((e, A, r//(A*e), mobius(e)*mobius(A))
                  for e in divisors(gcd(r, s)) for A in divisors(r//e)
                  if gcd(A, s) == 1 and mobius(A))
    bulk = sum(w for e, A, k, w in terms)
    endpoint = mobius(r)*int(gcd(r, s*q) == 1)
    return {"terms": terms, "bulk": bulk, "endpoint": endpoint,
            "residual": bulk-endpoint,
            "physical_coefficient": -F(mobius(s), s)*(bulk-endpoint)}


def nearest_reciprocal_approximation(X, Z, t, sign=1):
    """Exact reduced +/-1/q approximation to +/-Z*t/X, when Z*t/X<=1/2."""
    X, Z, t = map(F, (X, Z, t))
    if X < 2 or Z < 1 or t < 1 or Z*t/X > F(1, 2) or sign not in (-1, 1):
        raise ValueError("X>=2,Z,t>=1,Z*t/X<=1/2 and sign=+/-1 required")
    denominator = floor(X/(Z*t)+F(1, 2))
    return {"alpha": sign*Z*t/X, "denominator": denominator,
            "approximant": F(sign, denominator)}


def small_linear_row_saving(x, z):
    """Exponent bookkeeping only, for the separately proved row lemma.

    X=T^x,Z=T^z. The z=0 boundary records no fixed-power saving.
    This is not a certificate for a physical packet or an arbitrary weight.
    """
    x, z = map(F, (x, z))
    if x <= 0 or not 0 <= z < x:
        raise ValueError("x>0 and 0<=z<x required")
    return min(x/5, (x-z)/2, z/2)


def _unit_density(n):
    return sum((F(mobius(d), d) for d in divisors(n)), F(0))


def unit_density_squares(moduli, coefficients):
    """Finite phi(lcm)/lcm Gram, not the canonical AFE zero Gram.

    Rational real inputs remain exact; complex inputs use floating point.
    Repeated and nonsquarefree positive moduli are allowed.
    """
    if len(moduli) != len(coefficients) or any(d < 1 for d in moduli):
        raise ValueError("matching coefficients and positive moduli required")
    rows = list(zip(moduli, coefficients))
    quadratic = sum((_unit_density(lcm(a, b))*x*y.conjugate()
                     for a, x in rows for b, y in rows), F(0))
    squares = {}
    for r in sorted({r for d in moduli for r in divisors(d)}):
        if mobius(r):
            value = sum((_unit_density(d)*c for d, c in rows if d % r == 0), F(0))
            squares[r] = value*value.conjugate()/(r*_unit_density(r))
    return {"quadratic": quadratic, "squares": squares,
            "square_sum": sum(squares.values(), F(0))}


def unit_interval_ledger(Q, left, right, alpha):
    """Exact finite unit/divisor sums versus continuous interval density.

    The interval is (left,right]. The alias is signed, not a positive
    remainder. A BV discrepancy bound retains both endpoint jumps.
    """
    if Q < 1 or not 0 <= left < right:
        raise ValueError("Q>=1 and 0<=left<right required")
    alpha = F(alpha)

    def phase(x):
        return cmath.exp(2j*pi*float(alpha*x))

    direct = sum(phase(n) for n in range(floor(left)+1, floor(right)+1) if gcd(n, Q) == 1)
    expanded = sum(mobius(v)*sum(phase(v*n)
                   for n in range(floor(F(left)/v)+1, floor(F(right)/v)+1)) for v in divisors(Q))
    integral = (phase(right)-phase(left))/(2j*pi*float(alpha)) if alpha else right-left
    density = float(_unit_density(Q))*integral
    bound = sum(mobius(v)**2 for v in divisors(Q))*(2+2*pi*abs(float(alpha))*(right-left))
    return {"direct": direct, "divisor_sum": expanded, "density": density,
            "alias": direct-density, "variation_bound": bound}


def collapse_triple_rows(records):
    """Pointwise signed grouping of (d,kappa,k,l,coefficient), before norms.

    Apply at each physical A or u if coefficients depend on that variable.
    Zero product axes are excluded from this nonzero-frequency interface.
    """
    result = {}
    for d, kappa, k, l, coefficient in records:
        if d < 1 or kappa < 1 or k*l == 0:
            raise ValueError("d,kappa>=1 and nonzero k*l required")
        key = (d, kappa*k*l)
        result[key] = result.get(key, 0)+coefficient
    return result


def ratio_collision_count(M, D):
    """Primitive-ray count of n1*d2=n2*d1 in [M,2M) x [D,2D)."""
    if not isinstance(M, int) or not isinstance(D, int) or min(M, D) < 1:
        raise ValueError("positive integer M,D required")

    def dilations(a, b, length):
        lower = max((length+a-1)//a, (length+b-1)//b)
        upper = min((2*length-1)//a, (2*length-1)//b)
        return max(0, upper-lower+1)

    return sum(dilations(a, b, M)*dilations(a, b, D)
               for a in range(1, 2*min(M, D)) for b in range(1, 2*min(M, D)) if gcd(a, b) == 1)


def joint_gram_cost_exponents(x, d, m, prefactor):
    """Power ledger after one Cauchy; not a norm theorem or coverage gate.

    Inputs are exponents of X,D,M and the *physical* scalar prefactor.
    M contains the full kappa block, not just the two other dual factors.
    """
    x, d, m, prefactor = map(F, (x, d, m, prefactor))
    if min(x, d, m) < 0:
        raise ValueError("X,D,M exponents must be nonnegative")
    return {"resonant": prefactor+x+(m-d)/2,
            "density": prefactor+x/2+(max(x, 2*d)+m-d)/2,
            "aliases": prefactor+x/2+m+max(F(0), x+m-d)/2}


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
