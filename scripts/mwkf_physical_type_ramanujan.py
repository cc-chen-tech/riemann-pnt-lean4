"""Finite physical Type/Poisson/Ramanujan ledger with literal normalizations.

The finite Fourier sums below are exact algebraic models, evaluated in
floating point. They do not prove analytic tails, kernel separation, or
the coupled-kernel estimate. No squarefree mask is inserted on a split
parent: its nonsquarefree allocations must cancel in the full identity.
"""

import cmath
from fractions import Fraction as F
from math import ceil, floor, gcd, lcm, pi

from scripts.mwkf_mobius_type_identity import c_u, divisors, mobius, split_mobius_identity


def _radical(n):
    return max(d for d in divisors(n) if mobius(d))


def _kappa_radical(r, n):
    return sum(mobius(d)*d for d in divisors(gcd(r, abs(n))))


def slope_b_interval(Y, n, k, j, nu, K2, width):
    """Integer B in [Y,2Y) with |K2*(nu+n*k/(j*B))|<=width.

    Endpoints are exact rationals. No coprimality condition is inserted;
    this is a finite sampling identity, not the smooth Poisson estimate.
    """
    if (not isinstance(Y, int) or Y < 1
            or any(not isinstance(a, int) or not a for a in (n, k, j))
            or not isinstance(nu, int)):
        raise ValueError("positive integer Y, nonzero integer n,k,j and integer nu required")
    K2, width = F(K2), F(width)
    if K2 <= 0 or width < 0:
        raise ValueError("positive K2 and nonnegative width required")
    y, tol = F(n*k, j), width/K2
    if y < 0:
        y, nu = -y, -nu
    lower_ratio, upper_ratio = -tol-nu, tol-nu
    if upper_ratio <= 0:
        return None
    lo = max(Y, ceil(y/upper_ratio))
    hi = min(2*Y-1, floor(y/lower_ratio)) if lower_ratio > 0 else 2*Y-1
    return (lo, hi) if lo <= hi else None


def slope_b_sampling(Y, n, k, j, K2, width):
    """All finite B/nu aliases with their signed scaled frequencies."""
    # The zero-frequency slice validates the shared domain before division.
    slope_b_interval(Y, n, k, j, 0, K2, width)
    K2, width = F(K2), F(width)
    phases = (F(n*k, j*Y), F(n*k, j*(2*Y-1)))
    lo = ceil(-max(phases)-width/K2)
    hi = floor(-min(phases)+width/K2)
    intervals, rows = {}, []
    for nu in range(lo, hi+1):
        interval = slope_b_interval(Y, n, k, j, nu, K2, width)
        if interval is not None:
            intervals[nu] = interval
            rows.extend((B, nu, K2*(nu+F(n*k, j*B)))
                        for B in range(interval[0], interval[1]+1))
    return {"intervals": intervals, "rows": tuple(sorted(rows))}


def global_slope_error_exponents(a, beta):
    """Balanced-top q=1 ledger only; no automatic coverage or kernel claim.

    Kmin=T^a, Kmax=T^(1-a), B~T^beta. The second error explicitly
    charges the integer +1 in every monotone B sampling interval.
    """
    a, beta = F(a), F(beta)
    if not 0 <= a <= F(1, 2) or beta < 0:
        raise ValueError("0<=a<=1/2 and beta>=0 required")
    return {"density": F(3), "interval_error": 1+a+F(3, 2)*beta,
            "integer_error": 2+a+beta/2, "uncompleted_error": 2+F(3, 2)*beta}


def mobius_u_one_ledger(n, Q):
    """Exact U=1 integer identity, retaining d=1 and nonsquarefree quotients."""
    if any(not isinstance(a, int) or a < 1 for a in (n, Q)):
        raise ValueError("positive integers n,Q required")
    atoms = tuple((b, n//b, -mobius(b)) for b in divisors(n)
                  if b < n and mobius(b) and gcd(n, Q) == 1)
    return {"atoms": atoms, "bulk": sum(a[2] for a in atoms),
            "endpoint": int(n == 1)}


def global_e_primitive_packet(M, B, j, k, l, ns, amplitude):
    """Finite q=1 all-e/v fusion with a COMMON n cutoff, excluding HL/R.

    The exact physical symbol must already depend only on M,B,n,j,k,l.
    This does not check that hypothesis, Fourier tails, or analytic norms.
    Non-squarefree M or B are inactive. Shared M,B primes are NOT removed.
    """
    ns = tuple(ns)
    if (any(not isinstance(a, int) or a < 1 for a in (M, B))
            or any(not isinstance(a, int) or not a for a in (j, k, l, *ns))
            or len(ns) != len(set(ns))):
        raise ValueError("positive M,B; nonzero integer j,k,l; distinct nonzero n required")
    active = bool(mobius(M) and mobius(B))
    e = gcd(M, B)
    A, b = M//e, B//e
    direct, fused, coefficients = 0j, 0j, {}
    for n in ns:
        coefficients[n] = F(mobius(B)*_kappa_radical(M, n), M*B*abs(j)) if active else F(0)
        if active:
            value = amplitude(M, B, n)*cmath.exp(-2j*pi*float(F(n*k*l, j*B)))
            for v in divisors(M):
                if n % (M//v) == 0:
                    direct += F(mobius(A)*mobius(b)*mobius(v), B*v*abs(j))*value
            fused += coefficients[n]*value
    return {"allocation": (e, A, b) if active else None,
            "coefficients": coefficients, "direct": direct, "fused": fused}


def primitive_resonant_rows(M, j, kl, Bmax):
    """Exact Delta=0 divisor family, not the original canonical zero Gram.

    Rows are (B,h,e,r,mu(M)*mu(B)); only a finite B ceiling is imposed.
    An actual physical support or symbol must be supplied separately.
    """
    if (not isinstance(M, int) or M < 1 or not mobius(M)
            or any(not isinstance(a, int) or not a for a in (j, kl))
            or not isinstance(Bmax, int) or Bmax < 0):
        raise ValueError("positive squarefree M, nonzero integer j,kl, integer Bmax>=0 required")
    d = gcd(abs(j), M)
    M1, j1 = M//d, j//d
    rows = []
    if kl % j1 == 0:
        for r in divisors(abs(kl//j1)):
            B, h = M1*r, -kl//(j1*r)
            if B <= Bmax and mobius(B) and gcd(h, M) == 1:
                rows.append((B, h, gcd(M, B), r, mobius(d)*mobius(r)))
    return {"d": d, "M1": M1, "j1": j1, "rows": tuple(sorted(rows)),
            "divisor_bound": len(divisors(abs(kl)))}


def primitive_band_rows(M, B, j, kl, H):
    """Finite exact frequency window; H=0 retains only primitive resonances."""
    if (any(not isinstance(a, int) or a < 1 for a in (M, B))
            or any(not isinstance(a, int) or not a for a in (j, kl))):
        raise ValueError("positive integers M,B and nonzero integer j,kl required")
    H = F(H)
    if H < 0:
        raise ValueError("nonnegative rational H required")
    lower, upper = F(M, B)*(-H-F(kl, j)), F(M, B)*(H-F(kl, j))
    return tuple((h, j*B*h+M*kl, F(B*h, M)+F(kl, j))
                 for h in range(ceil(lower), floor(upper)+1) if gcd(h, M) == 1)


def general_unit_type_ii_packet(A, e, q, B, j, k, l, ns, amplitude):
    """GU2 finite common-n lifting with all literal IC2 unit masks.

    The supplied symbol must already be independent of the v allocation.
    Its analytical validity, Poisson tails, and outer C=HL/(Re) are not
    certified here. Inactive/nonsquarefree parents return zero, not a
    spurious factorization of their completed modulus.
    """
    ns = tuple(ns)
    if (any(not isinstance(n, int) or n < 1 for n in (A, e, q, B))
            or any(not isinstance(n, int) or not n for n in (j, k, l, *ns))
            or len(ns) != len(set(ns))):
        raise ValueError("positive A,e,q,B and nonzero integer j,k,l, distinct nonzero n required")
    r, q0, L = _radical(e*q), _radical(q), _radical(A*e*q)
    g = gcd(A, q0)
    a = A//g
    active = bool(mobius(A) and mobius(e) and gcd(e, A*q) == gcd(B, A*e*q) == 1)
    coefficients, labels, direct, collapsed = {}, [], 0j, 0j
    for n in ns:
        if not active:
            coefficients[n] = F(0)
            continue
        phase = F(n*A*k*l, j*B*L)
        value = amplitude(A, n)*cmath.exp(-2j*pi*float(phase))
        for v in divisors(L):
            if n % (L//v) == 0:
                labels.append((v, n//(L//v), n))
                direct += F(mobius(A)*mobius(v), B*v*abs(j))*value
        coefficients[n] = F(mobius(r//g)*_kappa_radical(r, n)*_kappa_radical(a, n),
                            a*r*B*abs(j))
        collapsed += coefficients[n]*value
    return {"a": a, "g": g, "r": r, "L": L, "active": active,
            "coefficients": coefficients, "lifted_labels": tuple(labels),
            "direct": direct, "collapsed": collapsed}


def radical_kappa_mass(r, M):
    """GU7 floor-count majorant. In particular, M<r does not add one per divisor."""
    if (not isinstance(r, int) or r < 1 or not mobius(r)
            or not isinstance(M, int) or M < 0):
        raise ValueError("positive squarefree r and integer M>=0 required")
    ds = divisors(r)
    return {"absolute_mass": sum(abs(_kappa_radical(r, n)) for n in range(1, M+1)),
            "gcd_floor_mass": sum(sum(gcd(a, d) == 1 for a in range(1, d+1))*(M//d)
                                  for d in ds),
            "divisor_bound": M*len(ds)}


def general_unit_type_ii_exponents(r_exp, s, rho, z, k, beta, eta, chi):
    """GU9/GU10 exponent ledger, not a coverage flag.

    beta is log_T(U*B0), eta is the whole e-shell exponent, chi is
    log_T(rad(q)). Density still needs the original smooth critical core.
    The endpoint, nonstationary-tail hypotheses and q outer sum are separate.
    """
    r_exp, s, rho, z, k, beta, eta, chi = map(F, (r_exp, s, rho, z, k, beta, eta, chi))
    if min(r_exp, s, z, k, beta, eta, chi) < 0 or eta > s:
        raise ValueError("nonnegative scale exponents and eta<=s required")
    error = rho+(s+chi)/2+F(3, 2)*(z+beta)-k
    return {"density_all_e": rho+2*s-r_exp,
            "error_one_e": error, "error_e_shell": error+eta}


def type_ii_n_frequency(d, B, j, kl, h):
    """GU12 rational Fourier frequency, not a test for actual physical support."""
    if (any(not isinstance(n, int) or n < 1 for n in (d, B))
            or any(not isinstance(n, int) or n == 0 for n in (j, kl))
            or not isinstance(h, int)):
        raise ValueError("positive integer d,B, nonzero integer j,kl, integer h required")
    determinant = j*B*h+d*kl
    return {"determinant": determinant, "frequency": F(determinant, j*d),
            "coprime": gcd(d, B) == 1}


def type_ii_smooth_ledger(n, U, V, Q, chi):
    """JT1 finite bulk and positive transition boundary, with literal units.

    Caller supplies chi=0 on t<=1 and chi=1 on t>=2. No smoothness is
    certified here. The quotient m is not restricted to squarefree numbers.
    """
    if any(not isinstance(a, int) or a < 1 for a in (n, U, V, Q)):
        raise ValueError("positive integer n,U,V,Q required")
    unit = gcd(n, Q) == 1
    direct = -sum(c_u(a, U)*mobius(n//a) for a in divisors(n)
                  if unit and a > U and n//a > V)
    atoms = tuple((c, b, n//(b*c), -mobius(c)*mobius(b)*chi(F(n, b*U)))
                  for c in divisors(n) if unit and c <= U and mobius(c)
                  for b in divisors(n//c) if b > V and mobius(b))
    boundary = sum(mobius(a)*mobius(n//a)*(1-chi(F(a, U)))
                   for a in divisors(n) if unit and U < a < 2*U and n//a > V)
    return {"direct": direct, "bulk_atoms": atoms,
            "bulk": sum(row[3] for row in atoms), "boundary": boundary}


def joint_type_ii_normal_coordinates(t, x, eta, sigma):
    """Exact rational normal form; no numerical stationary-phase approximation."""
    t, x, eta, sigma = map(F, (t, x, eta, sigma))
    if x <= 0 or eta <= 0:
        raise ValueError("positive x,eta required")
    y = 1/x-eta
    w = t+sigma/(eta*(eta+y))
    return {"y": y, "w": w, "jacobian": (eta+y)**(-2),
            "phase": -sigma/eta+y*w, "x_recovered": 1/(eta+y),
            "t_recovered": w-sigma/(eta*(eta+y))}


def joint_type_ii_divisor_packet(A, B, j, k, l, ns, amplitude):
    """JT7 finite all-v reassembly for e=q=1, with a COMMON n cutoff.

    amplitude(A,n) must already have the proved allocation-independent
    physical symbol. This does not certify that hypothesis, analytic tails,
    or a norm bound. A rectangular ell cutoff or leftover v-shell cannot
    replace the lifted labels. The physical outer factor C*mu(b)*mu(c)
    and the other indices are left to the caller.
    """
    ns = tuple(ns)
    if (any(not isinstance(a, int) or a < 1 for a in (A, B))
            or any(not isinstance(a, int) or a == 0 for a in (j, k, l, *ns))
            or len(ns) != len(set(ns))):
        raise ValueError("positive A,B, nonzero integer j,k,l and distinct nonzero n required")
    active = gcd(A, B) == 1 and mobius(A) != 0
    labels, divisor_sum, coefficients = [], 0j, {}
    for n in ns:
        value = amplitude(A, n)*cmath.exp(-2j*pi*float(F(n*k*l, j*B))) if active else 0j
        for v in divisors(A) if active else ():
            a0 = A//v
            if n % a0 == 0:
                labels.append((v, n//a0, n))
                divisor_sum += F(mobius(A)*mobius(v), B*v*abs(j))*value
        g = gcd(A, abs(n))
        phi_g = sum(gcd(a, g) == 1 for a in range(1, g+1))
        coefficients[n] = F(mobius(g)*phi_g, A*B*abs(j)) if active else F(0)
    collapsed = sum(coefficients[n]*amplitude(A, n)*cmath.exp(-2j*pi*float(F(n*k*l, j*B)))
                    for n in ns) if active else 0j
    return {"divisor_sum": divisor_sum, "collapsed_sum": collapsed,
            "coefficients": coefficients, "lifted_labels": tuple(labels)}


def type_ii_density_factor(B, n):
    """Rational factor zeta(2)*c(B)*delta_B(n), for nonzero n.

    Prime powers in B or n are not counted repeatedly. No asymptotic or
    positivity of the full complex physical density is asserted.
    """
    if not isinstance(B, int) or B < 1 or not isinstance(n, int) or not n:
        raise ValueError("positive integer B and nonzero integer n required")
    result = F(1)
    for p in divisors(B*abs(n)):
        if p > 1 and len(divisors(p)) == 2:
            result *= F(p if B % p == 0 else 1, p+1)
    return result


def type_ii_squarefree_mean_ledger(X, B, n, profile):
    """JT9 finite equality only; profile is supported on [1,2].

    density_factor omits zeta(2)^(-1) and the integral profile(x)/x dx.
    The analytic discrepancy bound is proved in the note, not by this code.
    """
    X = F(X)
    if X <= 0:
        raise ValueError("positive X required")
    factor = type_ii_density_factor(B, n)
    direct = sum(F(mobius(A)**2, A)*sum(mobius(d)*d for d in divisors(gcd(A, abs(n))))
                 *profile(A/X) for A in range(max(1, ceil(X)), floor(2*X)+1)
                 if gcd(A, B) == 1)
    expanded = sum(mobius(d)*sum(F(mobius(u)**2, u)*profile(d*u/X)
                    for u in range(max(1, ceil(X/d)), floor(2*X/d)+1) if gcd(u, d*B) == 1)
                   for d in divisors(abs(n)) if mobius(d) and gcd(d, B) == 1)
    return {"direct": direct, "divisor_expansion": expanded, "density_factor": factor}


def type_ii_linear_row_exponents(p, nu, omega, u, cutoff_exp=0):
    """JT16 e=q=1 row cost, not a coverage certificate or all-e estimate."""
    p, nu, omega, u, cutoff_exp = map(F, (p, nu, omega, u, cutoff_exp))
    a = 3-nu-omega
    if not (a > p > 0 and 0 <= nu <= p and min(omega, u, cutoff_exp) >= 0):
        raise ValueError("a=3-nu-omega>p>0, 0<=nu<=p and nonnegative lengths required")
    delta = min(a/5, (a-p)/2, p/2)
    baseline = 2+2*p+u+cutoff_exp-nu
    return {"row_length": a, "saving": delta, "baseline": baseline,
            "cost": baseline-delta, "stationary_b_min": 3-p-omega-cutoff_exp}


def joint_type_i_unit_packet(K, D, B, Q, z0, amplitude, dual_hat, j_cutoff, ell_cutoff):
    """JQ3/JQ5 finite samples and a rectangular double-Poisson truncation.

    amplitude(t,x) includes 1/x and is supported in [.5,3] x [1,2].
    dual_hat(j,xi) supplies the Fourier transform of H_j in JQ4. The
    caller must supply a correct Fourier pair and control both tails;
    this routine proves no smoothness, derivative bounds, or analytic gate.
    Only m is restricted to units here; the physical caller needs (B,Q)=1.
    """
    K, D, z0 = map(F, (K, D, z0))
    if K < 1 or D <= 0 or any(not isinstance(a, int) or a < 1
                              for a in (B, Q, j_cutoff, ell_cutoff)):
        raise ValueError("K>=1, D>0 and positive integer B,Q,cutoffs required")
    kappas = range(ceil(K/2), floor(3*K)+1)

    def sample(kappa, m):
        t, x = kappa/K, B*m/D
        return amplitude(t, x)*cmath.exp(2j*pi*float(z0*t/x))/D

    direct = sum(sample(kappa, m) for kappa in kappas
                 for m in range(ceil(D/B), floor(2*D/B)+1) if gcd(m, Q) == 1)
    divisor_sum = sum(mobius(v)*sum(sample(kappa, v*n) for kappa in kappas
                      for n in range(ceil(D/(B*v)), floor(2*D/(B*v))+1))
                      for v in divisors(Q) if mobius(v))
    zero, aliases = 0j, 0j
    for v in divisors(Q):
        if not mobius(v):
            continue
        coefficient, M = K*F(mobius(v), B*v), D/(B*v)
        for j in range(-j_cutoff, j_cutoff+1):
            zero += coefficient*dual_hat(j, 0)
            aliases += coefficient*sum(dual_hat(j, ell*M)
                        for ell in range(-ell_cutoff, ell_cutoff+1) if ell)
    return {"direct": direct, "divisor_sum": divisor_sum,
            "dual_truncated": zero+aliases, "zero_ell": zero, "nonzero_ell": aliases}


def joint_type_i_cost_exponents(s, rho, z, k, beta, eta=0):
    """JQ15--JQ18 exponent ledger, never a coverage certificate.

    All inputs are exponents, including rho. The density still needs its
    (1+Z)^(-J) factor. Actual smoothness, K/Z range, and both endpoints
    must be checked separately. An e-shell contains T^eta integers.
    """
    s, rho, z, k, beta, eta = map(F, (s, rho, z, k, beta, eta))
    if min(s, z, k, beta, eta) < 0 or eta > s:
        raise ValueError("nonnegative scale/cutoff exponents and eta<=s required")
    stationary, joint = rho+s+z/2+beta, rho+s+z+beta-k
    return {"density_shell": rho+2*s-eta,
            "stationary_one_e": stationary-eta, "joint_one_e": joint-eta,
            "stationary_shell": stationary, "joint_shell": joint,
            "best_alias_shell": min(stationary, joint)}


def type_i_quotient_ledger(n, U, V, Q):
    """Finite TI2 completion, with its small endpoint and literal unit mask.

    Atoms are (c,b,m,-mu(c)*mu(b)). No squarefree mask is placed on m.
    """
    if any(not isinstance(a, int) or a < 1 for a in (n, U, V, Q)):
        raise ValueError("positive integer n,U,V,Q required")
    unit = gcd(n, Q) == 1
    direct = -sum(c_u(a, U)*mobius(n//a) for a in divisors(n)
                  if unit and a > U and n//a <= V)
    atoms = tuple((c, b, n//(b*c), -mobius(c)*mobius(b))
                  for c in divisors(n) if unit and c <= U and mobius(c)
                  for b in divisors(n//c) if b <= V and mobius(b))
    return {"direct": direct, "atoms": atoms,
            "completed": sum(row[3] for row in atoms),
            "endpoint": mobius(n) if unit and n <= V else 0}


def type_i_unit_completion(B, Q, D, profile, profile_hat, cutoff):
    """TI3 unit-quotient Poisson ledger for a [1,2]-supported profile.

    The caller supplies a Fourier pair and must control the omitted tail.
    The profile represents Psi_z, including the reciprocal phase. This
    routine checks neither smoothness nor the physical kernel hypotheses.
    It restricts m to units; the physical caller additionally needs (B,Q)=1.
    """
    D = F(D)
    if (any(not isinstance(a, int) or a < 1 for a in (B, Q, cutoff)) or D <= 0):
        raise ValueError("positive integer B,Q,cutoff and positive D required")

    def samples(step):
        return range(ceil(D/step), floor(2*D/step)+1)

    direct = sum(profile(B*m/D)/D for m in samples(B) if gcd(m, Q) == 1)
    divisor_sum = sum(mobius(v)*sum(profile(B*v*n/D)/D for n in samples(B*v))
                      for v in divisors(Q) if mobius(v))
    dual = sum(F(mobius(v), B*v)*sum(profile_hat(ell*D/(B*v))
               for ell in range(-cutoff, cutoff+1)) for v in divisors(Q) if mobius(v))
    density = _unit_density(Q)/B*profile_hat(0)
    return {"direct": direct, "divisor_sum": divisor_sum,
            "dual_truncated": dual, "density": density, "aliases": dual-density}


def type_i_stationary_aliases(B, Q, D, z):
    """Exact TI13 candidate saddles (v,ell,x^2), including support endpoints.

    A candidate need not contribute: the actual amplitude can vanish there.
    No positivity or lower bound for the signed alias sum is asserted.
    """
    D, z = map(F, (D, z))
    if any(not isinstance(a, int) or a < 1 for a in (B, Q)) or D <= 0 or not z:
        raise ValueError("positive integer B,Q, positive D and nonzero z required")
    rows = []
    for v in divisors(Q):
        if not mobius(v):
            continue
        lower, upper = sorted((-z*B*v/D, -z*B*v/(4*D)))
        for ell in range(ceil(lower), floor(upper)+1):
            if ell*z < 0:
                rows.append((v, ell, -z*B*v/(ell*D)))
    return tuple(sorted(rows))


def type_i_density_cost(scales, U, V):
    """TI7 physical scale ledger, not a bound without its kernel hypotheses.

    density_scale still multiplies (1+Z)^(-J); both costs allow T^epsilon.
    The small endpoint must vanish or be separately included.
    """
    if any(not isinstance(a, int) or a < 1 for a in (U, V)):
        raise ValueError("positive integer U,V required")
    D, Z, rho = (F(scales[key]) for key in ("D", "Z", "rho"))
    if D <= 0 or Z < 0 or rho < 0:
        raise ValueError("positive D and nonnegative Z,rho required")
    return {"density_scale": rho*D**2, "alias_scale": rho*D*(1+Z)*U*V}


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
