"""Exact finite UC guards; no numerical experiment proves the analytic bound.

Cyclotomic arithmetic checks all primitive conductors for squarefree q<=35,
including imprimitive/even moduli and complex characters. Fraction checks
exercise the nonzero-shift area count and physical budgets. No file writes.
"""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import gcd, lcm


@lru_cache(None)
def divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


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
def primes(n):
    return tuple(p for p in divisors(n) if p > 1 and len(divisors(p)) == 2)


def phi(n):
    return sum(gcd(a, n) == 1 for a in range(n))


def ramanujan(n, k):
    return sum(d * mu(n // d) for d in divisors(gcd(n, k)))


def polydivide(a, b):
    a = list(a)
    quotient = [0] * (len(a) - len(b) + 1)
    for j in range(len(quotient) - 1, -1, -1):
        quotient[j] = a[j + len(b) - 1]
        for k, value in enumerate(b):
            a[j + k] -= quotient[j] * value
    assert all(x == 0 for x in a)
    return tuple(quotient)


@lru_cache(None)
def cyclotomic(n):
    value = (-1,) + (0,) * (n - 1) + (1,)
    for d in divisors(n)[:-1]:
        value = polydivide(value, cyclotomic(d))
    return value


def normalized(terms, n):
    """Evaluate integer root-of-unity polynomial modulo Phi_n, exactly."""
    value = [0] * n
    for exponent, coefficient in terms.items():
        value[exponent % n] += coefficient
    modulus = cyclotomic(n)
    degree = len(modulus) - 1
    for j in range(n - 1, degree - 1, -1):
        coefficient = value[j]
        for k, entry in enumerate(modulus):
            value[j - degree + k] -= coefficient * entry
    return tuple(value[:degree])


def shift(terms, exponent, factor=1):
    return Counter({k + exponent: factor * value for k, value in terms.items()})


def multiply(left, right):
    result = Counter()
    for a, x in left.items():
        for b, y in right.items():
            result[a + b] += x * y
    return result


def add_to(target, source, factor=1):
    for key, value in source.items():
        target[key] += factor * value


@lru_cache(None)
def prime_logs(p):
    for generator in range(1, p):
        values = {pow(generator, j, p): j for j in range(p - 1)}
        if len(values) == p - 1:
            return values
    raise AssertionError("missing primitive root")


def primitive_characters(ell):
    factors = primes(ell)
    for exponents in product(*(range(1, p - 1) for p in factors)):
        yield tuple(zip(factors, exponents))


def char_phase(character, x, root_order):
    if any(x % p == 0 for p, _ in character):
        return None
    return sum(j * prime_logs(p)[x % p] * (root_order // (p - 1))
               for p, j in character) % root_order


def gauss(modulus, character, root_order, conjugate=False):
    value = Counter()
    for x in range(modulus):
        if gcd(x, modulus) != 1:
            continue
        phase = char_phase(character, x, root_order)
        assert phase is not None
        value[x * (root_order // modulus) + (-phase if conjugate else phase)] += 1
    return value


def support_area(r, s, m, k, include_zero=False):
    # The exact support is x in [m/2,2m], (rx+delta)/s in [k/2,2k].
    bound = int(2 * r * m + 2 * s * k) + 2
    value = F(0)
    for delta in range(-bound, bound + 1):
        if delta == 0 and not include_zero:
            continue
        left = max(m / 2, (s * k / 2 - delta) / r)
        right = min(2 * m, (2 * s * k - delta) / r)
        value += max(F(0), right - left)
    return value


def cadd(x, y):
    return x[0] + y[0], x[1] + y[1]


def cmul(x, y):
    return x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def cdiv(x, y):
    norm = y[0] ** 2 + y[1] ** 2
    product_value = cmul(x, (y[0], -y[1]))
    return product_value[0] / norm, product_value[1] / norm


def kernel_polynomial(z, t):
    """The polynomial part of G_t, over Q(i), not the Gamma estimate."""
    one = (F(1), F(0))
    z2 = cmul(z, z)
    s = (F(1, 2), F(t))
    sbar = (F(1, 2), -F(t))
    first = cadd(one, (-4 * z2[0], -4 * z2[1]))
    quotient_s = cdiv(z2, cmul(s, s))
    quotient_sbar = cdiv(z2, cmul(sbar, sbar))
    second = cadd(one, (-quotient_s[0], -quotient_s[1]))
    third = cadd(one, (-quotient_sbar[0], -quotient_sbar[1]))
    return cmul(first, cmul(second, third))


def run():
    counts = Counter()
    for q in range(2, 36):
        if mu(q) == 0:
            continue
        order = lcm(q, *(p - 1 for p in primes(q)))
        spectra = []
        for ell in divisors(q):
            if ell <= 1:
                continue
            c = q // ell
            for character in primitive_characters(ell):
                phase_c = char_phase(character, c, order)
                tau_bar = gauss(ell, character, order, conjugate=True)
                induced = gauss(q, character, order, conjugate=True)
                assert normalized(induced, order) == normalized(
                    shift(tau_bar, -phase_c, mu(c)), order)
                counts["imprimitive_gauss"] += 1
                tau = gauss(ell, character, order)
                minus_one = char_phase(character, -1, order)
                assert normalized(multiply(tau_bar, tau), order) == normalized(
                    {minus_one: ell}, order)
                counts["gauss_product"] += 1
                spectra.append((character, induced))
                # Finite Fourier version of Poisson, tested with signed weights.
                weights = [(-1) ** x * (1 + x * x) for x in range(ell)]
                left = Counter()
                right_inner = Counter()
                for x, weight in enumerate(weights):
                    phase = char_phase(character, x, order)
                    if phase is not None:
                        left[phase] += ell * weight
                for k in range(ell):
                    phase = char_phase(character, k, order)
                    if phase is None:
                        continue
                    for x, weight in enumerate(weights):
                        right_inner[-phase - k * x * (order // ell)] += weight
                assert normalized(left, order) == normalized(
                    multiply(tau, right_inner), order)
                counts["finite_poisson"] += 1
                for u, d in ((1, 1), (-1, 2), (2, 3), (-3, 5)):
                    if gcd(u * d, ell) != 1:
                        continue
                    # Exact coefficient before/after both Gauss factors.
                    phase_before = char_phase(character, -u * d, order)
                    phase_after = char_phase(character, u * d, order)
                    left = shift(multiply(induced, tau), phase_before)
                    right = {-phase_c + phase_after: mu(c) * ell}
                    assert normalized(left, order) == normalized(right, order)
                    counts["combined_orientation"] += 1
        for x in range(q):
            if gcd(x, q) != 1:
                continue
            right = Counter()
            for character, tau in spectra:
                add_to(right, shift(tau, char_phase(character, x, order)))
            left = Counter({x * (order // q): phi(q)})
            left[0] -= mu(q)
            assert normalized(left, order) == normalized(right, order)
            counts["complete_centered_spectrum"] += 1

    for s in range(1, 49):
        if mu(s) == 0:
            continue
        for h in range(-12, 13):
            if not h:
                continue
            a, q = gcd(s, abs(h)), s // gcd(s, abs(h))
            u = h // a
            assert gcd(a, q) == gcd(u, q) == 1
            for delta in (-11, -2, 1, 5, 13):
                if gcd(delta, s) != 1:
                    continue
                assert F(ramanujan(s, h * delta), phi(s)) == F(mu(q), phi(q))
                counts["literal_mean"] += 1
    for a in range(1, 25):
        for c in range(1, 25):
            if gcd(a, c) != 1:
                continue
            pairs = [(x, y) for x in divisors(a) for y in divisors(c)]
            assert sorted(x * y for x, y in pairs) == list(divisors(a * c))
            for delta in range(-6, 7):
                value = sum(mu(x * y) for x, y in pairs if delta % (x * y) == 0)
                assert value == int(gcd(delta, a * c) == 1)
                counts["full_unit_mask"] += 1
    for a_scale in (1, 2, 4, 8, 16, 32):
        for d in range(1, 2 * a_scale):
            count = sum(a % d == 0 for a in range(a_scale, 2 * a_scale))
            assert count <= F(2 * a_scale, d)
            counts["divisor_rows"] += 1
    scales = [F(2) ** j for j in range(-5, 4)]
    for r, s, m, k in product(range(1, 6), range(1, 6), scales, scales):
        assert support_area(r, s, m, k) <= 20 * s * m * k
        counts["nonzero_shift_area"] += 1
    # Delta=0 is not harmless: the area/product ratio becomes unbounded.
    tiny = F(1, 1024)
    assert support_area(1, 1, tiny, tiny, include_zero=True) > 20 * tiny**2
    assert support_area(1, 1, tiny, tiny) == 0
    counts["zero_shift_negative_guard"] += 1
    # A dropped a-unit divisor and a dropped imprimitive factor really fail.
    assert sum(mu(d) for d in divisors(3) if 5 % d == 0) == 1
    assert gcd(5, 15) != 1
    counts["omitted_a_mask_negative_guard"] += 1
    # Exact prefactor, with no second 1/S or 1/ell.
    for t, q0, a, q, r in product((2, 7), (1, 3), (1, 5), (1, 7), (1, 8)):
        s = a * q
        assert F(t, q0 * r * s) * r * a * q == F(t, q0)
        counts["physical_prefactor"] += 1
    # The root-term cancellation is squared to stay rational.
    for v, ell, dc, a in product((F(1, 2), F(3), F(100)), (1, 4), (1, 3), (1, 7)):
        d0 = v / (dc * ell)
        assert v * ell / dc * a * a / d0 == (a * ell) ** 2
        counts["joint_divisor_budget"] += 1
    # KP1: exact residue normalization, four moving and two boundary zeros.
    for t in range(2, 19):
        assert kernel_polynomial((F(0), F(0)), t) == (F(1), F(0))
        counts["kernel_origin"] += 1
        for real_sign, imag_sign in product((-1, 1), (-1, 1)):
            z = (F(real_sign, 2), F(imag_sign * t))
            assert kernel_polynomial(z, t) == (F(0), F(0))
            counts["kernel_moving_pole_cancellation"] += 1
        for real_sign in (-1, 1):
            assert kernel_polynomial((F(real_sign, 2), F(0)), t) == (F(0), F(0))
            counts["kernel_boundary_zero"] += 1
    # KP3-4: rational index phase and squared physical normalization only.
    # The conjugation of arbitrary complex b is established in the paper.
    for q0, r, s, m1, m2 in product((1, 4), (2, 5), (3, 7), (1, 6), (2, 9)):
        d, e = q0 * r, q0 * s
        assert F(m1, m2) * F(e, d) == F(m1 * s, m2 * r)
        counts["finite_index_phase"] += 1
    for t, q0, rscale, sscale, u, v in product(
            (2, 9), (1, 3), (1, 8), (2, 7), (F(1, 2), F(3, 2)), (F(1), F(2))):
        r, s = rscale * u, sscale * v
        literal_square = F(4 * t * t * sscale, q0 * q0 * r * s**3 * rscale)
        normalized_square = F(4 * t * t, q0*q0*rscale**2*sscale**2*u*v**3)
        assert literal_square == normalized_square
        counts["kernel_prefactor_square"] += 1
    # KP5-6: derivative accounting and exact nonzero-label dyadic multiplicity.
    for m, a, b in product(range(31), (0, 1, 8), (0, 1, 8)):
        n_tau, n_x = a + b + 2*m + 2, b + m + 1
        j = 4*m + a + 2*b + 10
        assert m + n_x - n_tau == -a - 1
        assert n_tau + n_x + m <= j
        counts["joint_ibp_orders"] += 1
    assert 4*30 + 8 + 2*8 + 10 == 154
    for j in range(-2, 33):
        assert sum(1 for h in range(-1, j + 2) if j - h >= -1) == j + 3
        counts["label_dyadic_multiplicity"] += 1
    print(dict(sorted(counts.items())))
    print(f"TOTAL {sum(counts.values())} exact checks; analytic tails are paper proofs.")


if __name__ == "__main__":
    run()
