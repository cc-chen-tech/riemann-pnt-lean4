#!/usr/bin/env python3
"""Finite guards for common-frequency Parseval and conductor descent.

Cyclotomic identities are exact; finite floating norm checks are sanity
checks only. They do not establish smoothness, the general large sieve,
physical packet coverage, or any assertion about zeta zeros.
"""

from collections import defaultdict
from fractions import Fraction as Rat
from itertools import product
from math import gcd, lcm
import unittest

from check_pre_cauchy_common_determinant import inv, mobius, root_normal_form
from check_common_zero_product_poisson import complex_value, divisors, units
from check_all_common_frequencies_prime_average import kernel_terms, phi


def prime_powers(n):
    result, p = [], 2
    while p * p <= n:
        q = 1
        while n % p == 0:
            n //= p
            q *= p
        if q > 1:
            result.append((p, q))
        p += 1
    if n > 1:
        result.append((n, n))
    return result


def characters(modulus):
    """Enumerate all unit characters, including noncyclic 2-power groups."""
    factors = []
    for p, q in prime_powers(modulus):
        if p != 2 or q <= 4:
            for gen in units(q):
                logs = {pow(gen, k, q): k for k in range(phi(q))}
                if len(logs) == phi(q):
                    factors.append((q, (phi(q),), {x: (v,) for x, v in logs.items()}))
                    break
            else:
                raise AssertionError("cyclic prime-power unit group expected")
        else:
            order = q // 4
            logs = {((-1) ** s * pow(5, t, q)) % q: (s, t)
                    for s in range(2) for t in range(order)}
            factors.append((q, (2, order), logs))
    orders = [o for _, local_orders, _ in factors for o in local_orders]
    root_order = lcm(*orders) if orders else 1
    for indices in product(*(range(o) for o in orders)):
        chi = {}
        for n in units(modulus):
            logs = [v for q, _, table in factors for v in table[n % q]]
            chi[n] = sum(k * v * (root_order // o)
                         for k, v, o in zip(indices, logs, orders)) % root_order
        yield root_order, chi


def conductor(modulus, chi):
    for d in divisors(modulus):
        classes = defaultdict(set)
        for n in units(modulus):
            classes[n % d].add(chi[n])
        if all(len(values) == 1 for values in classes.values()):
            return d
    raise AssertionError("character must have a conductor")


def compress(modulus, terms):
    result = defaultdict(Rat)
    for exponent, coefficient in terms:
        result[exponent % modulus] += coefficient
    return [(e, a) for e, a in result.items() if a]


def square_terms(modulus, terms):
    terms = compress(modulus, terms)
    return [(x - y, a * b) for x, a in terms for y, b in terms]


def kloosterman_terms(c, J, K, z):
    return [(J * a + K * z * inv(a, c), Rat(1)) for a in units(c)]


def projection(c, row, selected):
    result = {x: 0j for x in units(c)}
    for order, chi in selected:
        coefficient = sum(row[x] * complex_value(order, [(-chi[x], Rat(1))]) for x in units(c))
        for x in units(c):
            result[x] += coefficient * complex_value(order, [(chi[x], Rat(1))]) / phi(c)
    return result


class FrequencyConductorChecks(unittest.TestCase):
    def assertRootsEqual(self, modulus, left, right):
        self.assertEqual(root_normal_form(modulus, left), root_normal_form(modulus, right))

    def test_all_character_enumeration_exact(self):
        for c in (2, 4, 6, 8, 9, 12, 15, 16, 20, 21):
            chars = list(characters(c))
            self.assertEqual(len(chars), phi(c))
            order = chars[0][0]
            for x, y in product(units(c), repeat=2):
                self.assertRootsEqual(order, [(chi[x] - chi[y], Rat(1)) for _, chi in chars],
                                      [(0, phi(c) * int(x == y))])

    def test_primitive_classification_edges(self):
        counts = {c: sum(conductor(c, chi) == c for _, chi in characters(c))
                  for c in (2, 3, 4, 6, 8, 9, 12, 15)}
        self.assertEqual(counts, {2: 0, 3: 1, 4: 1, 6: 0, 8: 2, 9: 4, 12: 1, 15: 3})

    def test_composite_primitive_gauss_all_arguments_exact(self):
        for c in (4, 8, 9, 12, 15, 21):
            for order, chi in characters(c):
                if conductor(c, chi) != c:
                    continue
                modulus = lcm(c, order)
                sc, sh = modulus // c, modulus // order
                tau = [(sc * a + sh * chi[a], Rat(1)) for a in units(c)]
                self.assertRootsEqual(modulus, square_terms(modulus, tau), [(0, c)])
                for j in range(c):
                    left = [(sc * j * a + sh * chi[a], Rat(1)) for a in units(c)]
                    right = [(e - sh * chi[j], a) for e, a in tau] if gcd(j, c) == 1 else []
                    self.assertRootsEqual(modulus, left, right)

    def test_nonprimitive_nonunit_gauss_need_not_vanish(self):
        # Principal mod 6 is imprimitive and has Ramanujan sum -1 at j=2.
        self.assertRootsEqual(6, [(2 * a, Rat(1)) for a in units(6)], [(0, -1)])

    def test_active_projected_kloosterman_mellin_exact(self):
        for c in (4, 8, 9, 12, 15):
            for order, chi in characters(c):
                if conductor(c, chi) != c:
                    continue
                modulus = lcm(c, order)
                sc, sh = modulus // c, modulus // order
                for J, K in ((1, 1), (2, 1), (1, 3), (0, 1)):
                    left = [(sc * e - sh * chi[z], a) for z in units(c)
                            for e, a in kloosterman_terms(c, J, K, z)]
                    right = [(sc * (J * a + K * b) - sh * (chi[a] + chi[b]), Rat(1))
                             for a, b in product(units(c), repeat=2)]
                    self.assertRootsEqual(modulus, left, right)
                    if gcd(J * K, c) != 1:
                        self.assertRootsEqual(modulus, left, [])

    def test_common_frequency_parseval_identity_exact(self):
        for g in (2, 3, 6, 10, 15):
            b = {r: Rat((r % 5) - 2, 3) for r in units(g)}
            base = {t: int(t == 1) for t in units(g)}
            amplitude = {t: Rat(1 if t % 3 else 2, 3) for t in units(g)}
            for J, K in ((1, 1), (0, 0), (2, 3)):
                left = []
                for nu in range(g):
                    phase = {t: base[t] + nu * (g - 1) * t for t in units(g)}
                    row = [(e, a * b[r]) for r in units(g)
                           for e, a in kernel_terms(g, J, K, r, phase, amplitude)]
                    left += [(e, a / g) for e, a in square_terms(g, row)]
                right = []
                for t in units(g):
                    row = [(e, a * b[r]) for r in units(g)
                           for e, a in kloosterman_terms(g, J, K, r * t)]
                    right += [(e, a * amplitude[t] ** 2 / (g * g))
                              for e, a in square_terms(g, row)]
                self.assertRootsEqual(g, left, right)

    def test_common_frequency_operator_bound_sanity(self):
        for g in (2, 3, 6, 10, 15, 30):
            b = {r: Rat((r % 7) - 3, 4) for r in units(g)}
            for J, K in ((1, 1), (0, 0), (2, 3), (g, g)):
                energy = sum(abs(sum(float(b[r]) * complex_value(g, kloosterman_terms(g, J, K, r * t))
                                     for r in units(g))) ** 2 for t in units(g)) / (g * g)
                bound = gcd(g, gcd(J, K)) ** 2 * sum(float(x) ** 2 for x in b.values())
                self.assertLessEqual(energy, bound + 1e-8)

    def test_nonunit_frequency_speed_cannot_use_full_parseval(self):
        g, speed = 15, 3
        self.assertNotEqual(len({nu * speed % g for nu in range(g)}), g)
        # Distinct unit inputs collide, so the off-diagonal term survives.
        self.assertEqual(gcd(1 * 11, g), 1)
        self.assertRootsEqual(g, [(nu * speed * (1 - 11), Rat(1, g)) for nu in range(g)], [(0, 1)])

    def test_composite_bessel_with_nonunit_indices_sanity(self):
        for c in (4, 8, 9, 12, 15, 21):
            b = {n: Rat((n % 7) - 3, 4) for n in range(1, 2 * c + 2)}
            left = 0.0
            for order, chi in characters(c):
                if conductor(c, chi) == c:
                    value = sum(float(a) * complex_value(order, [(chi[n % c], Rat(1))])
                                for n, a in b.items() if gcd(n, c) == 1)
                    left += c / phi(c) * abs(value) ** 2
            right = sum(abs(complex_value(c, [(v * n, a) for n, a in b.items()])) ** 2 for v in units(c))
            self.assertLessEqual(left, right + 1e-8)

    def test_reduced_fractions_with_composite_denominators(self):
        for R in (4, 7, 10):
            points = [Rat(v, c) for c in range(R + 1, 2 * R + 1) for v in units(c)]
            self.assertEqual(len(points), len(set(points)))
            for i, x in enumerate(points):
                for y in points[i + 1:]:
                    gap = abs(x - y)
                    self.assertGreaterEqual(min(gap, 1 - gap), Rat(1, 4 * R * R))

    def test_induced_transform_descent_keeps_masks_exact(self):
        c, k = 5, 6
        for order, chi in characters(c):
            if conductor(c, chi) != c:
                continue
            original, reduced, wrong = [], [], []
            for h, delta, n in product(range(1, 5), range(1, 5), range(1, 8)):
                weight = mobius(n) * (h - 2 * delta)
                if gcd(h * delta * n, c * k) == 1:
                    x = -h * delta * inv(n, c * k) % (c * k)
                    original.append((-chi[x % c], Rat(weight)))
                    reduced.append((-chi[-h * delta * inv(n, c) % c], Rat(weight)))
                if gcd(h * delta * n, c) == 1:
                    wrong.append((-chi[-h * delta * inv(n, c) % c], Rat(weight)))
            self.assertRootsEqual(order, original, reduced)
            # At least one character must see the dropped-mask error.
            if root_normal_form(order, wrong) != root_normal_form(order, reduced):
                break
        else:
            self.fail("mask counterexample fixture must be nontrivial")

    def test_induced_pointvalue_and_original_row_energy_sanity(self):
        for c, k in ((3, 5), (5, 6), (9, 2)):
            r = c * k
            original = {x: complex(x % 7 - 3, x % 3 - 1) for x in units(r)}
            reduced = {x: sum(v for y, v in original.items() if y % c == x) for x in units(c)}
            selected = [(order, chi) for order, chi in characters(c) if conductor(c, chi) == c]
            W = projection(c, reduced, selected)
            induced = [(order, {x: chi[x % c] for x in units(r)}) for order, chi in selected]
            Z = projection(r, original, induced)
            for x in units(r):
                self.assertAlmostEqual(abs(Z[x] - W[x % c] / phi(k)), 0, places=9)
            self.assertAlmostEqual(sum(abs(z) ** 2 for z in Z.values()),
                                   sum(abs(z) ** 2 for z in W.values()) / phi(k), places=8)

    def test_inactive_unit_masks_and_rescaling_exact(self):
        for k in (6, 10, 15):
            for h, delta, n in product(range(1, 8), repeat=3):
                expanded = sum(mobius(dh) * mobius(dd)
                               for dh in divisors(k) if h % dh == 0
                               for dd in divisors(k) if delta % dd == 0) * int(gcd(n, k) == 1)
                self.assertEqual(expanded, int(gcd(h * delta * n, k) == 1))
        g, c, k = 5, 7, 6
        for dh, dd, nu, n in product(divisors(k), divisors(k), range(g), units(g)):
            multiplier = dh * dd
            self.assertEqual(gcd(multiplier, g * c), 1)
            self.assertEqual((nu * multiplier * inv(n, g)) % g,
                             ((nu * multiplier % g) * inv(n, g)) % g)

    def test_inverse_totient_divisor_weight_euler_majorant(self):
        for K in (6, 10, 20):
            direct = sum((Rat(len(divisors(k)) ** 2, phi(k)) for k in range(1, K + 1) if mobius(k)), Rat(0))
            bound = Rat(1)
            for p in range(2, K + 1):
                if len(divisors(p)) == 2:
                    bound *= 1 + Rat(4, p - 1)
            self.assertLessEqual(direct, bound)

    def test_primitive_projection_deletes_principal_and_axes_sanity(self):
        for c in (4, 6, 8, 9, 12, 15):
            selected = [(o, ch) for o, ch in characters(c) if conductor(c, ch) == c]
            for J, K in ((0, 0), (0, 1), (1, 0)):
                row = {z: complex_value(c, kloosterman_terms(c, J, K, z)) for z in units(c)}
                self.assertLessEqual(sum(abs(v) ** 2 for v in projection(c, row, selected).values()), 1e-16)

    def test_composite_cross_residue_occupancy(self):
        for P, R, D, k1, k2 in ((12, 5, 1, 7, 11), (10, 10, 3, 7, 11)):
            for c in range(P + 1, 2 * P + 1):
                counts = defaultdict(int)
                for q in range(R + 1, 2 * R + 1):
                    if gcd(D * q * k2, c) == 1:
                        counts[D * inv(q * k2, c) % c] += 1
                self.assertLessEqual(max(counts.values(), default=0), 1 + Rat(R, P))
            for q in range(R + 1, 2 * R + 1):
                counts = defaultdict(int)
                for c in range(P + 1, 2 * P + 1):
                    if gcd(D * c * k1, q) == 1:
                        counts[-D * inv(c * k1, q) % q] += 1
                self.assertLessEqual(max(counts.values(), default=0), 1 + Rat(P, R))

    def test_frequency_averaged_pair_cauchy_sanity(self):
        for g in (3, 6, 10):
            left = [complex(n % 3 - 1, n % 5 - 2) for n in range(g)]
            right = [complex(n % 4 - 2, n % 7 - 3) for n in range(g)]
            direct = abs(sum(a * b.conjugate() * complex_value(g, [(n * n, Rat(1))])
                             for n, (a, b) in enumerate(zip(left, right))) / g) ** 2
            bound = sum(abs(a) ** 2 for a in left) * sum(abs(b) ** 2 for b in right) / (g * g)
            self.assertLessEqual(direct, bound + 1e-10)

    def test_extreme_exponent_accounts_for_g_sum(self):
        gamma, P, R, N = Rat(1), Rat(2), Rat(3, 2), Rat(3)
        EL = gamma + P + max(N, gamma + 2 * P) + N
        ES = gamma + R + max(N, gamma + 2 * R) + N
        pair = (EL + ES + P - R) / 2
        self.assertEqual((EL, ES, pair, pair + gamma), (11, Rat(19, 2), Rat(21, 2), Rat(23, 2)))

    def test_near_primitive_polytope_exponent_identity(self):
        cells = 0
        for gamma, d1, d2, k1, k2 in product(
                (Rat(0), Rat(1, 2), Rat(1)), (Rat(0), Rat(1, 4), Rat(1, 2)),
                (Rat(0), Rat(1, 4), Rat(1, 2)), (Rat(0), Rat(1, 6), Rat(1, 3)),
                (Rat(0), Rat(1, 6), Rat(1, 3))):
            s1, s2 = 3 - d1 - gamma - k1, 3 - d2 - gamma - k2
            if s1 < s2 or s1 <= Rat(2, 3) * (3 - d1 - gamma) or s2 <= Rat(2, 3) * (3 - d2 - gamma):
                continue
            self.assertGreater(gamma + 2 * s1, 3)
            self.assertGreater(gamma + 2 * s2, 3)
            E1 = gamma + s1 + max(3, gamma + 2 * s1) + 3
            E2 = gamma + s2 + max(3, gamma + 2 * s2) + 3
            full = (E1 + E2 + s1 - s2) / 2 + gamma
            self.assertEqual(full, 12 - 2 * d1 - d2 - 2 * k1 - k2)
            self.assertLessEqual(full, 12)
            cells += 1
        self.assertGreater(cells, 100)

    def test_inactive_and_genuine_gcd_weights_are_distinct(self):
        self.assertNotEqual(sum(Rat(1, phi(k)) for k in range(1, 20)), Rat(19))
        # A uniform extra genuine-gcd row count is not inverse-totient weighted.
        count, atom_bound = 7, Rat(3)
        self.assertEqual((count * atom_bound) ** 2, count ** 2 * atom_bound ** 2)


if __name__ == "__main__":
    unittest.main()
