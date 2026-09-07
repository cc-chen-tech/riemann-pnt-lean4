#!/usr/bin/env python3
"""Exact finite guards for CS1--CS17; not a PV/large-sieve or zero-free proof."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm
from pathlib import Path
import unittest

from check_physical_large_gcd_type_columns import mobius, phi, root_normal_form, units
from check_physical_squarefree_type_descent import divisors


def prime_factors(q):
    return [p for p in divisors(q) if p > 1
            and all(p % d for d in range(2, int(p**0.5) + 1))]


def characters(q):
    """A character is its exact root-of-unity phase on units, None elsewhere."""
    ps = prime_factors(q)
    logs = {}
    for p in ps:
        gen = next(g for g in range(1, p)
                   if len({pow(g, j, p) for j in range(p-1)}) == p-1)
        logs[p] = {pow(gen, j, p): j for j in range(p-1)}
    result = []
    for js in product(*(range(p-1) for p in ps)):
        ell = 1
        for p, j in zip(ps, js):
            if j:
                ell *= p
        phases = {
            n: sum((F(j*logs[p][n % p], p-1) for p, j in zip(ps, js)), F(0)) % 1
            for n in units(q)
        }
        result.append((ell, phases))
    return result


def root_value(terms):
    """Normalize rational-phase sums exactly in a cyclotomic quotient."""
    order = 1
    for phase, _ in terms:
        order = lcm(order, F(phase).denominator)
    return root_normal_form(order, [(int(F(z)*order), F(a)) for z, a in terms])


def roots_equal(left, right):
    return root_value(left + [(z, -a) for z, a in right]) == root_value([])


def centered_exponents(eta):
    z = (5-2*eta)/3
    return {
        "Z": z, "Q": 3-eta,
        "high": 3-eta-z/2, "low": eta-2+F(5, 2)*z,
        "mixed1": 2-eta, "mixed2": 3-F(3, 2)*eta,
        "last": F(7, 2)-2*eta, "principal": 3-eta,
    }


class CenteredConductorChecks(unittest.TestCase):
    def test_joint_hard_edge_has_no_uniform_c1_bound(self):
        # After e=fa the endpoint moves with a; fixed-e BV is not joint C1.
        hard = lambda a, u: int(1 <= a*u <= 2)
        for j in range(3, 15):
            h = F(1, 2**j)
            self.assertEqual(hard(1+h, 1)-hard(1-h, 1), 1)
            self.assertEqual(F(1, 2*h), 2**(j-1))
        self.assertNotEqual(hard(F(3, 2), F(3, 4)), hard(1, F(3, 4)))

    def test_finite_overlapping_partition_preserves_signed_joint_sum(self):
        # Piecewise-linear surrogate tests the finite algebra, not C6 regularity.
        rho = lambda x: F(1) if x <= 1 else max(F(0), 2-x)
        part = lambda x: rho(x)-rho(2*x)
        scales = [F(2)**j for j in range(-2, 8)]
        total = split = F(0)
        for h, delta in product(range(-9, 10), repeat=2):
            if not h or not delta:
                continue
            weight = F(h-2*delta+h*delta, 37)
            atoms = sum((part(abs(h)/H)*part(abs(delta)/L)
                         for H, L in product(scales, repeat=2)), F(0))
            self.assertEqual(atoms, 1)
            total += weight
            split += weight*atoms
        self.assertEqual(split, total)
        self.assertGreater(part(F(3, 4)), 0)
        self.assertFalse(1 <= F(3, 4) <= 2)  # New packet is not the old hard shell.

    def test_smooth_packet_support_and_sobolev_cost(self):
        for a in (F(1), F(3, 2), F(2)):
            self.assertGreaterEqual(F(1, 2)/a, F(1, 4))
            self.assertLessEqual(2/a, 2)
        self.assertGreater(2*5-4, 5)
        self.assertGreaterEqual(6, 5)

    def test_scope_contract_requires_explicit_smooth_repartition(self):
        note = (Path(__file__).resolve().parents[1]/
                "docs/research/2026-08-31-physical-centered-conductor-split.md").read_text()
        for required in ("CS0.", "一般 literal 硬壳", "\\Psi_{\\rm sm}",
                         "内部整包", "\\mathcal A^{\\rm sm}_J"):
            self.assertIn(required, note)

    def test_ie_mobius_coefficient_including_nonsquarefree(self):
        for f, a, b in product(range(1, 12), repeat=3):
            left = mobius(f)*mobius(f*a)*mobius(f*b)
            right = mobius(f)*mobius(a)*mobius(b) if gcd(a*b, f) == 1 else 0
            self.assertEqual(left, right)

    def test_complete_ie_preserves_actual_joint_weight_and_phase(self):
        for q in (1, 2, 3, 5, 6, 10, 15):
            actual, expanded = [], []
            for e, n in product(range(1, 9), range(1, 10)):
                if gcd(e*n, 7*q) > 1:
                    continue
                for u, v in product((-2, -1, 1, 2), repeat=2):
                    if gcd(u*v, q) > 1:
                        continue
                    weight = F(3*n+e*u+2*v+q, (n+2)*(e+3))
                    if gcd(e, n) == 1:
                        actual.append((F(-e*u*v*pow(n, -1, q), q),
                                       mobius(q)*mobius(e)*mobius(n)*weight))
                    for f in divisors(gcd(e, n)):
                        a, b = e//f, n//f
                        if gcd(a*b, f) == 1:
                            expanded.append((F(-a*u*v*pow(b, -1, q), q),
                                             mobius(q)*mobius(f)*mobius(a)*mobius(b)*weight))
            self.assertTrue(roots_equal(actual, expanded))

    def test_readding_ab_coprimality_breaks_ie(self):
        e = n = 2
        correct = sum(mobius(f) for f in divisors(gcd(e, n)))
        wrong = sum(mobius(f) for f in divisors(gcd(e, n))
                    if gcd(e//f, n//f) == 1)
        self.assertEqual(correct, 0)
        self.assertEqual(wrong, -1)

    def test_five_variable_actual_weight_coordinates(self):
        R, E, Q, S, H, L = map(F, (101, 15, 17, 255, 61, 67))
        for f in (1, 3, 5):
            A, B, U, V = E/f, R/f, H/E, L/E
            a, b, q, u, v = map(F, (7, 19, 13, -2, 3))
            self.assertEqual(
                (f*b/R, f*a*q/S, f*a*v/L, f*a*u/H),
                (b/B, E*Q/S*(a/A)*(q/Q), (a/A)*(v/V), (a/A)*(u/U)))

    def test_weighted_five_dimensional_sobolev_threshold(self):
        self.assertFalse(2*F(9, 2)-4 > 5)
        self.assertTrue(2*F(5)-4 > 5)
        self.assertTrue(2*F(6)-4 > 5)
        # Pointwise order-six decay with two BV powers would NOT suffice.
        self.assertFalse(6-2 > 5)

    def test_character_count_and_unique_primitive_conductor(self):
        for q in (1, 2, 3, 5, 6, 10, 15, 21, 30, 35):
            chars = characters(q)
            self.assertEqual(len(chars), phi(q))
            self.assertEqual(sum(ell == 1 for ell, _ in chars), 1)
            for ell, phase in chars:
                self.assertEqual(q % ell, 0)
                self.assertEqual(gcd(ell, q//ell), 1)
                self.assertNotEqual(ell, 2)
                for x, y in product(units(q), repeat=2):
                    self.assertEqual(phase[x*y % q], (phase[x]+phase[y]) % 1)

    def test_induced_gauss_and_original_mu_fusion_exact(self):
        for q in (2, 3, 5, 6, 10, 15, 21, 30, 35):
            for ell, ambient in characters(q):
                if ell == 1:
                    continue
                c = q//ell
                small = {x % ell: phase for x, phase in ambient.items()}
                direct = [(F(x, q)-phase, F(mobius(q)))
                          for x, phase in ambient.items()]
                reduced = [(F(x, ell)-small[x]-small[c % ell], F(mobius(ell)))
                           for x in units(ell)]
                self.assertTrue(roots_equal(direct, reduced), (q, ell))

    def test_complete_centered_character_expansion_exact(self):
        for q in (1, 2, 3, 5, 6, 10, 15, 21, 30, 35):
            for z in units(q)[:4]:
                actual = [(F(z, q), F(1)), (F(0), -F(mobius(q), phi(q)))]
                expanded = [
                    (F(x, q)-phase[x]+phase[z], F(1, phi(q)))
                    for ell, phase in characters(q) if ell > 1 for x in units(q)
                ]
                self.assertTrue(roots_equal(actual, expanded), (q, z))

    def test_conductor_one_center_is_not_original_principal(self):
        for q in (1, 2):
            z = units(q)[0]
            actual = [(F(z, q), F(1))]
            principal = [(F(0), F(mobius(q), phi(q)))]
            self.assertTrue(roots_equal(actual, principal))
            self.assertFalse(roots_equal(actual, []))

    def test_pv_unit_mask_ie_including_negative_labels(self):
        for ell in (3, 5, 7):
            for conductor, phases in characters(ell):
                if conductor == 1:
                    continue
                for c in (1, 2, 11):
                    actual, expanded = [], []
                    for u in range(-12, 13):
                        if not u or gcd(u, ell) > 1:
                            continue
                        w = F(u+2, abs(u)+3)
                        if gcd(u, c) == 1:
                            actual.append((phases[u % ell], w))
                        for j in divisors(c):
                            if u % j == 0:
                                expanded.append((phases[j % ell]+phases[(u//j) % ell],
                                                 mobius(j)*w))
                    self.assertTrue(roots_equal(actual, expanded))

    def test_common_product_coefficients_keep_c_masks(self):
        for c in (1, 2, 5):
            coeff = defaultdict(F)
            for a in range(1, 8):
                for u, v in product((-3, -2, -1, 1, 2, 3), repeat=2):
                    if gcd(a, 7*c) == 1 and gcd(u*v, c) == 1:
                        coeff[a*u*v] += F(mobius(a), (a+1)*(abs(u)+1)*(abs(v)+1))
            for ell in (3, 11):
                for _, phases in characters(ell):
                    product_side = [(phases[m % ell], x) for m, x in coeff.items()
                                    if gcd(m, ell) == 1]
                    original = [
                        (phases[a % ell]+phases[u % ell]+phases[v % ell],
                         F(mobius(a), (a+1)*(abs(u)+1)*(abs(v)+1)))
                        for a in range(1, 8)
                        for u, v in product((-3, -2, -1, 1, 2, 3), repeat=2)
                        if gcd(a, 7*c) == 1 and gcd(u*v, c) == 1 and gcd(a*u*v, ell) == 1
                    ]
                    self.assertTrue(roots_equal(product_side, original))

    def test_triple_integer_product_energy(self):
        for A, U, V in product((F(1, 2), F(1), F(2)), repeat=3):
            counts = defaultdict(int)
            for a in range(1, int(2*A)+1):
                for u in range(-int(2*U), int(2*U)+1):
                    for v in range(-int(2*V), int(2*V)+1):
                        if u*v:
                            counts[a*u*v] += 1
            K = A*U*V
            self.assertLessEqual(sum(counts.values()), 32*K)
            tau3 = lambda m: sum(len(divisors(m//d)) for d in divisors(m))
            for m, count in counts.items():
                self.assertLessEqual(count, 2*tau3(abs(m)))
                self.assertLessEqual(abs(m), 8*K)
            capacity = max(tau3(m) for m in range(1, int(8*K)+1))
            self.assertLessEqual(sum(x*x for x in counts.values()), 64*K*capacity)

    def test_high_conductor_full_square_no_length_assumption(self):
        for B, K, Q, c in product((F(1, 2), F(2), F(9)), repeat=4):
            full = B*K*(B+Q*Q/(c*c))*(K+Q*Q/(c*c))/(c*Q)
            exact = (B*K)**2/(c*Q)+B*K*(B+K)*Q/c**3+B*K*Q**3/c**5
            self.assertEqual(full, exact)
            self.assertGreater(full, (B*K)**2/(c*Q))

    def test_all_f_powers_in_high_terms(self):
        R, K0, Q = map(F, (91, 35, 17))
        for f in range(1, 21):
            B, K = R/f, K0/f
            self.assertEqual(B*K, R*K0/f**2)
            self.assertEqual(Q*B*B*K, Q*R*R*K0/f**3)
            self.assertEqual(Q*K*K*B, Q*K0*K0*R/f**3)
            self.assertEqual(Q**3*B*K, Q**3*R*K0/f**2)

    def test_low_conductor_character_count_and_f_cost(self):
        for ell in (3, 5, 6, 10, 15):
            self.assertLessEqual(sum(d == ell for d, _ in characters(ell)), phi(ell))
        E, R = F(19), F(91)
        for f in range(1, 20):
            self.assertEqual((E/f)*(R/f), E*R/f**2)
        self.assertEqual(F(1, 2)+1+1, F(5, 2))

    def test_balanced_threshold_and_remaining_principal(self):
        for eta in (F(3, 2), F(7, 4), F(19, 10), F(2), F(5, 2)):
            ex = centered_exponents(eta)
            self.assertEqual(ex["high"], ex["low"])
            self.assertEqual(ex["high"], F(13, 6)-F(2, 3)*eta)
            self.assertTrue(0 <= ex["Z"] <= ex["Q"])
            self.assertGreaterEqual(ex["high"], max(ex[k] for k in ("mixed1", "mixed2", "last")))
        self.assertEqual(centered_exponents(F(7, 4))["high"], 1)
        at19 = centered_exponents(F(19, 10))
        self.assertEqual((at19["high"], at19["principal"]), (F(9, 10), F(11, 10)))
        self.assertGreater(at19["principal"], 1)

    def test_actual_asymptotic_support_exponents(self):
        e, q = F(19), F(11)
        S = e+q
        T = S/3
        H = S-T/2
        self.assertEqual((T, e/T, H-e), (10, F(19, 10), 6))
        self.assertLess(H-e, q)
        self.assertEqual(2*H, 2*S-T)

    def test_research_files_have_no_hidden_control_bytes(self):
        root = Path(__file__).resolve().parents[1]
        paths = [Path(__file__), root/"docs/research/2026-08-31-physical-centered-conductor-split.md"]
        for path in paths:
            bad = [(i, x) for i, x in enumerate(path.read_bytes())
                   if (x < 32 and x not in (9, 10)) or x == 127]
            self.assertEqual(bad, [], str(path))


if __name__ == "__main__":
    unittest.main()
