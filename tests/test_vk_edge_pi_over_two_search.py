import cmath
import math
import unittest

from experiments.pnt.vk_edge_pi_over_two_search import (
    Spectrum,
    deterministic_search,
    estimate_sup_norm,
    fejer_sign_cos_normalized,
    finite_spectrum_kappa_lower_bound,
    missing_odd_dual_certificate,
    normalized_spectrum,
    sign_cos_truncation,
)


class SpectrumNormalizationTests(unittest.TestCase):
    def test_equal_frequencies_are_combined_before_normalization(self) -> None:
        spectrum = Spectrum(
            frequencies=(2.0, 3.0, 2.0),
            coefficients=(1.0 + 1.0j, 0.5j, 2.0 - 1.0j),
        ).combined()

        self.assertEqual(spectrum.frequencies, (2.0, 3.0))
        self.assertEqual(spectrum.coefficients, (3.0 + 0.0j, 0.5j))

    def test_normalization_preserves_the_polynomial_up_to_shift_and_scale(
        self,
    ) -> None:
        original = Spectrum(
            frequencies=(2.0, 5.0),
            coefficients=(2.0j, 1.0 - 0.5j),
        )
        normalized, shift, scale = normalized_spectrum(original, 2.0)

        self.assertEqual(normalized.frequencies[0], 1.0)
        self.assertAlmostEqual(normalized.coefficients[0].real, 1.0)
        self.assertAlmostEqual(normalized.coefficients[0].imag, 0.0)

        for z in (0.0, 0.25, 1.5, 4.0):
            original_y = z / 2.0 + shift
            self.assertAlmostEqual(
                normalized.value(z),
                original.value(original_y) / scale,
                places=12,
            )

    def test_invalid_distinguished_coefficient_is_rejected(self) -> None:
        spectrum = Spectrum((1.0, 2.0), (0.0j, 1.0 + 0.0j))
        with self.assertRaisesRegex(ValueError, "nonzero"):
            normalized_spectrum(spectrum, 1.0)


class SupNormEstimatorTests(unittest.TestCase):
    def test_single_frequency_norm_is_two(self) -> None:
        spectrum = Spectrum((1.0,), (1.0 + 0.0j,))
        estimate = estimate_sup_norm(
            spectrum,
            interval_start=0.0,
            interval_end=2.0 * math.pi,
            samples=4097,
        )

        self.assertAlmostEqual(estimate.value, 2.0, places=12)
        self.assertAlmostEqual(estimate.location, 0.0, places=12)

    def test_two_term_sign_cos_truncation_exceeds_pi_over_two(self) -> None:
        spectrum = sign_cos_truncation(2)
        estimate = estimate_sup_norm(
            spectrum,
            interval_start=0.0,
            interval_end=2.0 * math.pi,
            samples=65537,
        )

        self.assertEqual(spectrum.frequencies, (1.0, 3.0))
        self.assertEqual(spectrum.coefficients, (1.0 + 0.0j, -1.0 / 3.0))
        self.assertGreater(estimate.value, math.pi / 2.0)
        self.assertAlmostEqual(
            estimate.value,
            8.0 / (3.0 * math.sqrt(2.0)),
            places=7,
        )

    def test_near_collision_is_sampled_without_frequency_merging(self) -> None:
        epsilon = 1.0e-6
        spectrum = Spectrum(
            (1.0, 1.0 + epsilon),
            (1.0 + 0.0j, -0.25 + 0.5j),
        ).combined()

        self.assertEqual(len(spectrum.frequencies), 2)
        self.assertEqual(spectrum.frequencies[1], 1.0 + epsilon)
        self.assertTrue(math.isfinite(spectrum.value(1234.5)))


class DeterministicSearchTests(unittest.TestCase):
    def test_search_is_reproducible(self) -> None:
        first = deterministic_search(
            max_terms=3,
            trials=8,
            seed=20260724,
            interval_end=64.0,
            samples=2049,
        )
        second = deterministic_search(
            max_terms=3,
            trials=8,
            seed=20260724,
            interval_end=64.0,
            samples=2049,
        )

        self.assertEqual(first, second)
        self.assertGreaterEqual(first.estimate.value, math.pi / 2.0 - 0.1)
        self.assertEqual(first.seed, 20260724)

    def test_search_includes_normalized_fejer_candidates(self) -> None:
        max_terms = 6
        result = deterministic_search(
            max_terms=max_terms,
            trials=0,
            seed=20260724,
            interval_end=2.0 * math.pi,
            samples=32769,
        )
        fejer_upper_bound = math.pi * max_terms / (2.0 * max_terms - 1.0)

        self.assertLessEqual(result.estimate.value, fejer_upper_bound + 1.0e-10)

    def test_value_matches_direct_complex_evaluation(self) -> None:
        spectrum = Spectrum(
            (1.0, math.sqrt(2.0)),
            (1.0 + 0.0j, 0.25 - 0.75j),
        )
        y = 0.75
        direct = 2.0 * (
            cmath.exp(1.0j * y)
            + (0.25 - 0.75j) * cmath.exp(1.0j * math.sqrt(2.0) * y)
        ).real

        self.assertAlmostEqual(spectrum.value(y), direct, places=14)


class AnalyticLowerBoundTests(unittest.TestCase):
    def test_missing_odd_dual_certificate_is_strict(self) -> None:
        for odd_harmonic in (1, 3, 5, 11):
            certificate = missing_odd_dual_certificate(odd_harmonic)

            self.assertLess(certificate.l1_upper_bound, 2.0 / math.pi)
            self.assertGreater(certificate.norm_lower_bound, math.pi / 2.0)

    def test_missing_odd_dual_certificate_bounds_sampled_l1_norm(self) -> None:
        samples = 262144
        for odd_harmonic in (1, 3, 5, 11):
            certificate = missing_odd_dual_certificate(odd_harmonic)
            sampled_mean = sum(
                abs(
                    math.cos(2.0 * math.pi * index / samples)
                    + certificate.auxiliary_coefficient
                    * math.cos(
                        odd_harmonic * 2.0 * math.pi * index / samples
                    )
                )
                for index in range(samples)
            ) / samples

            self.assertLessEqual(
                sampled_mean,
                certificate.l1_upper_bound + 1.0e-10,
            )

    def test_missing_odd_dual_certificate_rejects_nonodd_harmonic(self) -> None:
        for invalid in (-1, 0, 2, 4):
            with self.assertRaisesRegex(ValueError, "positive odd"):
                missing_odd_dual_certificate(invalid)

    def test_fixed_term_bound_is_strictly_above_pi_over_two(self) -> None:
        for max_terms in range(1, 21):
            self.assertGreater(
                finite_spectrum_kappa_lower_bound(max_terms),
                math.pi / 2.0,
            )

    def test_bound_weakens_monotonically_with_term_budget(self) -> None:
        values = [
            finite_spectrum_kappa_lower_bound(max_terms)
            for max_terms in range(1, 21)
        ]
        self.assertTrue(
            all(left > right for left, right in zip(values, values[1:]))
        )

    def test_two_term_bound_is_consistent_with_sqrt_three_candidate(self) -> None:
        self.assertLess(
            finite_spectrum_kappa_lower_bound(2),
            math.sqrt(3.0),
        )

    def test_nonpositive_term_budget_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "positive"):
            finite_spectrum_kappa_lower_bound(0)

    def test_fejer_family_shows_no_gap_uniform_in_term_budget(self) -> None:
        for max_terms in (1, 2, 4, 8):
            spectrum = fejer_sign_cos_normalized(max_terms)
            estimate = estimate_sup_norm(
                spectrum,
                interval_start=0.0,
                interval_end=2.0 * math.pi,
                samples=32769,
            )
            upper_bound = math.pi * max_terms / (2.0 * max_terms - 1.0)

            self.assertEqual(len(spectrum.frequencies), max_terms)
            self.assertEqual(spectrum.coefficients[0], 1.0 + 0.0j)
            self.assertLessEqual(estimate.value, upper_bound + 1.0e-10)


if __name__ == "__main__":
    unittest.main()
