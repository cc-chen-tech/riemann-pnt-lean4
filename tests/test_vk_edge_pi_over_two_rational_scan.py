import math
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from experiments.pnt.vk_edge_pi_over_two_rational_scan import (
    derivative_bound,
    mesh_enclosure,
    optimize_two_term_rational,
    rational_period,
)
from experiments.pnt.vk_edge_pi_over_two_search import Spectrum


class RationalPeriodTests(unittest.TestCase):
    def test_common_period_uses_denominator_lcm(self) -> None:
        period = rational_period(
            (Fraction(1), Fraction(3, 2), Fraction(5, 6))
        )
        self.assertAlmostEqual(period, 12.0 * math.pi, places=12)

    def test_derivative_bound_is_coefficient_weighted(self) -> None:
        spectrum = Spectrum(
            (1.0, 3.0),
            (1.0 + 0.0j, -1.0 / 3.0),
        )
        self.assertAlmostEqual(derivative_bound(spectrum), 4.0, places=12)


class MeshEnclosureTests(unittest.TestCase):
    def test_single_frequency_enclosure_contains_exact_norm(self) -> None:
        spectrum = Spectrum((1.0,), (1.0 + 0.0j,))
        enclosure = mesh_enclosure(
            spectrum,
            period=2.0 * math.pi,
            samples=4097,
        )

        self.assertLessEqual(enclosure.lower, 2.0)
        self.assertGreaterEqual(enclosure.upper, 2.0)
        self.assertLess(enclosure.upper - enclosure.lower, 0.002)


class TwoTermOptimizationTests(unittest.TestCase):
    def test_third_harmonic_finds_classical_flattening_coefficient(self) -> None:
        candidate = optimize_two_term_rational(
            Fraction(3),
            coefficient_radius=0.75,
            grid_steps=25,
            refinements=4,
            samples=8193,
        )

        self.assertAlmostEqual(candidate.coefficient.real, -1.0 / 6.0, delta=0.01)
        self.assertAlmostEqual(candidate.coefficient.imag, 0.0, delta=0.01)
        self.assertAlmostEqual(
            candidate.enclosure.lower,
            math.sqrt(3.0),
            delta=0.002,
        )
        self.assertGreater(candidate.enclosure.lower, math.pi / 2.0)

    def test_optimizer_is_deterministic_for_rational_frequency(self) -> None:
        first = optimize_two_term_rational(
            Fraction(5, 2),
            coefficient_radius=0.5,
            grid_steps=9,
            refinements=2,
            samples=1025,
        )
        second = optimize_two_term_rational(
            Fraction(5, 2),
            coefficient_radius=0.5,
            grid_steps=9,
            refinements=2,
            samples=1025,
        )
        self.assertEqual(first, second)

    def test_direct_cli_execution_writes_report(self) -> None:
        script = Path("experiments/pnt/vk_edge_pi_over_two_rational_scan.py")
        with tempfile.TemporaryDirectory() as temporary_directory:
            output = Path(temporary_directory) / "result.json"
            completed = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "--numerator",
                    "3",
                    "--denominator",
                    "1",
                    "--grid-steps",
                    "9",
                    "--refinements",
                    "2",
                    "--samples",
                    "1025",
                    "--output",
                    str(output),
                ],
                check=False,
                capture_output=True,
                text=True,
            )

            self.assertEqual(completed.returncode, 0, completed.stderr)
            self.assertTrue(output.is_file())


if __name__ == "__main__":
    unittest.main()
