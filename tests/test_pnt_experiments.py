import math

from experiments.pnt import pnt_experiments as pnt


def test_prime_and_chebyshev_counts_are_exact_for_small_inputs():
    assert pnt.primes_up_to(30) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert pnt.prime_count(30) == 10

    theta_10 = math.log(2) + math.log(3) + math.log(5) + math.log(7)
    psi_10 = math.log(2) * 3 + math.log(3) * 2 + math.log(5) + math.log(7)

    assert math.isclose(pnt.chebyshev_theta(10), theta_10, rel_tol=0, abs_tol=1e-12)
    assert math.isclose(pnt.chebyshev_psi(10), psi_10, rel_tol=0, abs_tol=1e-12)


def test_log_integral_and_sample_row_expose_pnt_error_terms():
    li_100 = pnt.log_integral(100)
    assert 29.0 < li_100 < 31.0

    row = pnt.sample_row(100)

    assert row.x == 100
    assert row.pi_x == 25
    assert row.theta_x > 0
    assert row.psi_x > 0
    assert row.li_x == li_100
    assert math.isclose(row.psi_error, row.psi_x - row.x, rel_tol=0, abs_tol=1e-12)
    assert math.isclose(row.pi_minus_li, row.pi_x - row.li_x, rel_tol=0, abs_tol=1e-12)


def test_generate_dataset_uses_increasing_integer_sample_points():
    rows = pnt.generate_dataset(start=10, stop=100, points=5)

    assert [row.x for row in rows] == sorted({row.x for row in rows})
    assert rows[0].x == 10
    assert rows[-1].x == 100
    assert all(row.psi_x >= row.theta_x for row in rows)

