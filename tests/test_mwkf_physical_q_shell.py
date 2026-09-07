"""Scale adapter guards: original nonempty boxes, F!=J, and q harmonic mass."""

from fractions import Fraction as F
from math import ceil, exp, pi

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.audit_mwkf_ranges import ExponentBox, admissibility_violations, is_admissible
from scripts.mwkf_mobius_type_identity import mobius


@pytest.mark.parametrize("M,want", [(128, (16, 1, -1)), (192, (24, F(2, 3), F(-4, 9)))])
def test_unbalanced_scale_retains_distinct_j_and_n_lengths(M, want):
    row = pt.all_scale_critical_parameters(512, 256, 4, 8, M, 3, 5, -120, 4, 8)
    assert (row["alpha"], row["X"], row["Z"], row["J"], row["F"], row["n_scale"]) == (2, 128, 16, 4, 8, 120)
    assert tuple(row[key] for key in ("z0", "eta", "sigma")) == want


def test_original_mollifier_support_rejects_previous_positive_q_top_scale_examples():
    for gamma in (F(1, 5), F(1, 2)):
        assert admissibility_violations(ExponentBox(F(3), F(3), F(1, 2), F(1, 2), F(5, 2), F(5, 2), gamma)) == ("mollifier_r", "mollifier_s")
    row = pt.physical_q_shell_exponents(F(1, 5), 1, F(1, 2), F(3, 5))
    assert is_admissible(ExponentBox(*row["original_exponents"]))


@pytest.mark.parametrize("gamma,nu,u,beta,want", [
    (F(1, 5), 1, F(1, 2), F(3, 5), (F(14, 5), F(29, 10), F(12, 5), F(14, 5), 1)),
    (F(1, 5), 1, 0, F(6, 5), (F(14, 5), F(19, 5), F(14, 5), F(13, 5), 1)),
    (F(1, 2), 1, 0, 1, (F(5, 2), F(7, 2), F(5, 2), F(5, 2), 1)),
    (F(1, 5), 1, F(1, 2), F(4, 5), (F(14, 5), F(16, 5), F(27, 10), F(29, 10), F(11, 10))),
])
def test_entire_q_shell_pays_smaller_S_budget_without_an_extra_Q_count(gamma, nu, u, beta, want):
    row = pt.physical_q_shell_exponents(gamma, nu, u, beta)
    errors = row["bounds"]
    assert (row["target"], errors["uncompleted_error"], errors["interval_error"], errors["integer_error"], row["physical_error"]) == want
    assert is_admissible(ExponentBox(*row["original_exponents"]))
    assert row["physical_density"] == row["physical_resonance"] == 1
    assert "covered" not in row


@pytest.mark.parametrize("nu,u,beta,chi", [(1, F(1, 2), 1, 0), (F(4, 5), 0, F(6, 5), F(1, 5))])
def test_all_scale_ledger_reduces_to_general_q_ledger_only_when_R_equals_S(nu, u, beta, chi):
    row = pt.all_scale_error_exponents(3, 3, 5, nu, u, 1-u, beta, chi)
    old = pt.all_e_q_error_exponents(nu, u, beta, chi)
    assert {key: row[key] for key in old} == old
    assert row["resonance"] == 3


def test_unbalanced_integer_sampling_and_resonance_both_pay_alpha():
    row = pt.all_scale_error_exponents(3, F(5, 2), F(9, 2), F(4, 5), 0, F(1, 2), F(1, 10), 0)
    assert row == {"density": F(2), "resonance": F(5, 2), "uncompleted_error": F(21, 10),
                   "interval_error": F(8, 5), "integer_error": F(5, 2), "best_error": F(21, 10)}


def test_actual_q_shell_interior_keeps_every_q_away_from_mollifier_endpoint():
    N, Q = 512, 8
    R = F(N, 8*Q)
    assert all(q*r <= N/2 for q in range(Q, 2*Q) for r in range(ceil(R/2), int(2*R)+1))
    assert sum(F(mobius(q)**2, q) for q in range(Q, 2*Q)) <= 1


def test_unbalanced_primitive_completion_uses_F_not_J_for_Jacobian_and_argument():
    R, S, K, P, M, B, v, j, kl = 14, 7, 2, 3, 7, 5, 1, 2, 3
    scales = pt.all_scale_critical_parameters(R, S, K, P, M, B, v, 1, j, kl)
    freq = scales["F"]
    assert (scales["J"], freq) == (3, 6)
    N = ceil(8*B*freq)
    weight = lambda m, b, n: float(n/(B*freq))**2*exp(-pi*float(n/(B*freq))**2)
    row = pt.global_e_q_packet(M, B, 1, j, 1, kl, tuple(n for n in range(-N, N+1) if n), weight)
    hs = pt.primitive_band_rows(M, B, j, kl, 8/freq)
    rhs = freq*F(mobius(M)*mobius(B), M*abs(j))*sum(
        (1/(2*pi)-float(freq*f)**2)*exp(-pi*float(freq*f)**2) for _, _, f in hs)
    assert row["fused"] == pytest.approx(rhs, abs=2e-10)


@pytest.mark.parametrize("call", [
    lambda: pt.all_scale_critical_parameters(14, 0, 2, 3, 7, 5, 1, 1, 2, 3),
    lambda: pt.all_scale_critical_parameters(14, 7, 2, 3, 7, 5, 0, 1, 2, 3),
    lambda: pt.all_scale_critical_parameters(14, 7, 2, 3, 7, 5, 1, 0, 2, 3),
    lambda: pt.all_scale_error_exponents(3, 2, 4, 1, 0, 0, 1, 0),
    lambda: pt.all_scale_error_exponents(2, 3, 4, 1, 0, 1, 1, 0),
    lambda: pt.all_scale_error_exponents(3, 3, 5, 0, 0, 1, 1, 0),
    lambda: pt.physical_q_shell_exponents(F(14, 5), F(1, 10), F(1, 2), 0),
    lambda: pt.physical_q_shell_exponents(F(1, 5), 1, F(3, 4), 1),
    lambda: pt.physical_q_shell_exponents(F(1, 5), 1, 0, 3),
])
def test_invalid_endpoint_or_nonempty_core_hypotheses_are_rejected(call):
    with pytest.raises(ValueError):
        call()
