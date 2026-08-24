from fractions import Fraction as F
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.mwkf_mobius_type_identity import (
    c_u,
    crt_reciprocity_numerators,
    double_split_mobius_identity,
    mobius,
    split_mobius_identity,
    type_scale_bounds,
)
from scripts.audit_mwkf_coverage import (
    wright_denominator_factor_adapter,
    wright_type_i_adapter,
)
from scripts.audit_mwkf_ranges import boundary_witnesses


TYPE_NOTE = Path("docs/research/2026-08-24-mwkf-mobius-type-i-ii.md")


def test_truncated_divisor_coefficient() -> None:
    assert c_u(1, 3) == 1
    assert c_u(6, 3) == -1  # 1 + mu(2) + mu(3)
    assert c_u(12, 4) == -1  # divisors 1,2,3,4


def test_exact_mobius_type_split_for_all_small_integers() -> None:
    for cutoff in range(1, 9):
        for n in range(cutoff + 1, 80):
            lhs, type_i, type_ii = split_mobius_identity(
                n, cutoff_u=cutoff, cutoff_v=5
            )
            assert lhs == mobius(n)
            assert lhs == -(type_i + type_ii)


def test_exact_double_mobius_split_has_four_sectors() -> None:
    for cutoff in range(1, 6):
        for r in range(cutoff + 1, 30):
            for s in range(cutoff + 1, 30):
                lhs, sectors = double_split_mobius_identity(
                    r,
                    s,
                    cutoff_u=cutoff,
                    cutoff_v=4,
                )
                assert lhs == mobius(r) * mobius(s)
                assert lhs == sum(sectors.values())
                assert set(sectors) == {"I/I", "I/II", "II/I", "II/II"}


def test_squarefree_factorization_gives_exact_common_b_phase() -> None:
    # e(n * bar(s)/(a*b)) splits into characters modulo a and b.
    for a, b, s, n in ((5, 6, 7, 11), (7, 10, 9, -13), (11, 14, 3, 17)):
        inverse, mod_a, mod_b = crt_reciprocity_numerators(
            s=s, a=a, b=b, n=n
        )
        assert (inverse - mod_a - mod_b).denominator == 1


def test_one_third_split_has_exact_balanced_scales() -> None:
    scales = type_scale_bounds(F(3), u=F(1, 3), v=F(1, 3))
    assert scales.u_exp == F(1)
    assert scales.v_exp == F(1)
    assert scales.type_i_a_min == F(2)
    assert scales.type_ii_a_min == F(1)
    assert scales.type_ii_a_max == F(2)
    assert scales.type_ii_b_min == F(1)
    assert scales.type_ii_b_max == F(2)


def test_wright_type_i_fails_on_the_balanced_hard_endpoint() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    result = wright_type_i_adapter(
        box, a_factor=F(2), b_factor=F(1)
    )
    assert not result.applicable
    assert result.reason == "wright_hypotheses_fail"
    assert result.saving == F(-45, 8)


def test_wright_fixed_denominator_factor_still_loses_at_best_endpoint() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    result = wright_denominator_factor_adapter(
        box,
        fixed_factor=F(1),
        remaining_factor=F(2),
    )
    assert not result.applicable
    assert result.reason == "insufficient_saving"
    assert result.saving == F(-5)


def test_type_note_names_both_local_inequalities_and_blocker() -> None:
    text = TYPE_NOTE.read_text()
    for marker in (
        "## 2. Exact Möbius identity",
        "## 3. Reciprocity and exact Type-I/II sums",
        r"TI\(_{1/500}\)",
        r"TII\(_{1/500}\)",
        "## 4.1 Double Möbius split and denominator-factor audit",
        r"\mu^2(ab)=1",
        r"\frac{n_1\overline{s_1a_1}-n_2\overline{s_2a_2}}b",
        r"s_{\rm Wright,den}=-5",
        r"SP\(_b\)",
        "new spectral proposition status: unproved",
    ):
        assert marker in text
    assert "unconditional asymptotic proved" not in text
