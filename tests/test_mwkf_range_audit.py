import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mwkf_ranges import (
    ExponentBox,
    admissibility_violations,
    boundary_witnesses,
    derived_bounds,
    is_admissible,
)

NOTE = Path("docs/research/2026-08-24-mobius-weighted-off-diagonal.md")


def test_balanced_maximal_third_variable_box() -> None:
    box = ExponentBox(
        rho=F(3), sigma=F(3), m=F(1, 2), k=F(1, 2),
        ell=F(5, 2), h=F(5, 2), kappa=F(0),
    )
    assert box.third_length == F(5)
    assert admissibility_violations(box) == ()
    assert is_admissible(box)


def test_unbalanced_endpoint_boxes_remain_admissible() -> None:
    witnesses = boundary_witnesses()
    assert set(witnesses) == {
        "balanced_max_a", "r_long", "s_long", "large_q_endpoint"
    }
    assert all(is_admissible(box) for box in witnesses.values())
    assert witnesses["r_long"].third_length == F(4)
    assert witnesses["s_long"].third_length == F(4)
    assert witnesses["large_q_endpoint"].kappa == F(2)


def test_derived_bounds_match_the_written_polytope() -> None:
    for box in boundary_witnesses().values():
        bounds = derived_bounds(box)
        assert bounds["a"] == box.ell + box.h
        assert bounds["a"] <= bounds["a_cap"]
        assert box.m <= bounds["m_cap"]
        assert box.k <= bounds["k_cap"]


def test_balanced_box_exhibits_the_long_a_gap() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert box.third_length == F(5)
    assert (box.rho + box.sigma) / 2 == F(3)
    assert box.third_length - (box.rho + box.sigma) / 2 == F(2)


@pytest.mark.parametrize(
    ("box", "code"),
    [
        (ExponentBox(F(-1), F(1), F(0), F(0), F(0), F(0), F(0)),
         "nonnegative"),
        (ExponentBox(F(3), F(1), F(0), F(2), F(0), F(0), F(1)),
         "mollifier_r"),
        (ExponentBox(F(1), F(3), F(2), F(0), F(0), F(0), F(1)),
         "mollifier_s"),
        (ExponentBox(F(2), F(2), F(1), F(1), F(0), F(0), F(0)),
         "km_length"),
        (ExponentBox(F(2), F(2), F(0), F(1), F(0), F(0), F(0)),
         "ratio_balance"),
        (ExponentBox(F(2), F(2), F(0), F(0), F(2), F(0), F(0)),
         "delta_length"),
        (ExponentBox(F(2), F(2), F(0), F(0), F(0), F(3), F(0)),
         "frequency_length"),
        (ExponentBox(F(2), F(2), F(0), F(0), F(0), F(4), F(0)),
         "third_length"),
    ],
)
def test_each_constraint_has_a_stable_failure_code(
    box: ExponentBox, code: str
) -> None:
    assert code in admissibility_violations(box)
    assert not is_admissible(box)


def test_research_note_exposes_afe_audit_ledger() -> None:
    text = NOTE.read_text()
    for marker in (
        "> **Current proof status.**",
        "### 2.1 Completion and pole cancellation",
        "### 2.2 Absolute convergence and termwise expansion",
        "### 2.3 Uniform weight bounds",
    ):
        assert marker in text
    assert "\\Lambda(s)=\\gamma(s)\\zeta(s)" in text
    assert "\\left(1-4z^2\\right)" in text


def test_research_note_exposes_poisson_audit_ledger() -> None:
    text = NOTE.read_text()
    for marker in (
        "### 4.1 Residue class and Poisson normalization",
        "### 4.2 Zero mode from a common Mellin integral",
        "### 4.3 Residue and main-term normalization",
    ):
        assert marker in text
    assert "zero-mode audit result:" in text
    assert "C_t(z)\\zeta(1-2z)g_t(-z)" in text
    assert "\\mathcal E_{\\rm arch}" in text


def test_research_note_exposes_global_secondary_zero_master_and_ttstar_split() -> None:
    text = NOTE.read_text()
    for marker in (
        "### 9.69 A boundary-exact master for the secondary zero modes",
        "\\mathcal R^{(0)}_{\\rm sec}=\\mathcal M_{\\rm res}"
        "+\\mathcal R_{\\rm cent}",
        "### 9.70 The centered operator gate and the global TT* split",
        "\\det(u,v)=k_u\\ell_v-k_v\\ell_u",
        "required_ttstar_saving_exponent=4",
        "These terms are not literally added:",
        "not construct the analytic adapter from (4.5)",
        "### 9.71 The actual zero-mode projector has rank above product centering",
        "\\det G_T=(1-u^2)^3(1+u^2)",
        "\\operatorname{rank}(K-K^\\circ)\\leq2",
        "### 9.72 Determinant zero means equal primitive slope",
        "(k_u,\\ell_u)=(k_v,\\ell_v)",
        "\\mathfrak G_{\\det=0}(a)=\\sum_{(k,\\ell)=1}",
        "### 9.73 Type expansion does not diagonalize a resonant orbit",
        "a_{\\mathrm{AFE}}=h\\delta",
        "\\xi\\in\\mathbb Z/M\\mathbb Z",
        "\\Delta_{\\rm Type}=r_1s_2-r_2s_1",
        "Q\\Delta_{\\rm Type}=\\rho_1s_2-\\rho_2s_1",
        "-\\mu(s)\\mu(n)v_p(n)",
        "farey_type_ttstar_euclidean_ledger",
        "mobius_log_type_diagonal_recombination",
        "labelled_type_zero_determinant_recombination",
        "\\mathfrak G^{\\rm Type}_{0}",
        "\\mathcal N_{\\ne0}"
        "=\\left(1-\\frac1M\\right)D_{\\rm cont}"
        "+\\mathcal N_{\\ne0}^{\\rm off}",
        "\\Delta_{\\rm Type}\\ne0",
        "does not prove or remove the global same-slope gate",
        "No Type-I/II estimate is proved by these identities",
    ):
        assert marker in text


def test_research_note_records_product_trace_completion_and_rank_one_boundary() -> None:
    text = NOTE.read_text()
    for marker in (
        "### 9.78 Product-trace completion and the rank-one theorem boundary",
        r"\widehat K(h)=S(B-h,C;q)",
        r"=\frac1q\sum_{h\bmod q}S(B-h,C;q)A(h)",
        "Cauchy--Parseval gives no power saving",
        "Theorem 1.3(2) does not directly apply",
        r"\eta_{\rm FKMS,route}(1,14)=\frac1{224}",
        r"\dim\mathcal E_m\geq4m-1>3m",
        "rank-one Type-II pole stratification fails",
        "formal substitution, not a currently valid route",
        "proved-coverage column",
        "composite central band remain unproved",
        "### 9.79 Squarefree CRT transfer and its sharp cofactor cost",
        r"K_{qr}(x)=K_q^{(r)}(x)K_r^{(q)}(x)",
        r"\frac1{\varphi(r)}\sum_{\chi\bmod r}",
        r"\sum_{\chi\bmod r}|w_\chi|^2=1",
        "product-incidence energy",
        r"\varphi(r)\sum_{u\in U(r)}|C_u|^2",
        r"r^{1/2}q^{-\kappa}",
        r"\lambda>\frac{\sigma}{1+2\kappa}",
        r"\lambda>\frac45\sigma",
        r"\eta_{\rm CRT}(9/10)=\frac{9}{80}",
        r"=\kappa\sigma.",
        "squarefree_prime_factor_polytope_audit",
        "half-power coupled gate",
        "### 9.80 Exact rank-one resonance subtraction",
        r"R(\rho)=\sum_{j:r_j=\rho}R_j",
        "finite-value alias",
        r"\dim\mathcal E_{m,\mathcal P}\geq4m-1",
        r"\operatorname{RSCCG}_3",
        "signed resonant projector",
        "exhaustive implication",
        "### 9.81 Zero dual frequency of the resonant projector",
        r"\mathfrak R_{\mathcal P}^{(0)}",
        "rank_one_resonance_orthogonality_audit",
        "global principal evaluation",
        "centered operator estimate",
        "### 9.82 Pre-Poisson product-incidence orthogonality",
        r"e_q\!\left(-\overline r_qh\delta",
        r"Q=\frac qg",
        r"x_1\equiv x_2\pmod{rg},\qquad rg=s/Q",
        r"\mathcal S_Q(f,g)",
        r"\eta_{h\delta}(\lambda)",
        "half-power on this isolated",
        "alternative ordering of (9.493)",
        "unequal-label Gram",
        "hdelta_product_incidence_fourier_audit",
        "low-conductor incidence estimate",
        "smooth packet adapter",
    ):
        assert marker in text


def test_research_note_has_one_honest_phase_one_classification() -> None:
    text = NOTE.read_text()
    labels = (
        "Phase-1 classification: exact reduction verified",
        "Phase-1 classification: corrected reduction verified",
        "Phase-1 classification: exact reduction remains blocked",
        "Current classification: published coverage complete; Region D remains",
        "Current classification: published/elementary coverage complete; Region D remains",
        "Current classification: Young closes each fixed scalar stratum",
    )
    assert sum(label in text for label in labels) == 1
    assert "Accepted local gate after exact audit:" in text
    assert "arXiv:2601.00292" in text
    assert "withdrawn" in text.lower()
