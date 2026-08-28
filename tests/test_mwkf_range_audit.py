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
        "relevant resonant/nonzero-direct fixed atoms",
        "signed varying-conductor moment",
        r"jointly in \(s,\xi,h\delta\), and the",
        "low-active/short-product complement remain unproved",
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
        "### 9.83 The full unequal-label CRT character Gram",
        r"\widehat K_{r,a}(\chi)",
        r"\mathcal B_{q,a,\chi}",
        r"\mathcal C_r(a_1,a_2;y)",
        r"a_1\equiv a_2\pmod r",
        "globally coefficient-nonprincipal",
        r"\mathcal C_6=\varphi(6)=2",
        r"\mathcal C_{10}=-4=-\varphi(10)",
        "local-principal aliases",
        "squarefree_crt_unequal_outer_character_gram_audit",
        "coefficient-nonprincipal operator",
        "### 9.84 Prime-by-prime conductor of the cofactor kernel",
        r"g=(A,C,r)",
        r"t_p=\overline q_r\,\overline{(r/p)}_p",
        r"R_{\rm sm}=(R_0,6)",
        r"\varphi(g)R_0^{1/2+\varepsilon}",
        r"a_1\equiv a_2\pmod g",
        "cofactor-conductor operator problem",
        "### 9.85 Exact outer-label Fourier operator and the primitive product spectrum",
        r"\operatorname{Spec}_{\rm sing}(C_y)",
        r"P_r^{\rm prim}",
        r"\mathcal E_r^{\rm prim}(f,g)",
        "primitive_product_residue_energy_audit",
        "primitive_product_spectrum_exponent_audit",
        "one half-power larger than the",
        "analytic primitive-spectrum estimate",
        "### 9.86 A published fourth moment closes the unit-label interval subpacket",
        r"\mathcal E_{r,U}^{\rm prim}(I,J)",
        r"8^{\omega(r)}\tau(r)(\log r)^3(\log\log r)^7B^2",
        r"\frac{|I|^2|J|^2}{r\varphi(r)}",
        "cochrane_shi_unit_product_spectrum_audit",
        "nonunit gcd strata",
        "joint two-Möbius packet",
        "### 9.87 Exact nonunit gcd descent closes every sharp interval stratum",
        r"w=[d,e],\qquad R=\frac r w",
        r"e_r(kh\delta)",
        r"\frac{\varphi([d,e])}{[d,e]}",
        r"R=1",
        r"\Longleftrightarrow r\mid h\delta",
        r"1+H+L+\frac{HL}{r}",
        "nonunit_product_gcd_strata_audit",
        "cochrane_shi_all_gcd_product_spectrum_audit",
        "smooth, nonseparable AFE packet",
        "### 9.88 The archimedean smooth packet has bounded projective cost",
        r"\sum_{\mathbf n}|c_{\mathbf n}|",
        r"\operatorname {Var}_I w",
        "finite_two_variable_fourier_projective_audit",
        "smooth_projective_product_spectrum_audit",
        "joint arithmetic packet and coupled-kernel flags false",
        "### 9.89 Global ratio-frequency diagonalization before Type I/II",
        r"\widehat c_x(k)",
        r"\mathcal G_s(C,U)",
        r"d_1p_1t_2\equiv d_2p_2t_1\pmod s",
        r"b_1c_1n_1p_1t_2-b_2c_2n_2p_2t_1=js",
        "global_ratio_frequency_square_audit",
        "strictly more explicit **fixed-modulus inner gate**",
        r"outer sign \(\mu(s)\) is constant",
        "### 9.90 The global linear character master retains both Möbius weights",
        r"\mathcal A_s(\chi;U)",
        r"\mathscr S[\alpha,\beta,U]",
        r"D_s^{\rm small}(\chi)",
        "global_two_mobius_character_master_audit",
        "requested pre-Cauchy two-Möbius Type",
        r"(\star_1,\star_2)\in",
        r"\varepsilon_{\mathrm I}=-1",
        "all nine ordered cross-Type blocks",
        "arXiv:2105.15051",
        "do not provide a varying-squarefree-modulus estimate",
        "### 9.91 The cross-modulus zero product frequency is exactly diagonal",
        r"\xi(s,t)=\frac{\overline t_s}{s}",
        r"\xi(s_1,t_1)=\xi(s_2,t_2)",
        "primitive_product_farey_collision_audit",
        r"exponent \(11\)",
        r"3+3+5=11",
        "### 9.92 Exact Euler centering of every cross-modulus frequency",
        r"\mathfrak m_{s_1,s_2}(\kappa)",
        r"\mu(s_1)\mu(s_2)=\mu(r_1)\mu(r_2)",
        r"z_p(\kappa)",
        "cross_modulus_product_frequency_density_audit",
        "weighted Type/AFE packet has not yet been centered",
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
