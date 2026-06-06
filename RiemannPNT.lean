import RiemannExplorer
import GammaResidue
import HardyTheorem
import EulerAndLfunctions
import PrimeNumberTheorem
import ZeroFreeRegion

open Filter Topology Asymptotics

namespace RiemannPNT.API

/-- Public entry point for the equivalence of the three PNT formulations used
in the project. -/
theorem pnt_forms_equiv :
    (PrimeNumberTheorem.PNTForm1 ↔ PrimeNumberTheorem.PNTForm2) ∧
      (PrimeNumberTheorem.PNTForm2 ↔ PrimeNumberTheorem.PNTForm3) :=
  PrimeNumberTheorem.pnt_forms_equivalent

/-- Public error-term form of `PNTForm1`. -/
theorem pnt_form1_iff_error_isLittleO_main :
    PrimeNumberTheorem.PNTForm1 ↔
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
        =o[atTop] (fun x : ℝ => x / Real.log x) :=
  PrimeNumberTheorem.PNTForm1_iff_error_isLittleO_main

/-- Public error-term form of `PNTForm3`. -/
theorem pnt_form3_iff_error_isLittleO_id :
    PrimeNumberTheorem.PNTForm3 ↔
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
        =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm3_iff_error_isLittleO_id

/-- Public entry point for the equivalence between the pointwise and
composable RH-scale prime-counting error targets. -/
theorem rh_error_bound_iff_composable :
    PrimeNumberTheorem.RH_ErrorBound ↔
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound

/-- Public endpoint estimate in the partial-summation bridge from `θ` errors
to prime-counting errors. -/
theorem theta_error_div_log_isBigO_sqrt_mul_log
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    (fun x : ℝ => (Chebyshev.theta x - x) / Real.log x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) :=
  PrimeNumberTheorem.theta_error_div_log_isBigO_sqrt_mul_log hθ

/-- Public Abel-integral estimate in the partial-summation bridge from `θ`
errors to prime-counting errors. -/
theorem theta_error_integral_isBigO_sqrt_mul_log
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    (fun x : ℝ =>
      ∫ t in (2)..x,
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) :=
  PrimeNumberTheorem.theta_error_integral_isBigO_sqrt_mul_log hθ

/-- Public closed partial-summation bridge from the `θ` RH-scale target to the
prime-counting `Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_theta_error
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound hθ

/-- Public closed partial-summation bridge from the `ψ` RH-scale target to the
prime-counting `Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_psi_error
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound hψ

/-- Public bridge from the `θ` RH-scale target to the pointwise textbook
prime-counting RH error target. -/
theorem rh_error_bound_of_theta_error
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_ThetaErrorBound hθ

/-- Public bridge from the `ψ` RH-scale target to the pointwise textbook
prime-counting RH error target. -/
theorem rh_error_bound_of_psi_error
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_PsiErrorBound hψ

/-- Public bound showing that the jump term between `ψ` and the midpoint
convention `ψ₀` is negligible at the RH error scale. -/
theorem jumpVonMangoldt_isBigO_rh_scale :
    (fun x : ℝ => PrimeNumberTheorem.jumpVonMangoldt x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.jumpVonMangoldt_isBigO_rh_scale

/-- Public equivalence between the RH-scale error target for `ψ` and the
corresponding midpoint-convention `ψ₀` target. -/
theorem rh_psi_error_bound_iff_chebyshevPsi0_sub_id_isBigO :
    PrimeNumberTheorem.RH_PsiErrorBound ↔
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO

/-- Public conditional partial-summation bridge from the `θ` RH-scale target
to the prime-counting `Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_theta_error_and_integral_error
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound)
    (hintegral :
      (fun x : ℝ =>
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound_of_integral_error
    hθ hintegral

/-- Public conditional partial-summation bridge from the `ψ` RH-scale target
to the prime-counting `Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_psi_error_and_integral_error
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound)
    (hintegral :
      (fun x : ℝ =>
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound_of_integral_error
    hψ hintegral

/-- Public bridge between the project's RH/error target and Mathlib's RH
predicate. -/
theorem rh_iff_optimal_error_iff_mathlib :
    PrimeNumberTheorem.rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis ↔
        PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :=
  PrimeNumberTheorem.rh_iff_optimal_error_iff_mathlib

/-- Public compatibility bridge between Mathlib's RH predicate and the local
`RiemannHypothesis.Statement` interface used in the project files. -/
theorem rh_statement_iff_mathlib :
    _root_.RiemannHypothesis ↔ _root_.RiemannHypothesis.Statement :=
  PrimeNumberTheorem.rh_statement_iff_mathlib

/-- Public pointwise textbook-error form of the project's RH/error target. -/
theorem rh_iff_pointwise_error_iff :
    PrimeNumberTheorem.rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis.Statement ↔ PrimeNumberTheorem.RH_ErrorBound) :=
  PrimeNumberTheorem.rh_iff_pointwise_error_iff

/-- Public packaging lemma for closing the RH/error target from Mathlib-RH
implications in composable Big-O form. -/
theorem rh_iff_optimal_error_of_mathlib_implications
    (h_forward : _root_.RiemannHypothesis →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      _root_.RiemannHypothesis) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_mathlib_implications
    h_forward h_reverse

/-- Public packaging lemma for closing the RH/error target from Mathlib-RH
implications in pointwise textbook form. -/
theorem rh_iff_optimal_error_of_mathlib_pointwise_implications
    (h_forward : _root_.RiemannHypothesis → PrimeNumberTheorem.RH_ErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_ErrorBound → _root_.RiemannHypothesis) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_mathlib_pointwise_implications
    h_forward h_reverse

/-- Public packaging lemma for closing the RH/error target from a future RH-to-`ψ`
error theorem. -/
theorem rh_iff_optimal_error_of_RH_PsiErrorBound_implications
    (h_forward : _root_.RiemannHypothesis.Statement →
      PrimeNumberTheorem.RH_PsiErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      _root_.RiemannHypothesis.Statement) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_RH_PsiErrorBound_implications
    h_forward h_reverse

/-- Public packaging lemma for closing the RH/error target from a future RH-to-`θ`
error theorem. -/
theorem rh_iff_optimal_error_of_RH_ThetaErrorBound_implications
    (h_forward : _root_.RiemannHypothesis.Statement →
      PrimeNumberTheorem.RH_ThetaErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      _root_.RiemannHypothesis.Statement) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_RH_ThetaErrorBound_implications
    h_forward h_reverse

/-- Public forward direction from the RH/error target plus Mathlib RH to the
composable prime-counting error bound. -/
theorem rh_primeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error
    h

/-- Public forward direction from the RH/error target plus Mathlib RH to the
pointwise textbook prime-counting error bound. -/
theorem rh_error_bound_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public reverse direction from the composable prime-counting error bound to
Mathlib RH, assuming the RH/error target. -/
theorem mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound → _root_.RiemannHypothesis :=
  PrimeNumberTheorem.mathlib_RH_of_rh_iff_optimal_error h

/-- Public reverse direction from the pointwise textbook error bound to Mathlib
RH, assuming the RH/error target. -/
theorem mathlib_RH_of_rh_iff_pointwise_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_ErrorBound → _root_.RiemannHypothesis :=
  PrimeNumberTheorem.mathlib_RH_of_rh_iff_pointwise_error h

/-- Public Mathlib-facing pointwise textbook form of the RH/error equivalence
target. -/
theorem rh_iff_optimal_error_iff_mathlib_pointwise :
    PrimeNumberTheorem.rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis ↔ PrimeNumberTheorem.RH_ErrorBound) :=
  PrimeNumberTheorem.rh_iff_optimal_error_iff_mathlib_pointwise

/-- Public consequence: the RH/error target turns Mathlib RH into PNT form 1. -/
theorem pnt_form1_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public consequence: the RH/error target turns Mathlib RH into PNT form 2. -/
theorem pnt_form2_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public consequence: the RH/error target turns Mathlib RH into PNT form 3. -/
theorem pnt_form3_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public equivalence between Mathlib's RH predicate and the nontrivial-zero
line statement. -/
theorem rh_iff_nontrivial_zeros_on_line :
    _root_.RiemannHypothesis ↔
      ∀ s : ℂ, _root_.RiemannHypothesis.IsNontrivialZero s → s.re = 1 / 2 :=
  PrimeNumberTheorem.rh_iff_nontrivial_zeros_on_line

/-- Public functional-equation symmetry for nontrivial zeros. -/
theorem nontrivial_zero_symmetric
    {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : 0 < ρ.re) (hre' : ρ.re < 1) :
    riemannZeta (1 - ρ) = 0 :=
  PrimeNumberTheorem.nontrivial_zero_symmetric hρ hre hre'

/-- Public packaged symmetry: `1 - ρ` is a nontrivial zero whenever `ρ` is. -/
theorem nontrivial_zero_symmetric'
    {ρ : ℂ} (h : _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    _root_.RiemannHypothesis.IsNontrivialZero (1 - ρ) :=
  PrimeNumberTheorem.nontrivial_zero_symmetric' h

/-- Public critical-strip location theorem for nontrivial zeta zeros. -/
theorem nontrivial_zero_in_critical_strip {s : ℂ}
    (hζ : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 :=
  PrimeNumberTheorem.nontrivial_zero_in_critical_strip hζ hnt hs1

/-- Public local isolated-zero statement for `riemannZeta` away from the pole. -/
theorem riemannZeta_not_frequently_zero_nhdsNE_of_ne_one
    {x : ℂ} (hx : x ≠ 1) :
    ¬ ∃ᶠ z in 𝓝[≠] x, riemannZeta z = 0 :=
  PrimeNumberTheorem.riemannZeta_not_frequently_zero_nhdsNE_of_ne_one hx

/-- Public local finiteness of nontrivial zeta zeros in bounded height. -/
theorem finite_nontrivial_zeros_bounded_height (T : ℝ) :
    Set.Finite
      {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧ |s.im| ≤ T} :=
  PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height T

/-- Public simple-pole consequence at `s = 1`: `(s - 1)^2 ζ(s) → 0`. -/
theorem riemannZeta_pole_simple :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * riemannZeta s) (𝓝[≠] 1) (𝓝 0) :=
  PrimeNumberTheorem.riemannZeta_pole_simple

/-- Public RH symmetry consistency for nontrivial zeros. -/
theorem rh_zero_symmetric_self_consistent
    {ρ : ℂ}
    (hRH : _root_.RiemannHypothesis.Statement)
    (h : _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    ρ.re = 1 / 2 ∧ (1 - ρ).re = 1 / 2 :=
  PrimeNumberTheorem.rh_zero_symmetric_self_consistent hRH h

/-- Public closed-half-plane nonvanishing theorem for the Riemann zeta
function. -/
theorem zeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  ZetaValues.zeta_ne_zero_of_one_le_re hs

/-- Public coordinate form of zeta nonvanishing on `Re(s) ≥ 1`. -/
theorem zeta_ne_zero_re_im_of_one_le {β t : ℝ} (hβ : 1 ≤ β) :
    riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZetaValues.zeta_ne_zero_re_im_of_one_le hβ

/-- Public coordinate form of Dirichlet `LFunction` nonvanishing in
`Re(s) > 1`. -/
theorem dirichlet_lfunction_ne_zero_re_im {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ t : ℝ} (hσ : 1 < σ) :
    DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
  DirichletNonvanishing.lfunction_ne_zero_re_im χ hσ

/-- Public Gamma residue at zero. -/
theorem gamma_residue_at_zero :
    Tendsto (fun s : ℂ => s * Complex.Gamma s) (𝓝[≠] 0) (𝓝 1) :=
  GammaResidue.gamma_residue_at_zero

/-- Public Gamma residue formula at the negative integers. -/
theorem gamma_residue_at_neg_natural (n : ℕ) :
    Tendsto (fun s : ℂ => (s + n) * Complex.Gamma s) (𝓝[≠] (-n : ℂ))
      (𝓝 ((-1 : ℂ) ^ n / (n.factorial : ℂ))) :=
  GammaResidue.gamma_residue_at_neg_natural n

/-- Public simple-pole package for Gamma at negative integers. -/
theorem gamma_simple_pole_at_neg_natural (n : ℕ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f (-n : ℂ) ∧ f (-n : ℂ) ≠ 0 ∧
      ∀ s : ℂ, (s + (n : ℂ)) ≠ 0 → Complex.Gamma s = f s / (s + n) :=
  GammaResidue.IsSimplePoleOfGamma n

/-- Public coordinate form of the classical zero-free-region target. -/
theorem classical_zero_free_region_iff_re_im :
    ZeroFreeRegion.classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 2 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_iff_re_im

/-- Public bridge: the Vinogradov-Korobov target implies the classical
zero-free-region target. -/
theorem classical_zero_free_region_of_vinogradov_korobov
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov hvk

/-- Public high-height coordinate interface for the classical zero-free-region
target. -/
theorem classical_zero_free_region_iff_high_height_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ZeroFreeRegion.classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_iff_high_height_re_im T0 hT0

/-- Public height-`3` coordinate interface for the classical zero-free-region
target, matching the Vinogradov-Korobov cutoff. -/
theorem classical_zero_free_region_iff_high_height_re_im_at_three :
    ZeroFreeRegion.classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_iff_high_height_re_im_at_three

/-- Public coordinate compact-patching theorem at the height cutoff `3`. -/
theorem compact_patch_classical_zero_free_region_re_im_at_three
    (hhigh :
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.compact_patch_classical_zero_free_region_re_im_at_three hhigh

/-- Public coordinate form of the Vinogradov-Korobov zero-free-region target. -/
theorem vinogradov_korobov_zero_free_region_iff_re_im :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_iff_re_im

/-- Public pointwise width comparison showing that the Vinogradov-Korobov strip
dominates the classical `c / log |t|` strip above height `3`. -/
theorem classical_width_le_vinogradov_korobov_width {c t : ℝ}
    (hc : 0 ≤ c) (ht : 3 ≤ |t|) :
    c / Real.log |t| ≤
      c / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) :=
  ZeroFreeRegion.classical_width_le_vinogradov_korobov_width hc ht

/-- Public high-height classical-width consequence of the Vinogradov-Korobov
target, in real/imaginary coordinates. -/
theorem vinogradov_korobov_high_height_classical_zero_free_region_re_im
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_high_height_classical_zero_free_region_re_im hvk

/-- Public equivalence between Hardy's real `Z` zeros and zeta zeros on the
critical line. -/
theorem hardyZ_zero_iff_zeta_zero (t : ℝ) :
    HardyTheorem.hardyZ t = 0 ↔ riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.hardyZ_zero_iff_zeta_zero t

/-- Public packaging equivalence: the two signed Hardy moments are exactly the
first two signed integral-asymptotic targets. -/
theorem hardy_two_signed_moments_target_iff_integral_asymptotic_one_two :
    HardyTheorem.hardy_two_signed_moments_target ↔
      HardyTheorem.integral_asymptotic_target 1 ∧
        HardyTheorem.integral_asymptotic_target 2 :=
  HardyTheorem.hardy_two_signed_moments_target_iff_integral_asymptotic_one_two

/-- Public bridge from the two signed Hardy moments to the first integral
asymptotic target. -/
theorem integral_asymptotic_one_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.integral_asymptotic_target 1 :=
  HardyTheorem.integral_asymptotic_one_of_two_signed_moments h

/-- Public bridge from the two signed Hardy moments to the second integral
asymptotic target. -/
theorem integral_asymptotic_two_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.integral_asymptotic_target 2 :=
  HardyTheorem.integral_asymptotic_two_of_two_signed_moments h

/-- Public packaging lemma from the first two integral asymptotics to the two
signed Hardy moment target. -/
theorem hardy_two_signed_moments_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_two_signed_moments_target :=
  HardyTheorem.hardy_two_signed_moments_of_integral_asymptotic_one_two h1 h2

/-- Public consequence of the two signed Hardy moments: the first weighted
integral tends to `atBot`. -/
theorem weightedIntegral_one_tendsto_atBot_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    Tendsto (fun T : ℝ => HardyTheorem.weightedIntegral 1 T) atTop atBot :=
  HardyTheorem.weightedIntegral_one_tendsto_atBot_of_two_signed_moments h

/-- Public consequence of the two signed Hardy moments: the first weighted
integral is eventually negative. -/
theorem weightedIntegral_one_eventually_negative_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    ∀ᶠ T in atTop, HardyTheorem.weightedIntegral 1 T < 0 :=
  HardyTheorem.weightedIntegral_one_eventually_negative_of_two_signed_moments h

/-- Public consequence of the two signed Hardy moments: the second weighted
integral tends to `atTop`. -/
theorem weightedIntegral_two_tendsto_atTop_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    Tendsto (fun T : ℝ => HardyTheorem.weightedIntegral 2 T) atTop atTop :=
  HardyTheorem.weightedIntegral_two_tendsto_atTop_of_two_signed_moments h

/-- Public consequence of the two signed Hardy moments: the second weighted
integral is eventually positive. -/
theorem weightedIntegral_two_eventually_positive_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    ∀ᶠ T in atTop, 0 < HardyTheorem.weightedIntegral 2 T :=
  HardyTheorem.weightedIntegral_two_eventually_positive_of_two_signed_moments h

/-- Public tail-dominance consequence for `-hardyZ` from the first signed
Hardy moment. -/
theorem weightedIntegralOf_neg_hardyZ_one_tail_dominates_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.weightedIntegralOf_tail_dominates
      (fun t => -HardyTheorem.hardyZ t) 1 :=
  HardyTheorem.weightedIntegralOf_neg_hardyZ_one_tail_dominates_of_two_signed_moments h

/-- Public tail-dominance consequence for `hardyZ` from the second signed
Hardy moment. -/
theorem weightedIntegralOf_hardyZ_two_tail_dominates_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.weightedIntegralOf_tail_dominates HardyTheorem.hardyZ 2 :=
  HardyTheorem.weightedIntegralOf_hardyZ_two_tail_dominates_of_two_signed_moments h

/-- Public equivalence between Hardy's infinite-zero target and infinitude of
Hardy `Z` zeros. -/
theorem hardy_theorem_target_iff_hardyZ_zero_set_infinite :
    HardyTheorem.hardy_theorem_target ↔
      {t : ℝ | HardyTheorem.hardyZ t = 0}.Infinite :=
  HardyTheorem.hardy_theorem_target_iff_hardyZ_zero_set_infinite

/-- Public consequence: Hardy's infinite-zero target gives at least one
critical-line zero. -/
theorem exists_zero_on_critical_line_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_hardy_theorem_target h

/-- Public consequence: the first two signed Hardy moments give at least one
critical-line zero. -/
theorem exists_zero_on_critical_line_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_two_signed_moments hmom

/-- Public consequence: the first two Hardy integral asymptotics give at least
one critical-line zero. -/
theorem exists_zero_on_critical_line_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_integral_asymptotic_one_two h1 h2

/-- Public bridge from Hardy's unbounded-height target to infinitely many
critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_hardy_unbounded
    (h : HardyTheorem.hardy_zeros_unbounded_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line_of_unbounded h

/-- Public bridge between one-sided and absolute-height Hardy unbounded targets. -/
theorem hardy_zeros_unbounded_iff_abs_unbounded :
    HardyTheorem.hardy_zeros_unbounded_target ↔
      HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded

/-- Public HardyZ form of the positive-height unbounded target. -/
theorem hardy_zeros_unbounded_target_iff_hardyZ_unbounded :
    HardyTheorem.hardy_zeros_unbounded_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.hardy_zeros_unbounded_target_iff_hardyZ_unbounded

/-- Public HardyZ form of the absolute-height unbounded target. -/
theorem hardy_zeros_abs_unbounded_target_iff_hardyZ_abs_unbounded :
    HardyTheorem.hardy_zeros_abs_unbounded_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ |t| ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.hardy_zeros_abs_unbounded_target_iff_hardyZ_abs_unbounded

/-- Public equivalence between Hardy's infinite-zero target and the
absolute-height unbounded target, using the local finiteness of zeta zeros in
bounded height. -/
theorem hardy_theorem_target_iff_abs_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_theorem_target_iff_abs_unbounded

/-- Public equivalence between Hardy's infinite-zero target and the
positive-height unbounded target, using symmetry on the critical line. -/
theorem hardy_theorem_target_iff_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_theorem_target_iff_unbounded

/-- Public bridge from Hardy's infinite-zero target to arbitrarily large
absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_hardy_theorem_target h

/-- Public bridge from Hardy's infinite-zero target to arbitrarily large
positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_hardy_theorem_target h

/-- Public bridge from the first two signed Hardy moment targets to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_two_signed_moments hmom

/-- Public bridge from the first two Hardy integral asymptotics to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_integral_asymptotic_one_two h1 h2

/-- Public bridge from the first two signed Hardy moments to arbitrarily large
absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_two_signed_moments hmom

/-- Public bridge from the first two signed Hardy moments to arbitrarily large
positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_two_signed_moments hmom

/-- Public bridge from the first two Hardy integral asymptotics to arbitrarily
large absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two
    h1 h2

/-- Public bridge from the first two Hardy integral asymptotics to arbitrarily
large positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_integral_asymptotic_one_two
    h1 h2

/-- Public bridge from Hardy's absolute-height unbounded target to infinitely
many critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_hardy_abs_unbounded
    (h : HardyTheorem.hardy_zeros_abs_unbounded_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line
    (HardyTheorem.hardy_theorem_target_of_abs_unbounded h)

/-- Public interval-zero consequence of the Hardy--Littlewood lower-bound
target. -/
theorem eventually_exists_zero_on_critical_line_interval_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∀ᶠ T in atTop,
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.eventually_exists_zero_on_critical_line_interval_of_hardy_littlewood_lower_bound h

/-- Public interval-zero consequence of Selberg's positive-proportion target. -/
theorem eventually_exists_zero_on_critical_line_interval_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∀ᶠ T in atTop,
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.eventually_exists_zero_on_critical_line_interval_of_selberg_zero_proportion h

/-- Public Hardy-Z interval-zero consequence of the Hardy--Littlewood
lower-bound target. -/
theorem eventually_exists_hardyZ_zero_interval_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∀ᶠ T in atTop, ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ HardyTheorem.hardyZ t = 0 :=
  KnownResults.eventually_exists_hardyZ_zero_interval_of_hardy_littlewood_lower_bound h

/-- Public Hardy-Z interval-zero consequence of Selberg's positive-proportion
target. -/
theorem eventually_exists_hardyZ_zero_interval_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∀ᶠ T in atTop, ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ HardyTheorem.hardyZ t = 0 :=
  KnownResults.eventually_exists_hardyZ_zero_interval_of_selberg_zero_proportion h

/-- Public bridge from Hardy--Littlewood's linear lower-bound target to
arbitrarily large positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound h

/-- Public bridge from Hardy--Littlewood's linear lower-bound target to
arbitrarily large absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound h

/-- Public bridge from Hardy--Littlewood's linear lower-bound target to
Hardy's infinite-zero target. -/
theorem hardy_theorem_target_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_hardy_littlewood_lower_bound h

/-- Public bridge from Selberg's positive-proportion target to arbitrarily
large positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion h

/-- Public bridge from Selberg's positive-proportion target to arbitrarily
large absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_selberg_zero_proportion h

/-- Public bridge from Selberg's positive-proportion target to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_selberg_zero_proportion h

/-- Public bridge from Conrey's positive-proportion target to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_conrey_40_percent_target h

/-- Public bridge from Conrey's positive-proportion target to arbitrarily
large absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_conrey_40_percent_target h

/-- Public bridge from Conrey's positive-proportion target to arbitrarily
large positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_conrey_40_percent_target h

/-- Public entry point for the norm-error formulation of the corrected
height-truncated von Mangoldt explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖) atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_norm_error_tendsto_zero

/-- Public reverse-norm error formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T‖) atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_reverse_norm_error_tendsto_zero

/-- Public norm-small-o formulation of the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_norm_error_isLittleO_one

/-- Public real/imaginary error formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_re_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto
        (fun T : ℝ =>
          (PrimeNumberTheorem.explicitFormulaApprox x T).re -
            PrimeNumberTheorem.chebyshevPsi0 x)
        atTop (𝓝 0) ∧
      Tendsto
        (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
        atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_error_tendsto_zero

/-- Public absolute real/imaginary error formulation of the corrected
explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_re_im_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto
        (fun T : ℝ =>
          |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
            PrimeNumberTheorem.chebyshevPsi0 x|)
        atTop (𝓝 0) ∧
      Tendsto
        (fun T : ℝ => |(PrimeNumberTheorem.explicitFormulaApprox x T).im|)
        atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_abs_error_tendsto_zero

/-- Public bridge: any eventual norm error bound by a function tending to zero
closes the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_norm_le
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop,
      ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖ ≤ E T) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_norm_le
    hE hbound

/-- Public bridge: a Big-O norm error estimate against any function tending to
zero closes the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_norm_error_isBigO_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hO :
      (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖)
        =O[atTop] E) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_norm_error_isBigO_tendsto_zero
    hE hO

/-- Public bridge: an eventual `C/T` norm error estimate closes the corrected
explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_norm_le_const_mul_inv
    {x C : ℝ} {hx : x ≥ 2}
    (hbound : ∀ᶠ T in atTop,
      ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖ ≤ C * T⁻¹) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_norm_le_const_mul_inv
    hbound

/-- Public bridge: eventual real and imaginary error bounds by functions
tending to zero close the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_re_im_abs_le
    {x : ℝ} {hx : x ≥ 2} {Ere Eim : ℝ → ℝ}
    (hEre : Tendsto Ere atTop (𝓝 0))
    (hEim : Tendsto Eim atTop (𝓝 0))
    (hre_bound : ∀ᶠ T in atTop,
      |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
        PrimeNumberTheorem.chebyshevPsi0 x| ≤ Ere T)
    (him_bound : ∀ᶠ T in atTop,
      |(PrimeNumberTheorem.explicitFormulaApprox x T).im| ≤ Eim T) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_re_im_abs_le
    hEre hEim hre_bound him_bound

/-- Public bridge: eventual `C/T` real and imaginary error estimates close the
corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_re_im_abs_le_const_mul_inv
    {x Cre Cim : ℝ} {hx : x ≥ 2}
    (hre_bound : ∀ᶠ T in atTop,
      |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
        PrimeNumberTheorem.chebyshevPsi0 x| ≤ Cre * T⁻¹)
    (him_bound : ∀ᶠ T in atTop,
      |(PrimeNumberTheorem.explicitFormulaApprox x T).im| ≤ Cim * T⁻¹) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_re_im_abs_le_const_mul_inv
    hre_bound him_bound

/-- Public norm identity for a single nontrivial-zero contribution. -/
theorem norm_zero_contribution_eq
    (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ρ / ρ‖ = x ^ ρ.re / ‖ρ‖ :=
  PrimeNumberTheorem.norm_zero_contribution_eq ρ hx

/-- Public RH specialization: each nontrivial-zero contribution has
`sqrt x` amplitude. -/
theorem norm_zero_contribution_eq_sqrt_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ)
    {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ρ / ρ‖ = Real.sqrt x / ‖ρ‖ :=
  PrimeNumberTheorem.norm_zero_contribution_eq_sqrt_of_RH hRH hρ hx

/-- Public RH bound for any finite sum of nontrivial-zero contributions. -/
theorem norm_sum_zero_contributions_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x : ℝ} (hx : 0 < x) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    ‖∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x * ∑ ρ ∈ S, ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.norm_sum_zero_contributions_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx S hS

/-- Public RH bound for the height-truncated nontrivial-zero sum. -/
theorem norm_finiteNontrivialZeroSum_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T : ℝ} (hx : 0 < x) :
    ‖PrimeNumberTheorem.finiteNontrivialZeroSum x T‖ ≤
      Real.sqrt x *
        ∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T, ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.norm_finiteNontrivialZeroSum_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx

/-- Public RH bound for the new-zero contribution between two truncation
heights. -/
theorem norm_new_zero_contribution_sum_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) :
    ‖∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x *
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.norm_new_zero_contribution_sum_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx

/-- Public RH lower bound for the norm of a nontrivial zero. -/
theorem norm_nontrivial_zero_ge_half_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    (1 / 2 : ℝ) ≤ ‖ρ‖ :=
  PrimeNumberTheorem.norm_nontrivial_zero_ge_half_of_RH hRH hρ

/-- Public RH upper bound for the reciprocal norm of a nontrivial zero. -/
theorem inv_norm_nontrivial_zero_le_two_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    ‖ρ‖⁻¹ ≤ (2 : ℝ) :=
  PrimeNumberTheorem.inv_norm_nontrivial_zero_le_two_of_RH hRH hρ

/-- Public RH bound for finite reciprocal-norm zero sums. -/
theorem sum_inv_norm_le_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    (∑ ρ ∈ S, ‖ρ‖⁻¹) ≤ (2 : ℝ) * S.card :=
  PrimeNumberTheorem.sum_inv_norm_le_two_card_of_RH hRH S hS

/-- Public RH bound for the truncated reciprocal-norm zero sum. -/
theorem sum_inv_norm_nontrivialZerosFinset_le_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement) (T : ℝ) :
    (∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T, ‖ρ‖⁻¹) ≤
      (2 : ℝ) * (PrimeNumberTheorem.nontrivialZerosFinset T).card :=
  PrimeNumberTheorem.sum_inv_norm_nontrivialZerosFinset_le_two_card_of_RH
    hRH T

/-- Public RH bound for reciprocal-norm sums over newly appearing zeros. -/
theorem sum_inv_norm_new_zeros_le_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement) (T U : ℝ) :
    (∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹) ≤
      (2 : ℝ) *
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T).card :=
  PrimeNumberTheorem.sum_inv_norm_new_zeros_le_two_card_of_RH hRH T U

/-- Public RH count-bound for the height-truncated nontrivial-zero sum. -/
theorem norm_finiteNontrivialZeroSum_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T : ℝ} (hx : 0 < x) :
    ‖PrimeNumberTheorem.finiteNontrivialZeroSum x T‖ ≤
      Real.sqrt x *
        ((2 : ℝ) * (PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.norm_finiteNontrivialZeroSum_le_sqrt_mul_two_card_of_RH
    hRH hx

/-- Public RH count-bound for the new-zero contribution between truncation
heights. -/
theorem norm_new_zero_contribution_sum_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) :
    ‖∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x *
        ((2 : ℝ) *
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.norm_new_zero_contribution_sum_le_sqrt_mul_two_card_of_RH
    hRH hx

/-- Public RH Cauchy-type bound for two explicit-formula truncations,
measured by the reciprocal-norm sum of newly included zeros. -/
theorem norm_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U‖ ≤
      Real.sqrt x *
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.norm_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx hTU

/-- Public RH Cauchy-type bound for two explicit-formula truncations,
measured by the number of newly included zeros. -/
theorem norm_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U‖ ≤
      Real.sqrt x *
        ((2 : ℝ) *
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.norm_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    hRH hx hTU

/-- Public real-part RH Cauchy-type truncation bound, measured by the
reciprocal-norm sum of newly included zeros. -/
theorem abs_re_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U).re| ≤
      Real.sqrt x *
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.abs_re_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx hTU

/-- Public imaginary-part RH Cauchy-type truncation bound, measured by the
reciprocal-norm sum of newly included zeros. -/
theorem abs_im_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U).im| ≤
      Real.sqrt x *
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.abs_im_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx hTU

/-- Public real-part RH Cauchy-type truncation bound, measured by the number of
newly included zeros. -/
theorem abs_re_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U).re| ≤
      Real.sqrt x *
        ((2 : ℝ) *
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.abs_re_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    hRH hx hTU

/-- Public imaginary-part RH Cauchy-type truncation bound, measured by the
number of newly included zeros. -/
theorem abs_im_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U).im| ≤
      Real.sqrt x *
        ((2 : ℝ) *
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.abs_im_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    hRH hx hTU

/-- Public conditional explicit-formula bridge from an RH reciprocal-norm tail
bound over newly included zeros. -/
theorem explicit_formula_von_mangoldt_of_RH_base_and_new_zero_sum_tendsto_zero
    (hRH : _root_.RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : PrimeNumberTheorem.explicitFormulaApprox x B =
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          Real.sqrt x *
            ∑ ρ ∈
              (PrimeNumberTheorem.nontrivialZerosFinset T \
                PrimeNumberTheorem.nontrivialZerosFinset B), ‖ρ‖⁻¹)
        atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_RH_base_and_new_zero_sum_tendsto_zero
    hRH hB htail

/-- Public conditional explicit-formula bridge from an RH zero-count tail bound
over newly included zeros. -/
theorem explicit_formula_von_mangoldt_of_RH_base_and_new_zero_card_tendsto_zero
    (hRH : _root_.RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : PrimeNumberTheorem.explicitFormulaApprox x B =
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          Real.sqrt x *
            ((2 : ℝ) *
              (PrimeNumberTheorem.nontrivialZerosFinset T \
                PrimeNumberTheorem.nontrivialZerosFinset B).card))
        atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_RH_base_and_new_zero_card_tendsto_zero
    hRH hB htail

/-- Public stability bridge: if the zero sum has no new terms eventually and
the stable truncation equals `ψ₀(x)`, then the explicit-formula target follows. -/
theorem explicit_formula_von_mangoldt_of_eventually_no_new_zeros
    {x B : ℝ} {hx : x ≥ 2}
    (hnew : ∀ᶠ T in atTop,
      B ≤ T ∧
        PrimeNumberTheorem.nontrivialZerosFinset T \
            PrimeNumberTheorem.nontrivialZerosFinset B = ∅)
    (hB : PrimeNumberTheorem.explicitFormulaApprox x B =
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_no_new_zeros
    hnew hB

end RiemannPNT.API
