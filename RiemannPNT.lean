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
