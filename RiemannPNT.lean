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
