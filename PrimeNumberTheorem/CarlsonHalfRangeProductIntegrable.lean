import HardyTheorem.AFECriticalHalfRangeScale
import PrimeNumberTheorem.CarlsonConreyCriticalBoundaryReduction
import PrimeNumberTheorem.CarlsonGaussianHilbertMemLp
import ZeroFreeRegion.PhragmenLindelofZeta

/-! # Global Gaussian integrability of the one-scale Carlson product

This is deliberately separate from the quantitative tail estimate.  It uses
only unconditional polynomial zeta growth and the elementary pointwise bound
for the finite Selberg mollifier. -/

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- A fixed absolute eighth polynomial moment of the half-strength Gaussian. -/
noncomputable def gaussianPolynomialMomentEight : ℝ :=
  ∫ y : ℝ, (1 + |y|) ^ 8 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)

theorem integrable_gaussianPolynomialMomentEight :
    Integrable fun y : ℝ =>
      (1 + |y|) ^ 8 * Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
  exact integrable_one_add_abs_pow_mul_exp_neg_mul_sq (by norm_num) 8

theorem gaussianPolynomialMomentEight_nonneg :
    0 ≤ gaussianPolynomialMomentEight := by
  unfold gaussianPolynomialMomentEight
  exact integral_nonneg fun y =>
    mul_nonneg (pow_nonneg (by positivity) 8) (Real.exp_nonneg _)

/-- After translation and dilation, the eighth polynomial Gaussian moment
costs at most `Delta^9` times one fixed absolute constant. -/
theorem integral_centeredPolynomialEight_mul_halfGaussian_le
    {Delta w : ℝ} (hDelta : 1 ≤ Delta) :
    (∫ t : ℝ, (1 + |t - w|) ^ 8 *
      Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2)) ≤
        Delta ^ 9 * gaussianPolynomialMomentEight := by
  let g : ℝ → ℝ := fun y =>
    (1 + |y|) ^ 8 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)
  have hDeltaPos : 0 < Delta := zero_lt_one.trans_le hDelta
  have hleft : Integrable fun t : ℝ =>
      (1 + |t - w|) ^ 8 *
        Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2) := by
    have hb : 0 < 1 / (2 * Delta ^ 2) := by positivity
    exact Integrable.comp_sub_right
      (integrable_one_add_abs_pow_mul_exp_neg_mul_sq hb 8) w
  have hg : Integrable g := by
    simpa only [g] using integrable_gaussianPolynomialMomentEight
  have hscaled : Integrable fun t : ℝ => g ((t - w) / Delta) := by
    have hdiv : Integrable fun u : ℝ => g (u / Delta) :=
      hg.comp_div hDeltaPos.ne'
    simpa only [sub_eq_add_neg] using hdiv.comp_add_right (-w)
  have hright : Integrable fun t : ℝ => Delta ^ 8 * g ((t - w) / Delta) :=
    hscaled.const_mul (Delta ^ 8)
  have hpoint : ∀ t : ℝ,
      (1 + |t - w|) ^ 8 *
          Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2) ≤
        Delta ^ 8 * g ((t - w) / Delta) := by
    intro t
    have hlinear : 1 + |t - w| ≤ Delta * (1 + |(t - w) / Delta|) := by
      rw [abs_div, abs_of_pos hDeltaPos]
      field_simp [hDeltaPos.ne']
      nlinarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t - w|) hlinear 8
    have hexp :
        Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2) =
          Real.exp (-(1 / 2 : ℝ) * ((t - w) / Delta) ^ 2) := by
      congr 1
      field_simp [hDeltaPos.ne']
    rw [hexp]
    dsimp only [g]
    calc
      _ ≤ (Delta * (1 + |(t - w) / Delta|)) ^ 8 *
          Real.exp (-(1 / 2 : ℝ) * ((t - w) / Delta) ^ 2) := by
        gcongr
      _ = Delta ^ 8 * ((1 + |(t - w) / Delta|) ^ 8 *
          Real.exp (-(1 / 2 : ℝ) * ((t - w) / Delta) ^ 2)) := by ring
  calc
    _ ≤ ∫ t : ℝ, Delta ^ 8 * g ((t - w) / Delta) :=
      integral_mono hleft hright hpoint
    _ = Delta ^ 8 * (Delta * gaussianPolynomialMomentEight) := by
      rw [integral_const_mul]
      congr 1
      calc
        (∫ t : ℝ, g ((t - w) / Delta)) =
            ∫ t : ℝ, (fun u : ℝ => g (u / Delta)) (t + (-w)) := by
              simp only [sub_eq_add_neg]
        _ = ∫ u : ℝ, g (u / Delta) :=
          integral_add_right_eq_self (μ := volume)
            (fun u : ℝ => g (u / Delta)) (-w)
        _ = |Delta| * ∫ y : ℝ, g y := by
          simpa only [smul_eq_mul] using Measure.integral_comp_div g Delta
        _ = Delta * gaussianPolynomialMomentEight := by
          rw [abs_of_pos hDeltaPos]
          rfl
    _ = Delta ^ 9 * gaussianPolynomialMomentEight := by ring

private theorem continuous_linearLogSelbergMollifiedZetaProduct_critical
    (X : ℕ) :
    Continuous fun t : ℝ =>
      linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t) := by
  let line : ℝ → ℂ := fun t => (1 / 2 : ℂ) + I * t
  have hline : Continuous line := by dsimp only [line]; fun_prop
  have hzeta : Continuous fun t : ℝ => riemannZeta (line t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : line t ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [line] at hre
    exact (differentiableAt_riemannZeta hne).continuousAt.comp hline.continuousAt
  have hmoll : Continuous fun t : ℝ =>
      HardyTheorem.linearLogSelbergMollifier X (line t) := by
    simpa only [HardyTheorem.linearLogSelbergMollifier_eq_selbergMoebiusMollifier,
      line, HardyTheorem.selbergMoebiusMollifier] using
      HardyTheorem.continuous_selbergMollifier_criticalLine X
        (fun n => (HardyTheorem.selbergMoebiusCoeff X n : ℂ))
  exact hzeta.mul hmoll

private theorem continuous_riemannZeta_critical :
    Continuous fun t : ℝ => riemannZeta ((1 / 2 : ℂ) + I * t) := by
  let line : ℝ → ℂ := fun t => (1 / 2 : ℂ) + I * t
  have hline : Continuous line := by dsimp only [line]; fun_prop
  rw [continuous_iff_continuousAt]
  intro t
  have hne : line t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [line] at hre
  exact (differentiableAt_riemannZeta hne).continuousAt.comp hline.continuousAt

private theorem exists_norm_riemannZeta_critical_le_compact :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ≤ M := by
  rcases isCompact_Icc.exists_bound_of_continuousOn
      continuous_riemannZeta_critical.continuousOn with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_right 0 M)

/-- A product-growth estimate uniform in the mollifier length.  All length
dependence is the explicit elementary factor `X`. -/
theorem exists_uniform_norm_sq_linearLogSelbergMollifiedZetaProduct_le_polynomial :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ,
      ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)‖ ^ 2 ≤
        C * X * (|t| + 3) ^ 8 := by
  obtain ⟨M, hM, hcompact⟩ := exists_norm_riemannZeta_critical_le_compact
  obtain ⟨Czeta, hCzeta, hzeta⟩ :=
    ZeroFreeRegion.exists_norm_riemannZeta_le_polynomial_on_zero_four
  let B : ℝ := 2 * Czeta
  let C : ℝ := 4 * M ^ 2 + B ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX t
  let A : ℝ := |t| + 3
  have hA : 1 ≤ A := by dsimp only [A]; linarith [abs_nonneg t]
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hX0 : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hsqrt : (Real.sqrt X) ^ 2 = (X : ℝ) := Real.sq_sqrt hX0
  have hm := HardyTheorem.norm_selbergMoebiusMollifier_criticalLine_le_two_sqrt hX t
  by_cases ht : |t| ≤ 1
  · have hz := hcompact t (abs_le.mp ht)
    have hprod :
        ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)‖ ≤
          M * (2 * Real.sqrt X) := by
      rw [linearLogSelbergMollifiedZetaProduct,
        HardyTheorem.linearLogSelbergMollifier_eq_selbergMoebiusMollifier,
        norm_mul]
      exact mul_le_mul hz hm (norm_nonneg _) hM
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hprod 2
    have hA8 : 1 ≤ A ^ 8 := one_le_pow₀ hA
    calc
      _ ≤ (M * (2 * Real.sqrt X)) ^ 2 := hsq
      _ = 4 * M ^ 2 * X := by
        rw [mul_pow, mul_pow, hsqrt]
        ring
      _ ≤ C * X := by
        apply mul_le_mul_of_nonneg_right
        · dsimp only [C]
          nlinarith [sq_nonneg B]
        · exact hX0
      _ ≤ C * X * A ^ 8 := le_mul_of_one_le_right (mul_nonneg hC hX0) hA8
  · have htHigh : 1 ≤ |t| := le_of_not_ge ht
    have hz := hzeta ((1 / 2 : ℂ) + I * t)
      (by norm_num : (((1 / 2 : ℂ) + I * t).re) ∈ Icc (0 : ℝ) 4)
      (by simpa using htHigh)
    have hz' : ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ≤
        Czeta * A ^ 4 := by simpa [A] using hz
    have hprod :
        ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)‖ ≤
          B * Real.sqrt X * A ^ 4 := by
      rw [linearLogSelbergMollifiedZetaProduct,
        HardyTheorem.linearLogSelbergMollifier_eq_selbergMoebiusMollifier,
        norm_mul]
      dsimp only [B]
      calc
        _ ≤ (Czeta * A ^ 4) * (2 * Real.sqrt X) :=
          mul_le_mul hz' hm (norm_nonneg _) (by positivity)
        _ = 2 * Czeta * Real.sqrt X * A ^ 4 := by ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hprod 2
    calc
      _ ≤ (B * Real.sqrt X * A ^ 4) ^ 2 := hsq
      _ = B ^ 2 * X * A ^ 8 := by
        calc
          (B * Real.sqrt X * A ^ 4) ^ 2 =
              B ^ 2 * (Real.sqrt X) ^ 2 * A ^ 8 := by ring
          _ = B ^ 2 * X * A ^ 8 := by rw [hsqrt]
      _ ≤ C * X * A ^ 8 := by
        gcongr
        dsimp only [C]
        nlinarith [sq_nonneg M]

private theorem exists_norm_linearLogSelbergMollifiedZetaProduct_le_compact
    (X : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)‖ ≤ M := by
  let f : ℝ → ℂ := fun t =>
    linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)
  have hf : Continuous f := by
    simpa only [f] using continuous_linearLogSelbergMollifiedZetaProduct_critical X
  rcases isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_right 0 M)

/-- For each fixed mollifier length, the critical product has an
unconditional global degree-eight square-growth bound. -/
theorem exists_norm_sq_linearLogSelbergMollifiedZetaProduct_le_polynomial
    {X : ℕ} (hX : 2 ≤ X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)‖ ^ 2 ≤
        C * (|t| + 3) ^ 8 := by
  obtain ⟨M, hM, hcompact⟩ :=
    exists_norm_linearLogSelbergMollifiedZetaProduct_le_compact X
  obtain ⟨Czeta, hCzeta, hzeta⟩ :=
    ZeroFreeRegion.exists_norm_riemannZeta_le_polynomial_on_zero_four
  let B : ℝ := 2 * Czeta * Real.sqrt X
  let C : ℝ := M ^ 2 + B ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t
  let A : ℝ := |t| + 3
  have hA : 1 ≤ A := by dsimp only [A]; linarith [abs_nonneg t]
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  by_cases ht : |t| ≤ 1
  · have hsmall := hcompact t (abs_le.mp ht)
    have hsq :
        ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)‖ ^ 2 ≤
          M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsmall 2
    have hA8 : 1 ≤ A ^ 8 := one_le_pow₀ hA
    calc
      _ ≤ M ^ 2 := hsq
      _ ≤ C := by dsimp only [C]; nlinarith [sq_nonneg B]
      _ ≤ C * A ^ 8 := le_mul_of_one_le_right hC hA8
  · have htHigh : 1 ≤ |t| := le_of_not_ge ht
    have hz := hzeta ((1 / 2 : ℂ) + I * t)
      (by norm_num : (((1 / 2 : ℂ) + I * t).re) ∈ Icc (0 : ℝ) 4)
      (by simpa using htHigh)
    have hz' : ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ≤
        Czeta * (|t| + 3) ^ 4 := by simpa using hz
    have hm := HardyTheorem.norm_selbergMoebiusMollifier_criticalLine_le_two_sqrt hX t
    have hprod :
        ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)‖ ≤
          B * A ^ 4 := by
      rw [linearLogSelbergMollifiedZetaProduct,
        HardyTheorem.linearLogSelbergMollifier_eq_selbergMoebiusMollifier,
        norm_mul]
      dsimp only [B, A]
      calc
        _ ≤ (Czeta * (|t| + 3) ^ 4) * (2 * Real.sqrt X) := by
          exact mul_le_mul hz' hm (norm_nonneg _) (by positivity)
        _ = (2 * Czeta * Real.sqrt X) * (|t| + 3) ^ 4 := by ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hprod 2
    calc
      _ ≤ (B * A ^ 4) ^ 2 := hsq
      _ = B ^ 2 * A ^ 8 := by ring
      _ ≤ C * A ^ 8 := by
        exact mul_le_mul_of_nonneg_right
          (by dsimp only [C]; nlinarith [sq_nonneg M]) (pow_nonneg hA0 _)

/-- Recenter the global polynomial growth bound at an arbitrary Gaussian center. -/
theorem exists_norm_sq_linearLogSelbergMollifiedZetaProduct_le_centeredPolynomial
    {X : ℕ} (hX : 2 ≤ X) (w : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * t)‖ ^ 2 ≤
        C * (1 + |t - w|) ^ 8 := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_norm_sq_linearLogSelbergMollifiedZetaProduct_le_polynomial hX
  let D : ℝ := |w| + 3
  refine ⟨C * D ^ 8, mul_nonneg hC (pow_nonneg (by positivity) 8), ?_⟩
  intro t
  have hshift : |t| + 3 ≤ D * (1 + |t - w|) := by
    have htri : |t| ≤ |t - w| + |w| := by
      calc
        |t| = |(t - w) + w| := by ring_nf
        _ ≤ |t - w| + |w| := abs_add_le _ _
    dsimp only [D]
    nlinarith [abs_nonneg (t - w),
      mul_nonneg (abs_nonneg w) (abs_nonneg (t - w))]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ |t| + 3) hshift 8
  calc
    _ ≤ C * (|t| + 3) ^ 8 := hglobal t
    _ ≤ C * (D * (1 + |t - w|)) ^ 8 := mul_le_mul_of_nonneg_left hpow hC
    _ = (C * D ^ 8) * (1 + |t - w|) ^ 8 := by ring

/-- The full-real-line Gaussian product moment is unconditionally integrable.
This does not yet estimate the two tails. -/
theorem integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaProduct
    {Delta w : ℝ} {X : ℕ} (hDelta : 0 < Delta) (hX : 2 ≤ X) :
    Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct X
        ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_sq_linearLogSelbergMollifiedZetaProduct_le_centeredPolynomial hX w
  have hb : 0 < 1 / Delta ^ 2 := by positivity
  have hpoly := integrable_one_add_abs_pow_mul_exp_neg_mul_sq hb 8
  have hpolyCentered : Integrable fun t : ℝ =>
      (1 + |t - w|) ^ 8 * Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2) :=
    Integrable.comp_sub_right hpoly w
  have hmajor : Integrable fun t : ℝ =>
      C * ((1 + |t - w|) ^ 8 * Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2)) :=
    hpolyCentered.const_mul C
  apply Integrable.mono_nonneg hmajor
  · have hweight : Continuous (carlsonGaussianWeight Delta w) := by
      unfold carlsonGaussianWeight
      fun_prop
    exact (hweight.mul
        ((continuous_linearLogSelbergMollifiedZetaProduct_critical X).norm.pow 2))
      |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  · exact Filter.Eventually.of_forall fun t => by
      have hweight : carlsonGaussianWeight Delta w t =
          Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2) := by
        unfold carlsonGaussianWeight
        congr 1
        field_simp [hDelta.ne']
      rw [hweight]
      calc
        _ ≤ Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2) *
              (C * (1 + |t - w|) ^ 8) := by
          gcongr
          exact hbound t
        _ = C * ((1 + |t - w|) ^ 8 *
              Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2)) := by ring

/-- The part of the full Gaussian product moment outside the central AFE
window. -/
noncomputable def carlsonHalfRangeProductTail
    (Delta w : ℝ) (X : ℕ) (L U : ℝ) : ℝ :=
  ∫ t : ℝ in (Icc L U)ᶜ, carlsonGaussianWeight Delta w t *
    ‖linearLogSelbergMollifiedZetaProduct X
      ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2

/-- Uniform quantitative tail bound before choosing the Carlson scales.  A
distance `D` from the center extracts half of the Gaussian; the remaining
half absorbs the degree-eight polynomial growth. -/
theorem exists_carlsonHalfRangeProductTail_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Delta w D L U : ℝ} {X : ℕ},
      1 ≤ Delta → 0 ≤ D → 2 ≤ X →
      (∀ t ∈ (Icc L U)ᶜ, D ≤ |t - w|) →
      carlsonHalfRangeProductTail Delta w X L U ≤
        C * X * (|w| + 3) ^ 8 *
          Real.exp (-(D ^ 2) / (2 * Delta ^ 2)) *
            Delta ^ 9 * gaussianPolynomialMomentEight := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_uniform_norm_sq_linearLogSelbergMollifiedZetaProduct_le_polynomial
  refine ⟨C, hC, ?_⟩
  intro Delta w D L U X hDelta hD hX hsep
  have hDeltaPos : 0 < Delta := zero_lt_one.trans_le hDelta
  let A : ℝ := C * X * (|w| + 3) ^ 8 *
    Real.exp (-(D ^ 2) / (2 * Delta ^ 2))
  let residual : ℝ → ℝ := fun t =>
    (1 + |t - w|) ^ 8 *
      Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hresidual : Integrable residual := by
    have hb : 0 < 1 / (2 * Delta ^ 2) := by positivity
    simpa only [residual] using Integrable.comp_sub_right
      (integrable_one_add_abs_pow_mul_exp_neg_mul_sq hb 8) w
  have hmajor : Integrable fun t : ℝ => A * residual t :=
    hresidual.const_mul A
  have hactual : IntegrableOn (fun t : ℝ => carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct X
        ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ((Icc L U)ᶜ) :=
    (integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaProduct
      hDeltaPos hX).integrableOn
  have hpoint : ∀ t ∈ (Icc L U)ᶜ,
      carlsonGaussianWeight Delta w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        A * residual t := by
    intro t ht
    have hshift : |t| + 3 ≤ (|w| + 3) * (1 + |t - w|) := by
      have htri : |t| ≤ |t - w| + |w| := by
        calc
          |t| = |(t - w) + w| := by ring_nf
          _ ≤ |t - w| + |w| := abs_add_le _ _
      nlinarith [abs_nonneg w, abs_nonneg (t - w),
        mul_nonneg (abs_nonneg w) (abs_nonneg (t - w))]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ |t| + 3) hshift 8
    have hprod :
        ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
          C * X * (|w| + 3) ^ 8 * (1 + |t - w|) ^ 8 := by
      calc
        _ ≤ C * X * (|t| + 3) ^ 8 := hglobal X hX t
        _ ≤ C * X * ((|w| + 3) * (1 + |t - w|)) ^ 8 := by
          gcongr
        _ = C * X * (|w| + 3) ^ 8 * (1 + |t - w|) ^ 8 := by ring
    have hdistSq : D ^ 2 ≤ (t - w) ^ 2 := by
      have habs := hsep t ht
      nlinarith [sq_abs (t - w)]
    have hhalfExp :
        Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2) ≤
          Real.exp (-(D ^ 2) / (2 * Delta ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hden : 0 < 2 * Delta ^ 2 := by positivity
      have hquot : D ^ 2 / (2 * Delta ^ 2) ≤
          (t - w) ^ 2 / (2 * Delta ^ 2) :=
        div_le_div_of_nonneg_right hdistSq hden.le
      calc
        -(1 / (2 * Delta ^ 2)) * (t - w) ^ 2 =
            -((t - w) ^ 2 / (2 * Delta ^ 2)) := by ring
        _ ≤ -(D ^ 2 / (2 * Delta ^ 2)) := neg_le_neg hquot
        _ = -(D ^ 2) / (2 * Delta ^ 2) := by ring
    have hweight : carlsonGaussianWeight Delta w t =
        Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2) *
          Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2) := by
      unfold carlsonGaussianWeight
      rw [← Real.exp_add]
      congr 1
      field_simp [hDeltaPos.ne']
      ring
    rw [hweight]
    dsimp only [A, residual]
    calc
      _ ≤ (Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2) *
            Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2)) *
          (C * X * (|w| + 3) ^ 8 * (1 + |t - w|) ^ 8) := by
        gcongr
      _ ≤ (Real.exp (-(D ^ 2) / (2 * Delta ^ 2)) *
            Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2)) *
          (C * X * (|w| + 3) ^ 8 * (1 + |t - w|) ^ 8) := by
        gcongr
      _ = C * X * (|w| + 3) ^ 8 *
          Real.exp (-(D ^ 2) / (2 * Delta ^ 2)) *
            ((1 + |t - w|) ^ 8 *
              Real.exp (-(1 / (2 * Delta ^ 2)) * (t - w) ^ 2)) := by ring
  have hset :
      carlsonHalfRangeProductTail Delta w X L U ≤
        ∫ t : ℝ in (Icc L U)ᶜ, A * residual t := by
    unfold carlsonHalfRangeProductTail
    exact setIntegral_mono_on hactual hmajor.integrableOn
      measurableSet_Icc.compl hpoint
  calc
    carlsonHalfRangeProductTail Delta w X L U
        ≤ ∫ t : ℝ in (Icc L U)ᶜ, A * residual t := hset
    _ ≤ ∫ t : ℝ, A * residual t :=
      setIntegral_le_integral hmajor
        (Filter.Eventually.of_forall fun t =>
          mul_nonneg hA (mul_nonneg (pow_nonneg (by positivity) 8)
            (Real.exp_nonneg _)))
    _ = A * ∫ t : ℝ, residual t := by rw [integral_const_mul]
    _ ≤ A * (Delta ^ 9 * gaussianPolynomialMomentEight) := by
      exact mul_le_mul_of_nonneg_left
        (integral_centeredPolynomialEight_mul_halfGaussian_le hDelta) hA
    _ = C * X * (|w| + 3) ^ 8 *
          Real.exp (-(D ^ 2) / (2 * Delta ^ 2)) *
            Delta ^ 9 * gaussianPolynomialMomentEight := by
      dsimp only [A]
      ring

/-- If the center lies in the middle half of `[V,4V]`, its distance from the
complement is at least `V`. -/
theorem halfRange_center_separation
    {V w : ℝ} (hV : 0 ≤ V) (hwLower : 2 * V ≤ w) (hwUpper : w ≤ 3 * V) :
    ∀ t ∈ (Icc V (4 * V))ᶜ, V ≤ |t - w| := by
  intro t ht
  rw [mem_compl_iff, mem_Icc] at ht
  by_cases htLower : t < V
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · have htV : V ≤ t := le_of_not_gt htLower
    have htUpper : 4 * V < t := lt_of_not_ge fun ht4 => ht ⟨htV, ht4⟩
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The uniform tail estimate at the broad half-range scale used by the
critical AFE. -/
theorem exists_carlsonHalfRangeProductTail_le_broadScale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V w : ℝ} {X : ℕ},
      1 ≤ V → 2 * V ≤ w → w ≤ 3 * V → 2 ≤ X →
      carlsonHalfRangeProductTail
          (4 * (4 * V) ^ (19 / 20 : ℝ)) w X V (4 * V) ≤
        C * X * (|w| + 3) ^ 8 *
          Real.exp (-(V ^ 2) /
            (2 * (4 * (4 * V) ^ (19 / 20 : ℝ)) ^ 2)) *
          (4 * (4 * V) ^ (19 / 20 : ℝ)) ^ 9 *
            gaussianPolynomialMomentEight := by
  obtain ⟨C, hC, htail⟩ := exists_carlsonHalfRangeProductTail_le
  refine ⟨C, hC, ?_⟩
  intro V w X hV hwLower hwUpper hX
  have hFourV : 1 ≤ 4 * V := by nlinarith
  have hpow : 1 ≤ (4 * V) ^ (19 / 20 : ℝ) := by
    exact Real.one_le_rpow hFourV (by norm_num)
  have hDelta : 1 ≤ 4 * (4 * V) ^ (19 / 20 : ℝ) := by nlinarith
  exact htail hDelta (zero_le_one.trans hV) hX
    (halfRange_center_separation (zero_le_one.trans hV) hwLower hwUpper)

/-- Exact exponent exposed by the slightly enlarged and algebraically simpler
width `16*V^(19/20)`. -/
theorem halfRange_simpleScale_exponent_identity
    {V : ℝ} (hV : 0 < V) :
    V ^ 2 / (2 * (16 * V ^ (19 / 20 : ℝ)) ^ 2) =
      V ^ (1 / 10 : ℝ) / 512 := by
  have hp : 0 < V ^ (19 / 20 : ℝ) := Real.rpow_pos_of_pos hV _
  have hratio :
      V ^ 2 / (V ^ (19 / 20 : ℝ)) ^ 2 = V ^ (1 / 10 : ℝ) := by
    calc
      V ^ 2 / (V ^ (19 / 20 : ℝ)) ^ 2 =
          V ^ (2 : ℝ) / V ^ ((19 / 20 : ℝ) * 2) := by
        rw [show V ^ 2 = V ^ (2 : ℝ) by norm_num [Real.rpow_natCast],
          show (V ^ (19 / 20 : ℝ)) ^ 2 =
              (V ^ (19 / 20 : ℝ)) ^ (2 : ℝ) by
            norm_num [Real.rpow_natCast],
          Real.rpow_mul hV.le]
      _ = V ^ ((2 : ℝ) - (19 / 20 : ℝ) * 2) := by
        rw [Real.rpow_sub hV]
      _ = V ^ (1 / 10 : ℝ) := by norm_num
  calc
    V ^ 2 / (2 * (16 * V ^ (19 / 20 : ℝ)) ^ 2) =
        (V ^ 2 / (V ^ (19 / 20 : ℝ)) ^ 2) / 512 := by
      field_simp [hp.ne']
      ring
    _ = V ^ (1 / 10 : ℝ) / 512 := by rw [hratio]

/-- A polynomial times the exposed `V^(1/10)` exponential tends to zero. -/
theorem tendsto_pow_eighteen_mul_exp_neg_oneTenth :
    Tendsto (fun V : ℝ => V ^ 18 *
      Real.exp (-(V ^ (1 / 10 : ℝ)) / 512)) atTop (nhds 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (180 : ℝ) (1 / 512 : ℝ) (by norm_num)
  have hscale : Tendsto (fun V : ℝ => V ^ (1 / 10 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hcomp := hbase.comp hscale
  apply hcomp.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
  simp only [Function.comp_apply]
  have hpow : (V ^ (1 / 10 : ℝ)) ^ (180 : ℝ) = V ^ (18 : ℕ) := by
    calc
      _ = V ^ (18 : ℝ) := by
        rw [← Real.rpow_mul hV]
        norm_num
      _ = V ^ (18 : ℕ) := Real.rpow_natCast V 18
  rw [hpow]
  rw [show -(1 / 512 : ℝ) * V ^ (1 / 10 : ℝ) =
      -(V ^ (1 / 10 : ℝ)) / 512 by ring]

/-- At the simple broad scale, the whole tail is bounded by one absolute
constant times a fixed polynomial-exponential function tending to zero. -/
theorem exists_carlsonHalfRangeProductTail_le_simpleScalePolynomial :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {V w : ℝ} {X : ℕ},
      1 ≤ V → 2 * V ≤ w → w ≤ 3 * V → 2 ≤ X →
      (X : ℝ) ≤ V ^ (9 / 20 : ℝ) →
      carlsonHalfRangeProductTail
          (16 * V ^ (19 / 20 : ℝ)) w X V (4 * V) ≤
        A * V ^ 18 * Real.exp (-(V ^ (1 / 10 : ℝ)) / 512) := by
  obtain ⟨C, hC, htail⟩ := exists_carlsonHalfRangeProductTail_le
  let A : ℝ := C * 6 ^ 8 * 16 ^ 9 * gaussianPolynomialMomentEight
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC (pow_nonneg (by norm_num) 8))
        (pow_nonneg (by norm_num) 9))
      gaussianPolynomialMomentEight_nonneg
  refine ⟨A, hA, ?_⟩
  intro V w X hV hwLower hwUpper hX hXscale
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hV0 : 0 ≤ V := hVpos.le
  have hXleV : (X : ℝ) ≤ V := by
    exact hXscale.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hV (by norm_num : (9 / 20 : ℝ) ≤ 1))
  have hw0 : 0 ≤ w := by nlinarith
  have hwLinear : |w| + 3 ≤ 6 * V := by
    rw [abs_of_nonneg hw0]
    nlinarith
  have hpowScale : V ^ (19 / 20 : ℝ) ≤ V := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hV (by norm_num : (19 / 20 : ℝ) ≤ 1)
  have hDelta : 1 ≤ 16 * V ^ (19 / 20 : ℝ) := by
    have : 1 ≤ V ^ (19 / 20 : ℝ) := Real.one_le_rpow hV (by norm_num)
    nlinarith
  have hraw := htail hDelta hV0 hX
    (halfRange_center_separation hV0 hwLower hwUpper)
  have hexp :
      Real.exp (-(V ^ 2) /
          (2 * (16 * V ^ (19 / 20 : ℝ)) ^ 2)) =
        Real.exp (-(V ^ (1 / 10 : ℝ)) / 512) := by
    congr 1
    calc
      -(V ^ 2) / (2 * (16 * V ^ (19 / 20 : ℝ)) ^ 2) =
          -(V ^ 2 / (2 * (16 * V ^ (19 / 20 : ℝ)) ^ 2)) := by ring
      _ = -(V ^ (1 / 10 : ℝ) / 512) := by
        rw [halfRange_simpleScale_exponent_identity hVpos]
      _ = -(V ^ (1 / 10 : ℝ)) / 512 := by ring
  rw [hexp] at hraw
  calc
    carlsonHalfRangeProductTail
          (16 * V ^ (19 / 20 : ℝ)) w X V (4 * V) ≤
        C * X * (|w| + 3) ^ 8 *
          Real.exp (-(V ^ (1 / 10 : ℝ)) / 512) *
          (16 * V ^ (19 / 20 : ℝ)) ^ 9 *
            gaussianPolynomialMomentEight := hraw
    _ ≤ C * V * (6 * V) ^ 8 *
          Real.exp (-(V ^ (1 / 10 : ℝ)) / 512) *
          (16 * V) ^ 9 * gaussianPolynomialMomentEight := by
      gcongr
      exact gaussianPolynomialMomentEight_nonneg
    _ = A * V ^ 18 * Real.exp (-(V ^ (1 / 10 : ℝ)) / 512) := by
      dsimp only [A]
      ring

/-- Uniform negligibility of the middle-half Carlson tail. -/
theorem exists_eventually_carlsonHalfRangeProductTail_le_one_simpleScale :
    ∀ᶠ V : ℝ in atTop, ∀ (w : ℝ) (X : ℕ),
      2 * V ≤ w → w ≤ 3 * V → 2 ≤ X →
      (X : ℝ) ≤ V ^ (9 / 20 : ℝ) →
      carlsonHalfRangeProductTail
          (16 * V ^ (19 / 20 : ℝ)) w X V (4 * V) ≤ 1 := by
  obtain ⟨A, hA, htail⟩ :=
    exists_carlsonHalfRangeProductTail_le_simpleScalePolynomial
  have hlimit : Tendsto (fun V : ℝ => A *
      (V ^ 18 * Real.exp (-(V ^ (1 / 10 : ℝ)) / 512))) atTop (nhds 0) :=
    by simpa using tendsto_pow_eighteen_mul_exp_neg_oneTenth.const_mul A
  have hevent : ∀ᶠ V : ℝ in atTop,
      A * (V ^ 18 * Real.exp (-(V ^ (1 / 10 : ℝ)) / 512)) ≤ 1 :=
    by
      filter_upwards [(tendsto_order.1 hlimit).2 1 (by norm_num)] with V h
      exact h.le
  filter_upwards [eventually_ge_atTop (1 : ℝ), hevent] with V hV hsmall
  intro w X hwLower hwUpper hX hXscale
  exact (htail hV hwLower hwUpper hX hXscale).trans (by
    simpa only [mul_assoc] using hsmall)

/-- The simple width still dominates every half-range AFE product frequency. -/
theorem four_mul_sqrt_fourV_scale_mul_length_le_simpleScale
    {V : ℝ} {X : ℕ} (hV : 1 ≤ V)
    (hX : (X : ℝ) ≤ V ^ (9 / 20 : ℝ)) :
    4 * Real.sqrt ((4 * V) / (2 * Real.pi)) * (X : ℝ) ≤
      16 * V ^ (19 / 20 : ℝ) := by
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hFourV : 1 ≤ 4 * V := by nlinarith
  have hXFour : (X : ℝ) ≤ (4 * V) ^ (9 / 20 : ℝ) :=
    hX.trans (Real.rpow_le_rpow hVpos.le (by nlinarith) (by norm_num))
  have hbase := HardyTheorem.AFE.four_mul_sqrt_scale_mul_length_le_halfRangeDelta
    hFourV hXFour
  have hfourPow : (4 : ℝ) ^ (19 / 20 : ℝ) ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (by norm_num : (19 / 20 : ℝ) ≤ 1)
  have hscale : 4 * (4 * V) ^ (19 / 20 : ℝ) ≤
      16 * V ^ (19 / 20 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hVpos.le]
    have hVp : 0 ≤ V ^ (19 / 20 : ℝ) := Real.rpow_nonneg hVpos.le _
    nlinarith
  exact hbase.trans hscale

/-- Exact central-window plus tail decomposition. -/
theorem integral_gaussian_product_eq_setIntegral_add_tail
    {Delta w L U : ℝ} {X : ℕ} (hDelta : 0 < Delta) (hX : 2 ≤ X) :
    (∫ t : ℝ, carlsonGaussianWeight Delta w t *
      ‖linearLogSelbergMollifiedZetaProduct X
        ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) =
      (∫ t : ℝ in Icc L U, carlsonGaussianWeight Delta w t *
        ‖linearLogSelbergMollifiedZetaProduct X
          ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) +
        carlsonHalfRangeProductTail Delta w X L U := by
  symm
  exact integral_add_compl (s := Icc L U) measurableSet_Icc
    (integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaProduct
      hDelta hX)

/-- Conditional full-line critical product bound at the simple scale.  The
only analytic premise is the symmetric square-root AFE; the Gaussian tail is
now unconditionally absorbed by `1`. -/
theorem integral_gaussian_product_le_halfRange_simpleScale
    (hAFE : HardyTheorem.AFE.zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ᶠ V : ℝ in atTop, ∀ (w : ℝ) (X : ℕ),
      2 * V ≤ w → w ≤ 3 * V → 2 ≤ X →
      (X : ℝ) ≤ V ^ (9 / 20 : ℝ) →
      (∫ t : ℝ,
        carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
        3 * Real.sqrt
          (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2) + 1 := by
  obtain ⟨R, hR, hwindow⟩ :=
    HardyTheorem.AFE.setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange_log
      hAFE
  refine ⟨R, hR, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    exists_eventually_carlsonHalfRangeProductTail_le_one_simpleScale] with
      V hV htail
  intro w X hwLower hwUpper hX hXscale
  have hVpos : 0 < V := by linarith
  have hVone : 1 ≤ V := by linarith
  have hFourV : 4 ≤ 4 * V := by nlinarith
  have hTwoPi : 2 * Real.pi ≤ 4 * V := by
    nlinarith [Real.pi_lt_four]
  obtain ⟨hSqrtOne, hSqrtUpper⟩ :=
    HardyTheorem.AFE.criticalHalfRange_sqrt_scale_bounds hTwoPi hFourV
  have hcentral := hwindow (L := V) (U := 4 * V)
    (Delta := 16 * V ^ (19 / 20 : ℝ))
    (by linarith) (by nlinarith) hX hXscale hSqrtOne hSqrtUpper
    (four_mul_sqrt_fourV_scale_mul_length_le_simpleScale hVone hXscale) w
  have hcentral' :
      (∫ t : ℝ in Icc V (4 * V),
        carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
        3 * Real.sqrt
          (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2) := by
    simpa only [carlsonGaussianWeight,
      linearLogSelbergMollifiedZetaProduct,
      HardyTheorem.linearLogSelbergMollifier_eq_selbergMoebiusMollifier,
      Complex.normSq_eq_norm_sq] using hcentral
  have hDelta : 0 < 16 * V ^ (19 / 20 : ℝ) := by positivity
  calc
    (∫ t : ℝ,
        carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) =
      (∫ t : ℝ in Icc V (4 * V),
        carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) +
        carlsonHalfRangeProductTail
          (16 * V ^ (19 / 20 : ℝ)) w X V (4 * V) :=
      integral_gaussian_product_eq_setIntegral_add_tail
        (L := V) (U := 4 * V) hDelta hX
    _ ≤ 3 * Real.sqrt
          (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2) + 1 :=
      add_le_add hcentral' (htail w X hwLower hwUpper hX hXscale)

/-- The conditional half-range AFE estimate promoted to the full line with
one explicit, and still unestimated, Gaussian tail. -/
theorem integral_gaussian_product_le_halfRange_scale_add_tail
    (hAFE : HardyTheorem.AFE.zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ {X : ℕ} {L U : ℝ},
      1 < L → L ≤ U → 2 ≤ X →
      (X : ℝ) ≤ L ^ (9 / 20 : ℝ) →
      2 * Real.pi ≤ U → 4 ≤ U →
      ∀ w : ℝ,
      (∫ t : ℝ,
        carlsonGaussianWeight (4 * U ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
        3 * Real.sqrt
          (Real.pi / (1 / (4 * U ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log U) ^ 6 + 4 * R ^ 2) +
        carlsonHalfRangeProductTail
          (4 * U ^ (19 / 20 : ℝ)) w X L U := by
  obtain ⟨R, hR, hlocal⟩ :=
    HardyTheorem.AFE.setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange_scale
      hAFE
  refine ⟨R, hR, ?_⟩
  intro X L U hL hLU hX hXscale hTwoPi hFour w
  have hUpos : 0 < U := by linarith
  have hDelta : 0 < 4 * U ^ (19 / 20 : ℝ) := by positivity
  have hcentral := hlocal hL hLU hX hXscale hTwoPi hFour w
  have hcentral' :
      (∫ t : ℝ in Icc L U,
        carlsonGaussianWeight (4 * U ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
        3 * Real.sqrt
          (Real.pi / (1 / (4 * U ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log U) ^ 6 + 4 * R ^ 2) := by
    simpa only [carlsonGaussianWeight,
      linearLogSelbergMollifiedZetaProduct,
      HardyTheorem.linearLogSelbergMollifier_eq_selbergMoebiusMollifier,
      Complex.normSq_eq_norm_sq] using hcentral
  calc
    _ = (∫ t : ℝ in Icc L U,
          carlsonGaussianWeight (4 * U ^ (19 / 20 : ℝ)) w t *
            ‖linearLogSelbergMollifiedZetaProduct X
              ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) +
          carlsonHalfRangeProductTail
            (4 * U ^ (19 / 20 : ℝ)) w X L U :=
      integral_gaussian_product_eq_setIntegral_add_tail
        (L := L) (U := U) hDelta hX
    _ ≤ _ := add_le_add hcentral' (le_refl _)

end CarlsonZeroDensity
end PrimeNumberTheorem
