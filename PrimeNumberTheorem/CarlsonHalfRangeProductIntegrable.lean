import HardyTheorem.AFECriticalHalfRangeScale
import PrimeNumberTheorem.CarlsonConreyCriticalBoundaryReduction
import PrimeNumberTheorem.CarlsonGaussianHilbertMemLp
import ZeroFreeRegion.PhragmenLindelofZeta

/-! # Global Gaussian integrability of the one-scale Carlson product

This is deliberately separate from the quantitative tail estimate.  It uses
only unconditional polynomial zeta growth and the elementary pointwise bound
for the finite Selberg mollifier. -/

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

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
