import PrimeNumberTheorem.VKEdgeFullMovingComplementEnergy

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Sharp energy after deleting a strictly-left finite zero package

A fixed finite package separated by a positive real-part gap from `beta`
decays exponentially after normalization by `exp (beta * y)`.  This module
quantifies that decay and proves that deleting such a package preserves a
fixed fraction of any genuine complementary-zero Gaussian energy lower bound.
-/

/-- Multiplicity-weighted reciprocal-norm mass of a finite complex package. -/
noncomputable def finiteZeroClusterReciprocalMultiplicityMass
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) : ℝ :=
  ∑ rho ∈ S, (multiplicity rho : ℝ) / ‖rho‖

theorem finiteZeroClusterReciprocalMultiplicityMass_nonneg
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) :
    0 ≤ finiteZeroClusterReciprocalMultiplicityMass S multiplicity := by
  unfold finiteZeroClusterReciprocalMultiplicityMass
  exact Finset.sum_nonneg fun _ _ =>
    div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-- A fixed finite package strictly to the left of `beta` is exponentially
small after normalization at `beta`. -/
theorem norm_normalizedFiniteZeroClusterContribution_le_exp_leftGap
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta delta a y : ℝ}
    (hdelta : 0 ≤ delta)
    (ha : 0 ≤ a)
    (hay : a ≤ y)
    (hgap : ∀ rho ∈ S, rho.re ≤ beta - delta) :
    ‖normalizedFiniteZeroClusterContribution
        S multiplicity beta y‖ ≤
      Real.exp (-delta * a) *
        finiteZeroClusterReciprocalMultiplicityMass S multiplicity := by
  classical
  have hy : 0 ≤ y := ha.trans hay
  have hmass :=
    finiteZeroClusterReciprocalMultiplicityMass_nonneg S multiplicity
  unfold normalizedFiniteZeroClusterContribution
  rw [norm_mul]
  have hscalar : ‖((Real.exp (-beta * y) : ℝ) : ℂ)‖ =
      Real.exp (-beta * y) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [hscalar]
  calc
    Real.exp (-beta * y) *
          ‖∑ rho ∈ S,
              (multiplicity rho : ℂ) *
                (Real.exp y : ℂ) ^ rho / rho‖ ≤
        Real.exp (-beta * y) *
          ∑ rho ∈ S,
            ‖(multiplicity rho : ℂ) *
              (Real.exp y : ℂ) ^ rho / rho‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
    _ = Real.exp (-beta * y) *
          ∑ rho ∈ S,
            (multiplicity rho : ℝ) *
              (Real.exp y) ^ rho.re / ‖rho‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro rho hrho
      exact
        ZeroForcedOscillation.norm_natCast_mul_cpow_div
          (Real.exp y) (Real.exp_pos y) rho (multiplicity rho)
    _ ≤ Real.exp (-beta * y) *
          ∑ rho ∈ S,
            (multiplicity rho : ℝ) *
              Real.exp ((beta - delta) * y) / ‖rho‖ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.sum_le_sum
      intro rho hrho
      have hexp : (Real.exp y) ^ rho.re ≤
          Real.exp ((beta - delta) * y) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp,
          mul_comm y rho.re]
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (hgap rho hrho) hy)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _))
        (norm_nonneg rho)
    _ = Real.exp (-delta * y) *
          finiteZeroClusterReciprocalMultiplicityMass S multiplicity := by
      unfold finiteZeroClusterReciprocalMultiplicityMass
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      have hexpMul :
          Real.exp (-beta * y) * Real.exp ((beta - delta) * y) =
            Real.exp (-delta * y) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (-beta * y) *
              ((multiplicity rho : ℝ) *
                Real.exp ((beta - delta) * y) / ‖rho‖) =
            ((multiplicity rho : ℝ) / ‖rho‖) *
              (Real.exp (-beta * y) *
                Real.exp ((beta - delta) * y)) := by ring
        _ = ((multiplicity rho : ℝ) / ‖rho‖) *
              Real.exp (-delta * y) := by rw [hexpMul]
        _ = Real.exp (-delta * y) *
              ((multiplicity rho : ℝ) / ‖rho‖) := by ring
    _ ≤ Real.exp (-delta * a) *
          finiteZeroClusterReciprocalMultiplicityMass S multiplicity := by
      apply mul_le_mul_of_nonneg_right _ hmass
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hay (neg_nonpos.mpr hdelta)

private theorem continuous_normalizedFiniteZeroClusterContribution_leftGap
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (beta : ℝ) :
    Continuous (normalizedFiniteZeroClusterContribution S multiplicity beta) := by
  rw [show normalizedFiniteZeroClusterContribution S multiplicity beta =
      fun y =>
        MathlibAux.driftingExponentialPolynomial S
          (finiteZeroClusterCoefficientAt multiplicity beta 0)
          Complex.im (fun rho => rho.re - beta) 0 y by
    funext y
    exact normalizedFiniteZeroClusterContribution_eq_drifting
      S multiplicity beta 0 y]
  unfold MathlibAux.driftingExponentialPolynomial
  fun_prop

/-- Gaussian second moment of a fixed strictly-left package inherits the
square of its pointwise exponential bound. -/
theorem
    normalizedFiniteZeroClusterContributionForwardGaussianSecondMoment_le_exp_leftGap
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta delta a m L : ℝ}
    (hdelta : 0 ≤ delta)
    (ha : 0 ≤ a)
    (hm : 0 < m)
    (_hL : 0 ≤ L)
    (hgap : ∀ rho ∈ S, rho.re ≤ beta - delta) :
    (∫ t : ℝ in Set.Icc 0 L,
        normalizedGaussian m t *
          ‖normalizedFiniteZeroClusterContribution
            S multiplicity beta (a + t)‖ ^ 2) ≤
      (Real.exp (-delta * a) *
        finiteZeroClusterReciprocalMultiplicityMass S multiplicity) ^ 2 := by
  let B : ℝ := Real.exp (-delta * a) *
    finiteZeroClusterReciprocalMultiplicityMass S multiplicity
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le
    (finiteZeroClusterReciprocalMultiplicityMass_nonneg S multiplicity)
  have hweight : Continuous (normalizedGaussian m) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_normalizedGaussian hm t).continuousAt
  have hselected : Continuous (fun t : ℝ =>
      normalizedFiniteZeroClusterContribution
        S multiplicity beta (a + t)) :=
    (continuous_normalizedFiniteZeroClusterContribution_leftGap
      S multiplicity beta).comp (continuous_const.add continuous_id)
  have hleftInt : IntegrableOn (fun t : ℝ =>
      normalizedGaussian m t *
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta (a + t)‖ ^ 2) (Set.Icc 0 L) :=
    (hweight.mul (hselected.norm.pow 2)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hrightInt : IntegrableOn
      (fun t : ℝ => normalizedGaussian m t * B ^ 2)
      (Set.Icc 0 L) := by
    simpa [mul_comm] using
      ((integrable_normalizedGaussian hm).const_mul (B ^ 2)).integrableOn
  have hpoint : ∀ t ∈ Set.Icc 0 L,
      normalizedGaussian m t *
          ‖normalizedFiniteZeroClusterContribution
            S multiplicity beta (a + t)‖ ^ 2 ≤
        normalizedGaussian m t * B ^ 2 := by
    intro t ht
    have hnorm :=
      norm_normalizedFiniteZeroClusterContribution_le_exp_leftGap
        (S := S) (multiplicity := multiplicity) (beta := beta)
        (delta := delta) (a := a) (y := a + t)
        hdelta ha (by linarith [ht.1]) hgap
    have hsquare :
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta (a + t)‖ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    exact mul_le_mul_of_nonneg_left hsquare
      (normalizedGaussian_pos hm t).le
  have hmono :=
    setIntegral_mono_on hleftInt hrightInt measurableSet_Icc hpoint
  calc
    (∫ t : ℝ in Set.Icc 0 L,
        normalizedGaussian m t *
          ‖normalizedFiniteZeroClusterContribution
            S multiplicity beta (a + t)‖ ^ 2) ≤
        ∫ t : ℝ in Set.Icc 0 L,
          normalizedGaussian m t * B ^ 2 := hmono
    _ ≤ ∫ t : ℝ, normalizedGaussian m t * B ^ 2 :=
      setIntegral_le_integral
        (by simpa [mul_comm] using
          (integrable_normalizedGaussian hm).const_mul (B ^ 2))
        (Filter.Eventually.of_forall fun t =>
          mul_nonneg (normalizedGaussian_pos hm t).le (sq_nonneg B))
    _ = B ^ 2 := by
      rw [MeasureTheory.integral_mul_const,
        integral_normalizedGaussian hm, one_mul]

/-- The full finite-height normalized zero sum splits into a selected finite
package and its actual complement. -/
theorem
    normalizedFiniteZeroClusterComplementContribution_empty_eq_selected_add_complement
    {S : Finset ℂ} {T beta y : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    normalizedFiniteZeroClusterComplementContribution ∅ T beta y =
      normalizedFiniteZeroClusterContribution S
          (analyticOrderNatAt riemannZeta) beta y +
        normalizedFiniteZeroClusterComplementContribution S T beta y := by
  have hsplit :=
    finiteNontrivialZeroSumWithMultiplicity_eq_cluster_add_complement
      (S := S) (x := Real.exp y) (T := T) hS
  have hempty :
      finiteZeroClusterComplementContribution ∅ (Real.exp y) T =
        finiteNontrivialZeroSumWithMultiplicity (Real.exp y) T := by
    simp [finiteZeroClusterComplementContribution,
      finiteNontrivialZeroSumWithMultiplicity]
  unfold normalizedFiniteZeroClusterComplementContribution
    normalizedFiniteZeroClusterContribution
  rw [hempty]
  rw [hsplit]
  ring

private theorem continuous_normalizedFiniteZeroClusterComplementContribution_leftGap
    (S : Finset ℂ) (T beta : ℝ) :
    Continuous (normalizedFiniteZeroClusterComplementContribution S T beta) := by
  rw [show normalizedFiniteZeroClusterComplementContribution S T beta =
      normalizedFiniteZeroClusterContribution
        (nontrivialZerosFinset T \ S)
        (analyticOrderNatAt riemannZeta) beta by
    funext y
    rfl]
  exact continuous_normalizedFiniteZeroClusterContribution_leftGap
    (nontrivialZerosFinset T \ S)
      (analyticOrderNatAt riemannZeta) beta

/-- Deleting a strictly-left finite package preserves one quarter of a full
Gaussian energy lower bound once the deleted package has at most one quarter
of that energy. -/
theorem
    normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment_gt_quarter_of_leftGap
    {S : Finset ℂ} {T beta delta a m L C : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hdelta : 0 ≤ delta)
    (ha : 0 ≤ a)
    (hm : 0 < m)
    (hL : 0 ≤ L)
    (hgap : ∀ rho ∈ S, rho.re ≤ beta - delta)
    (hfull : C <
      ∫ t : ℝ in Set.Icc 0 L,
        normalizedGaussian m t *
          ‖normalizedFiniteZeroClusterComplementContribution
            ∅ T beta (a + t)‖ ^ 2)
    (hsmall :
      (Real.exp (-delta * a) *
          finiteZeroClusterReciprocalMultiplicityMass
            S (analyticOrderNatAt riemannZeta)) ^ 2 ≤ C / 4) :
    C / 4 <
      ∫ t : ℝ in Set.Icc 0 L,
        normalizedGaussian m t *
          ‖normalizedFiniteZeroClusterComplementContribution
            S T beta (a + t)‖ ^ 2 := by
  let selected : ℝ → ℂ := fun t =>
    normalizedFiniteZeroClusterContribution S
      (analyticOrderNatAt riemannZeta) beta (a + t)
  let remaining : ℝ → ℂ := fun t =>
    normalizedFiniteZeroClusterComplementContribution S T beta (a + t)
  let full : ℝ → ℂ := fun t =>
    normalizedFiniteZeroClusterComplementContribution ∅ T beta (a + t)
  let weight : ℝ → ℝ := normalizedGaussian m
  have hdecomp (t : ℝ) : full t = selected t + remaining t := by
    exact
      normalizedFiniteZeroClusterComplementContribution_empty_eq_selected_add_complement
        hS
  have hweight : Continuous weight :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_normalizedGaussian hm t).continuousAt
  have hselected : Continuous selected :=
    (continuous_normalizedFiniteZeroClusterContribution_leftGap
      S (analyticOrderNatAt riemannZeta) beta).comp
        (continuous_const.add continuous_id)
  have hremaining : Continuous remaining :=
    (continuous_normalizedFiniteZeroClusterComplementContribution_leftGap
      S T beta).comp (continuous_const.add continuous_id)
  have hfullContinuous : Continuous full :=
    (continuous_normalizedFiniteZeroClusterComplementContribution_leftGap
      ∅ T beta).comp (continuous_const.add continuous_id)
  have hfullInt : IntegrableOn
      (fun t => weight t * ‖full t‖ ^ 2) (Set.Icc 0 L) :=
    (hweight.mul (hfullContinuous.norm.pow 2)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hupperInt : IntegrableOn
      (fun t => 2 * (weight t * ‖selected t‖ ^ 2) +
        2 * (weight t * ‖remaining t‖ ^ 2)) (Set.Icc 0 L) := by
    exact
      ((continuous_const.mul
          (hweight.mul (hselected.norm.pow 2))).add
        (continuous_const.mul
          (hweight.mul (hremaining.norm.pow 2)))).continuousOn.integrableOn_compact
        isCompact_Icc
  have hpoint : ∀ t ∈ Set.Icc 0 L,
      weight t * ‖full t‖ ^ 2 ≤
        2 * (weight t * ‖selected t‖ ^ 2) +
          2 * (weight t * ‖remaining t‖ ^ 2) := by
    intro t ht
    have htriangle : ‖full t‖ ≤ ‖selected t‖ + ‖remaining t‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    have hsquare : ‖full t‖ ^ 2 ≤
        2 * ‖selected t‖ ^ 2 + 2 * ‖remaining t‖ ^ 2 := by
      nlinarith [norm_nonneg (full t), norm_nonneg (selected t),
        norm_nonneg (remaining t),
        sq_nonneg (‖selected t‖ - ‖remaining t‖)]
    have hw := (normalizedGaussian_pos hm t).le
    dsimp [weight]
    nlinarith
  have hmono :=
    setIntegral_mono_on hfullInt hupperInt measurableSet_Icc hpoint
  have hselectedUpper :=
    normalizedFiniteZeroClusterContributionForwardGaussianSecondMoment_le_exp_leftGap
      (S := S) (multiplicity := analyticOrderNatAt riemannZeta)
      (beta := beta) (delta := delta) (a := a) (m := m) (L := L)
      hdelta ha hm hL hgap
  have hsplit :
      (∫ t : ℝ in Set.Icc 0 L,
          (2 * (weight t * ‖selected t‖ ^ 2) +
            2 * (weight t * ‖remaining t‖ ^ 2))) =
        2 * (∫ t : ℝ in Set.Icc 0 L,
          weight t * ‖selected t‖ ^ 2) +
        2 * (∫ t : ℝ in Set.Icc 0 L,
          weight t * ‖remaining t‖ ^ 2) := by
    rw [MeasureTheory.integral_add]
    · simp_rw [MeasureTheory.integral_const_mul]
    · exact
        ((hweight.mul (hselected.norm.pow 2)).continuousOn.integrableOn_compact
          isCompact_Icc).const_mul 2
    · exact
        ((hweight.mul (hremaining.norm.pow 2)).continuousOn.integrableOn_compact
          isCompact_Icc).const_mul 2
  dsimp [full, weight] at hmono hfull
  rw [hsplit] at hmono
  dsimp [selected, remaining, weight] at hmono hselectedUpper ⊢
  nlinarith

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
