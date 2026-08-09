import PrimeNumberTheorem.VKEdgeDynamicMaximalLayer
import PrimeNumberTheorem.VKEdgeZeroClusterApproximationL2

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# The full moving complementary-zero energy

The dynamic packet API accepts an arbitrary finite set `K` of ordinate
buckets.  This module supplies the canonical choice containing every
finite-height zero outside the selected set `S`, proves that the resulting
moving packet is exactly the complementary term in the actual explicit
formula, and transfers a lower bound for the concrete no-jump remainder to
that full moving energy.

The transfer still requires a lower bound for the true remainder energy.
It does not produce a zero-density contradiction or a zero-free theorem.
-/

/-- The unit ordinate buckets actually occupied by finite-height zeros
outside the selected set `S`. -/
noncomputable def dynamicComplementFullBucketSet
    (S : Finset ℂ) (T : ℝ) : Finset ℕ :=
  (nontrivialZerosFinset T \ S).image
    (fun rho => Nat.floor |rho.im|)

/-- A dynamic unit bucket is exactly the corresponding floor fiber of the
finite-height complement. -/
theorem dynamicComplementZeroPacket_eq_floorFiber
    (S : Finset ℂ) (T : ℝ) (n : ℕ) :
    dynamicComplementZeroPacket S T n =
      (nontrivialZerosFinset T \ S).filter
        (fun rho => Nat.floor |rho.im| = n) := by
  classical
  ext rho
  constructor
  · intro hrho
    rcases Finset.mem_inter.mp hrho with ⟨hbucket, hcomplement⟩
    rcases Finset.mem_filter.mp hbucket with
      ⟨hwide, hlow, hhigh⟩
    rcases Finset.mem_sdiff.mp hcomplement with ⟨hT, hnotS⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hT, hnotS⟩, ?_⟩
    exact
      (Nat.floor_eq_iff (abs_nonneg rho.im)).2
        ⟨hlow, hhigh⟩
  · intro hrho
    rcases Finset.mem_filter.mp hrho with ⟨hcomplement, hfloor⟩
    rcases Finset.mem_sdiff.mp hcomplement with ⟨hT, hnotS⟩
    rcases mem_nontrivialZerosFinset.mp hT with ⟨hzero, himT⟩
    have hfloorBounds :=
      (Nat.floor_eq_iff (abs_nonneg rho.im)).1 hfloor
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, hfloorBounds.1,
      hfloorBounds.2⟩, Finset.mem_sdiff.mpr ⟨hT, hnotS⟩⟩
    apply mem_nontrivialZerosFinset.mpr
    refine ⟨hzero, ?_⟩
    linarith

/-- With the occupied floor fibers as `K`, the dynamic moving packet is
exactly the complete normalized complementary-zero contribution. -/
theorem dynamicComplementMovingPacketContribution_fullBucketSet
    (S : Finset ℂ) (T beta a y : ℝ) :
    dynamicComplementMovingPacketContribution S T beta a
        (dynamicComplementFullBucketSet S T) y =
      normalizedFiniteZeroClusterComplementContribution S T beta y := by
  classical
  let Z : Finset ℂ := nontrivialZerosFinset T \ S
  let f : ℂ → ℂ := fun rho =>
    finiteZeroClusterCoefficientAt
        (analyticOrderNatAt riemannZeta) beta a rho *
      (Real.exp ((rho.re - beta) * (y - a)) : ℂ) *
        Complex.exp (I * (rho.im * y))
  have hmaps (rho : ℂ) (hrho : rho ∈ Z) :
      Nat.floor |rho.im| ∈ dynamicComplementFullBucketSet S T := by
    apply Finset.mem_image.mpr
    exact ⟨rho, hrho, rfl⟩
  have hfiber :
      (∑ rho ∈ Z, f rho) =
        ∑ n ∈ dynamicComplementFullBucketSet S T,
          ∑ rho ∈ Z.filter
            (fun rho => Nat.floor |rho.im| = n),
            f rho := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  change
    dynamicComplementMovingPacketContribution S T beta a
        (dynamicComplementFullBucketSet S T) y =
      normalizedFiniteZeroClusterContribution Z
        (analyticOrderNatAt riemannZeta) beta y
  rw [normalizedFiniteZeroClusterContribution_eq_drifting]
  unfold dynamicComplementMovingPacketContribution
    dynamicComplementPacketIndexSet
    MathlibAux.driftingExponentialPolynomial
  rw [Finset.sum_sigma]
  simp_rw [dynamicComplementZeroPacket_eq_floorFiber]
  simpa [Z, f] using hfiber.symm

/-- Forward Gaussian energy of the complete normalized complementary-zero
term in the actual finite-height explicit formula. -/
noncomputable def
    normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment
    (S : Finset ℂ) (T beta a m L : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Icc 0 L,
    normalizedGaussian m t *
      ‖normalizedFiniteZeroClusterComplementContribution
        S T beta (a + t)‖ ^ 2

/-- The canonical full-bucket dynamic energy is exactly the actual
complementary-zero Gaussian second moment. -/
theorem
    dynamicComplementForwardMovingGaussianSecondMoment_fullBucketSet
    (S : Finset ℂ) (T beta a m L : ℝ) :
    dynamicComplementForwardMovingGaussianSecondMoment
        S T beta a (dynamicComplementFullBucketSet S T) m L =
      normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment
        S T beta a m L := by
  unfold dynamicComplementForwardMovingGaussianSecondMoment
    normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [dynamicComplementMovingPacketContribution_fullBucketSet]

/-- Forward Gaussian energy of the concrete no-jump selected-cluster
explicit-formula remainder.  The deleted midpoint jump is null on logarithmic
Lebesgue measure by `normalizedFiniteZeroClusterPsiRemainder_ae_eq_withoutJump`.
-/
noncomputable def
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
    (S : Finset ℂ) (T beta a m L : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Icc 0 L,
    normalizedGaussian m t *
      ‖normalizedFiniteZeroClusterPsiRemainderWithoutJump
        S T beta (a + t)‖ ^ 2

private theorem
    continuous_normalizedFiniteZeroClusterComplementContribution
    (S : Finset ℂ) (T beta : ℝ) :
    Continuous
      (normalizedFiniteZeroClusterComplementContribution S T beta) := by
  rw [show
      normalizedFiniteZeroClusterComplementContribution S T beta =
        normalizedFiniteZeroClusterContribution
          (nontrivialZerosFinset T \ S)
          (analyticOrderNatAt riemannZeta) beta by
    funext y
    rfl]
  rw [show
      normalizedFiniteZeroClusterContribution
          (nontrivialZerosFinset T \ S)
          (analyticOrderNatAt riemannZeta) beta =
        fun y =>
          MathlibAux.driftingExponentialPolynomial
            (nontrivialZerosFinset T \ S)
            (finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta 0)
            Complex.im (fun rho => rho.re - beta) 0 y by
    funext y
    exact
      normalizedFiniteZeroClusterContribution_eq_drifting
        (nontrivialZerosFinset T \ S)
        (analyticOrderNatAt riemannZeta) beta 0 y]
  unfold MathlibAux.driftingExponentialPolynomial
  fun_prop

private theorem
    normSq_normalizedFiniteZeroClusterPsiRemainderWithoutJump_le_components
    (S : Finset ℂ) (T beta y : ℝ) :
    ‖normalizedFiniteZeroClusterPsiRemainderWithoutJump
        S T beta y‖ ^ 2 ≤
      3 *
        (‖normalizedFiniteZeroClusterComplementContribution
            S T beta y‖ ^ 2 +
          ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ^ 2 +
          ‖normalizedZeroPackageClosedTerms beta y‖ ^ 2) := by
  rw [normalizedFiniteZeroClusterPsiRemainderWithoutJump_eq_components]
  let A :=
    ‖normalizedFiniteZeroClusterComplementContribution S T beta y‖
  let B :=
    ‖normalizedFiniteZeroClusterApproximationError T beta y‖
  let C :=
    ‖normalizedZeroPackageClosedTerms beta y‖
  have htriangle :
      ‖normalizedFiniteZeroClusterComplementContribution S T beta y +
          normalizedFiniteZeroClusterApproximationError T beta y +
          normalizedZeroPackageClosedTerms beta y‖ ≤
        A + B + C := by
    calc
      ‖normalizedFiniteZeroClusterComplementContribution S T beta y +
          normalizedFiniteZeroClusterApproximationError T beta y +
          normalizedZeroPackageClosedTerms beta y‖ ≤
          ‖normalizedFiniteZeroClusterComplementContribution S T beta y +
            normalizedFiniteZeroClusterApproximationError T beta y‖ +
            ‖normalizedZeroPackageClosedTerms beta y‖ :=
        norm_add_le _ _
      _ ≤
          (‖normalizedFiniteZeroClusterComplementContribution S T beta y‖ +
            ‖normalizedFiniteZeroClusterApproximationError T beta y‖) +
            ‖normalizedZeroPackageClosedTerms beta y‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
      _ = A + B + C := rfl
  have hsumSq :
      (A + B + C) ^ 2 ≤ 3 * (A ^ 2 + B ^ 2 + C ^ 2) := by
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - C),
      sq_nonneg (B - C)]
  have hnormNonneg :
      0 ≤
        ‖normalizedFiniteZeroClusterComplementContribution S T beta y +
          normalizedFiniteZeroClusterApproximationError T beta y +
          normalizedZeroPackageClosedTerms beta y‖ :=
    norm_nonneg _
  dsimp [A, B, C] at hsumSq
  nlinarith

/-- Uniform control of the approximation and closed terms transfers the
concrete no-jump remainder energy to the complete moving complementary-zero
energy.  No zero-spacing or zero-density hypothesis is used. -/
theorem
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment_le_fullMoving_add_uniformErrors
    {S : Finset ℂ} {T beta a m L eta : ℝ}
    (hm : 0 < m)
    (hbeta : 0 ≤ beta)
    (ha : 1 ≤ a)
    (heta : 0 ≤ eta)
    (happrox :
      ∀ y ∈ Set.Icc a (a + L),
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ≤ eta) :
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
        S T beta a m L ≤
      3 *
          dynamicComplementForwardMovingGaussianSecondMoment
            S T beta a (dynamicComplementFullBucketSet S T) m L +
        3 *
          (eta ^ 2 +
            (Real.exp (-beta * a) *
              zeroPackageClosedTermsUniformBound) ^ 2) := by
  let weight : ℝ → ℝ := normalizedGaussian m
  let complement : ℝ → ℂ := fun t =>
    normalizedFiniteZeroClusterComplementContribution
      S T beta (a + t)
  let residual : ℝ → ℂ := fun t =>
    normalizedFiniteZeroClusterPsiRemainderWithoutJump
      S T beta (a + t)
  let closedBound : ℝ :=
    Real.exp (-beta * a) * zeroPackageClosedTermsUniformBound
  have hweightContinuous : Continuous weight := by
    dsimp [weight]
    exact continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_normalizedGaussian hm t).continuousAt
  have hcomplementContinuous : Continuous complement := by
    dsimp [complement]
    exact
      (continuous_normalizedFiniteZeroClusterComplementContribution
        S T beta).comp (continuous_const.add continuous_id)
  have hcomplementInt :
      IntegrableOn
        (fun t => weight t * ‖complement t‖ ^ 2)
        (Set.Icc 0 L) := by
    exact
      (hweightContinuous.mul
        (hcomplementContinuous.norm.pow 2)).continuousOn.integrableOn_compact
          isCompact_Icc
  have hconstInt :
      IntegrableOn
        (fun t => weight t * (eta ^ 2 + closedBound ^ 2))
        (Set.Icc 0 L) := by
    simpa [weight, mul_comm] using
      ((integrable_normalizedGaussian hm).const_mul
        (eta ^ 2 + closedBound ^ 2)).integrableOn
  have hupperInt :
      IntegrableOn
        (fun t =>
          3 * (weight t * ‖complement t‖ ^ 2) +
            3 * (weight t * (eta ^ 2 + closedBound ^ 2)))
        (Set.Icc 0 L) :=
    (hcomplementInt.const_mul 3).add (hconstInt.const_mul 3)
  have hpoint :
      ∀ t ∈ Set.Icc 0 L,
        weight t * ‖residual t‖ ^ 2 ≤
          3 * (weight t * ‖complement t‖ ^ 2) +
            3 * (weight t * (eta ^ 2 + closedBound ^ 2)) := by
    intro t ht
    have hy : a + t ∈ Set.Icc a (a + L) := by
      constructor <;> linarith [ht.1, ht.2]
    have hclosed :
        ‖normalizedZeroPackageClosedTerms beta (a + t)‖ ≤
          closedBound := by
      dsimp [closedBound]
      exact
        norm_normalizedZeroPackageClosedTerms_le_uniformBound
          hbeta ha (by linarith [ht.1])
    have hcomponents :=
      normSq_normalizedFiniteZeroClusterPsiRemainderWithoutJump_le_components
        S T beta (a + t)
    have happroxSq :
        ‖normalizedFiniteZeroClusterApproximationError
            T beta (a + t)‖ ^ 2 ≤ eta ^ 2 := by
      nlinarith [happrox (a + t) hy,
        norm_nonneg
          (normalizedFiniteZeroClusterApproximationError
            T beta (a + t))]
    have hclosedSq :
        ‖normalizedZeroPackageClosedTerms beta (a + t)‖ ^ 2 ≤
          closedBound ^ 2 := by
      nlinarith [hclosed,
        norm_nonneg (normalizedZeroPackageClosedTerms beta (a + t))]
    have hinside :
        ‖residual t‖ ^ 2 ≤
          3 *
            (‖complement t‖ ^ 2 +
              eta ^ 2 + closedBound ^ 2) := by
      dsimp [residual, complement]
      linarith
    have hweightNonneg : 0 ≤ weight t := by
      dsimp [weight]
      exact (normalizedGaussian_pos hm t).le
    calc
      weight t * ‖residual t‖ ^ 2 ≤
          weight t *
            (3 *
              (‖complement t‖ ^ 2 +
                eta ^ 2 + closedBound ^ 2)) :=
        mul_le_mul_of_nonneg_left hinside hweightNonneg
      _ =
          3 * (weight t * ‖complement t‖ ^ 2) +
            3 * (weight t * (eta ^ 2 + closedBound ^ 2)) := by
        ring
  have hmono :
      (∫ t : ℝ in Set.Icc 0 L,
          weight t * ‖residual t‖ ^ 2) ≤
        ∫ t : ℝ in Set.Icc 0 L,
          (3 * (weight t * ‖complement t‖ ^ 2) +
            3 * (weight t * (eta ^ 2 + closedBound ^ 2))) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · filter_upwards with t
      exact mul_nonneg
        (normalizedGaussian_pos hm t).le (sq_nonneg _)
    · exact hupperInt
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hpoint t ht
  have hsplit :
      (∫ t : ℝ in Set.Icc 0 L,
          (3 * (weight t * ‖complement t‖ ^ 2) +
            3 * (weight t * (eta ^ 2 + closedBound ^ 2)))) =
        3 *
            (∫ t : ℝ in Set.Icc 0 L,
              weight t * ‖complement t‖ ^ 2) +
          3 * (eta ^ 2 + closedBound ^ 2) *
            (∫ t : ℝ in Set.Icc 0 L, weight t) := by
    calc
      (∫ t : ℝ in Set.Icc 0 L,
          (3 * (weight t * ‖complement t‖ ^ 2) +
            3 * (weight t * (eta ^ 2 + closedBound ^ 2)))) =
          (∫ t : ℝ in Set.Icc 0 L,
            3 * (weight t * ‖complement t‖ ^ 2)) +
          ∫ t : ℝ in Set.Icc 0 L,
            3 * (weight t * (eta ^ 2 + closedBound ^ 2)) :=
        MeasureTheory.integral_add
          (hcomplementInt.const_mul 3) (hconstInt.const_mul 3)
      _ =
          3 *
              (∫ t : ℝ in Set.Icc 0 L,
                weight t * ‖complement t‖ ^ 2) +
            3 * (eta ^ 2 + closedBound ^ 2) *
              (∫ t : ℝ in Set.Icc 0 L, weight t) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_mul_const]
        ring
  have hweightMass :
      (∫ t : ℝ in Set.Icc 0 L, weight t) ≤ 1 := by
    calc
      (∫ t : ℝ in Set.Icc 0 L, weight t) ≤
          ∫ t : ℝ, weight t :=
        setIntegral_le_integral
          (by simpa [weight] using integrable_normalizedGaussian hm)
          (Filter.Eventually.of_forall fun t => by
            dsimp [weight]
            exact (normalizedGaussian_pos hm t).le)
      _ = 1 := by
        simpa [weight] using integral_normalizedGaussian hm
  have herrorNonneg :
      0 ≤ 3 * (eta ^ 2 + closedBound ^ 2) := by positivity
  have hupper :
      (∫ t : ℝ in Set.Icc 0 L,
          weight t * ‖residual t‖ ^ 2) ≤
        3 *
            (∫ t : ℝ in Set.Icc 0 L,
              weight t * ‖complement t‖ ^ 2) +
          3 * (eta ^ 2 + closedBound ^ 2) := by
    calc
      (∫ t : ℝ in Set.Icc 0 L,
          weight t * ‖residual t‖ ^ 2) ≤ _ := hmono
      _ =
          3 *
              (∫ t : ℝ in Set.Icc 0 L,
                weight t * ‖complement t‖ ^ 2) +
            3 * (eta ^ 2 + closedBound ^ 2) *
              (∫ t : ℝ in Set.Icc 0 L, weight t) := hsplit
      _ ≤
          3 *
              (∫ t : ℝ in Set.Icc 0 L,
                weight t * ‖complement t‖ ^ 2) +
            3 * (eta ^ 2 + closedBound ^ 2) :=
        by
          have hmass :=
            mul_le_of_le_one_right herrorNonneg hweightMass
          linarith
  change
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
        S T beta a m L ≤
      3 *
          normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment
            S T beta a m L +
        3 *
          (eta ^ 2 +
            (Real.exp (-beta * a) *
              zeroPackageClosedTermsUniformBound) ^ 2) at hupper
  rw [←
    dynamicComplementForwardMovingGaussianSecondMoment_fullBucketSet] at hupper
  exact hupper

/-- Any lower bound `R` for the concrete normalized remainder energy forces
a lower bound for the complete moving complementary-zero energy after paying
only the finite-height approximation and closed-term budgets. -/
theorem dynamicComplementFullMovingGaussianSecondMoment_ge_of_normalizedRemainder
    {S : Finset ℂ} {T beta a m L eta R : ℝ}
    (hm : 0 < m)
    (hbeta : 0 ≤ beta)
    (ha : 1 ≤ a)
    (heta : 0 ≤ eta)
    (happrox :
      ∀ y ∈ Set.Icc a (a + L),
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ≤ eta)
    (hR :
      R ≤
        normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          S T beta a m L) :
    (1 / 3 : ℝ) * R -
        (eta ^ 2 +
          (Real.exp (-beta * a) *
            zeroPackageClosedTermsUniformBound) ^ 2) ≤
      dynamicComplementForwardMovingGaussianSecondMoment
        S T beta a (dynamicComplementFullBucketSet S T) m L := by
  have hupper :=
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment_le_fullMoving_add_uniformErrors
      (S := S) hm hbeta ha heta happrox
  linarith

/-- The existing uniform good-height theorem discharges the finite-height
approximation input in the full moving-energy transfer on every sufficiently
late fixed logarithmic window. -/
theorem
    eventually_exists_goodHeight_normalizedRemainder_to_fullMovingGaussianEnergy
    {S : Finset ℂ} {beta L m eta : ℝ}
    (hbeta : 1 / 2 < beta)
    (hbeta1 : beta < 1)
    (hL : 0 ≤ L)
    (hm : 0 < m)
    (heta : 0 < eta) :
    ∀ᶠ a in atTop,
      ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
        ExplicitFormulaAux.goodHeight T ∧
          (1 / 3 : ℝ) *
                normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                  S T beta a m L -
              (eta ^ 2 +
                (Real.exp (-beta * a) *
                  zeroPackageClosedTermsUniformBound) ^ 2) ≤
            dynamicComplementForwardMovingGaussianSecondMoment
              S T beta a (dynamicComplementFullBucketSet S T) m L := by
  have hselect :=
    ExplicitFormulaResidues.eventually_exists_uniform_goodHeight_normalized_window_remainder_lt
      hbeta hbeta1 hL heta
  have haOne : ∀ᶠ a : ℝ in atTop, 1 ≤ a :=
    eventually_ge_atTop 1
  filter_upwards [hselect, haOne] with a hselectA ha
  rcases hselectA with ⟨T, hTmem, hgood, hpoint⟩
  refine ⟨T, hTmem, hgood, ?_⟩
  apply
    dynamicComplementFullMovingGaussianSecondMoment_ge_of_normalizedRemainder
      hm (by linarith) ha heta.le
  · intro y hy
    rw [normalizedFiniteZeroClusterApproximationError, norm_mul]
    have hscalar :
        ‖((Real.exp (-beta * y) : ℝ) : ℂ)‖ =
          Real.exp (-beta * y) := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    rw [hscalar]
    exact (hpoint y hy).le
  · exact le_rfl

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
