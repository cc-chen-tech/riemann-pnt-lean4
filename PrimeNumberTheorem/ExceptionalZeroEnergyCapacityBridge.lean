import PrimeNumberTheorem.ExceptionalZeroDirectedGrowth

open Complex MeasureTheory Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# A common energy-capacity object for right-higher zeta zeros

The absolute mass below uses exactly the finite zeta-zero complement occurring
in the right-higher explicit-formula energy.  Its summand is the target-
normalized Pintz kernel weight.  Thus the bridge changes neither the zero set,
the truncation height, nor the normalization.

The half-height exponent lemma records only an obstruction for the current
majorant: at `T = x^(1/2)`, the classical Carlson count exponent combined with
the squared L1 absolute mass cannot make the target-normalized capacity decay
for `1/2 < sigma < beta < 1`.  This module does not analyze a direct L2 bound,
a dyadic weighted Carlson capacity, or a two-height tail transfer.  In
particular, it proves no Carlson contradiction and excludes no off-line zero.
-/

/-- Target-normalized absolute zero mass on the exact right-higher complement.
At `x = exp y`, each summand is
`ord_rho(zeta) / |rho| * x^(Re rho - beta)`. -/
noncomputable def rightHigherTargetNormalizedAbsoluteMass
    (S : Finset ℂ) (Told sigma T beta y : ℝ) : ℝ :=
  ∑ rho ∈ nontrivialZerosFinset T \
      rightHigherExclusionSet S Told sigma T,
    ‖finiteZeroClusterCoefficientAt
        (analyticOrderNatAt riemannZeta) beta 0 rho‖ *
      Real.exp ((rho.re - beta) * y)

theorem rightHigherTargetNormalizedAbsoluteMass_nonneg
    (S : Finset ℂ) (Told sigma T beta y : ℝ) :
    0 ≤ rightHigherTargetNormalizedAbsoluteMass S Told sigma T beta y := by
  unfold rightHigherTargetNormalizedAbsoluteMass
  positivity

/-- The frozen coefficient at logarithmic center zero is exactly the
multiplicity-weighted reciprocal-ordinate kernel. -/
theorem finiteZeroClusterCoefficientAt_zero_norm_eq_kernelWeight
    (beta : ℝ) (rho : ℂ) :
    ‖finiteZeroClusterCoefficientAt
        (analyticOrderNatAt riemannZeta) beta 0 rho‖ =
      (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ := by
  simp [finiteZeroClusterCoefficientAt, div_eq_mul_inv]

private theorem norm_targetNormalizedMovingZeroTerm
    (beta y : ℝ) (rho : ℂ) :
    ‖finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta 0 rho *
        (Real.exp ((rho.re - beta) * y) : ℂ) *
        Complex.exp (I * (rho.im * y))‖ =
      ‖finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta 0 rho‖ *
        Real.exp ((rho.re - beta) * y) := by
  have hreal :
      ‖(Real.exp ((rho.re - beta) * y) : ℂ)‖ =
        Real.exp ((rho.re - beta) * y) := by
    rw [norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hphase :
      ‖Complex.exp (I * (rho.im * y))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [norm_mul, norm_mul, hreal, hphase, mul_one]

/-- Triangle inequality on the exact right-higher complement.  This is the
pointwise energy-to-capacity bridge before squaring and Gaussian averaging. -/
theorem norm_normalizedRightHigherComplement_le_absoluteMass
    (S : Finset ℂ) (Told sigma T beta y : ℝ) :
    ‖normalizedFiniteZeroClusterComplementContribution
        (rightHigherExclusionSet S Told sigma T) T beta y‖ ≤
      rightHigherTargetNormalizedAbsoluteMass
        S Told sigma T beta y := by
  classical
  let Z : Finset ℂ :=
    nontrivialZerosFinset T \
      rightHigherExclusionSet S Told sigma T
  have hrewrite :
      normalizedFiniteZeroClusterComplementContribution
          (rightHigherExclusionSet S Told sigma T) T beta y =
        MathlibAux.driftingExponentialPolynomial Z
          (finiteZeroClusterCoefficientAt
            (analyticOrderNatAt riemannZeta) beta 0)
          Complex.im (fun rho => rho.re - beta) 0 y := by
    rw [← normalizedFiniteZeroClusterContribution_eq_drifting]
    rfl
  rw [hrewrite]
  unfold MathlibAux.driftingExponentialPolynomial
  calc
    ‖∑ rho ∈ Z,
        finiteZeroClusterCoefficientAt
            (analyticOrderNatAt riemannZeta) beta 0 rho *
          (Real.exp ((rho.re - beta) * (y - 0)) : ℂ) *
          Complex.exp (I * (rho.im * y))‖ ≤
        ∑ rho ∈ Z,
          ‖finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta 0 rho *
            (Real.exp ((rho.re - beta) * (y - 0)) : ℂ) *
            Complex.exp (I * (rho.im * y))‖ :=
      norm_sum_le _ _
    _ = rightHigherTargetNormalizedAbsoluteMass
          S Told sigma T beta y := by
      unfold rightHigherTargetNormalizedAbsoluteMass Z
      apply Finset.sum_congr rfl
      intro rho hrho
      simpa using norm_targetNormalizedMovingZeroTerm beta y rho

/-- Gaussian average of the squared common absolute mass. -/
noncomputable def rightHigherGaussianAbsoluteCapacity
    (S : Finset ℂ) (Told sigma T beta a m L : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Icc 0 L,
    normalizedGaussian m t *
      rightHigherTargetNormalizedAbsoluteMass
          S Told sigma T beta (a + t) ^ 2

/-- The actual right-higher Gaussian second moment is bounded by the Gaussian
average of the squared common absolute mass. -/
theorem rightHigherGaussianSecondMoment_le_absoluteCapacity
    (S : Finset ℂ) (Told sigma T beta a L : ℝ)
    {m : ℝ} (hm : 0 < m) :
    (∫ t : ℝ in Set.Icc 0 L,
        normalizedGaussian m t *
          ‖normalizedFiniteZeroClusterComplementContribution
              (rightHigherExclusionSet S Told sigma T)
              T beta (a + t)‖ ^ 2) ≤
      rightHigherGaussianAbsoluteCapacity
        S Told sigma T beta a m L := by
  let complement : ℝ → ℂ := fun t =>
    normalizedFiniteZeroClusterComplementContribution
      (rightHigherExclusionSet S Told sigma T) T beta (a + t)
  let mass : ℝ → ℝ := fun t =>
    rightHigherTargetNormalizedAbsoluteMass
      S Told sigma T beta (a + t)
  let weight : ℝ → ℝ := normalizedGaussian m
  have hcomplement : Continuous complement := by
    let Z : Finset ℂ :=
      nontrivialZerosFinset T \
        rightHigherExclusionSet S Told sigma T
    have heq :
        complement = fun t =>
          MathlibAux.driftingExponentialPolynomial Z
            (finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta 0)
            Complex.im (fun rho => rho.re - beta) 0 (a + t) := by
      funext t
      dsimp [complement]
      rw [← normalizedFiniteZeroClusterContribution_eq_drifting]
      rfl
    rw [heq]
    unfold MathlibAux.driftingExponentialPolynomial
    fun_prop
  have hmass : Continuous mass := by
    dsimp [mass, rightHigherTargetNormalizedAbsoluteMass]
    fun_prop
  have hweight : Continuous weight := by
    dsimp [weight]
    exact continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_normalizedGaussian hm t).continuousAt
  have hlowerInt :
      IntegrableOn (fun t => weight t * ‖complement t‖ ^ 2)
        (Set.Icc 0 L) :=
    (hweight.mul (hcomplement.norm.pow 2)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hupperInt :
      IntegrableOn (fun t => weight t * mass t ^ 2)
        (Set.Icc 0 L) :=
    (hweight.mul (hmass.pow 2)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) L,
      weight t * ‖complement t‖ ^ 2 ≤ weight t * mass t ^ 2 := by
    intro t ht
    have hnorm : ‖complement t‖ ≤ mass t := by
      exact norm_normalizedRightHigherComplement_le_absoluteMass
        S Told sigma T beta (a + t)
    have hmassNonneg : 0 ≤ mass t :=
      rightHigherTargetNormalizedAbsoluteMass_nonneg
        S Told sigma T beta (a + t)
    have hsq : ‖complement t‖ ^ 2 ≤ mass t ^ 2 := by
      nlinarith [norm_nonneg (complement t)]
    exact mul_le_mul_of_nonneg_left hsq
      (normalizedGaussian_pos hm t).le
  exact setIntegral_mono_on hlowerInt hupperInt measurableSet_Icc hpoint

/-- With height `H(x) = x^(1/2)`, the classical Carlson count exponent plus
target normalization is strictly positive throughout the zeta strip.  Hence
the current classical-count plus squared-L1-mass polynomial majorant cannot
decay. -/
theorem halfHeightCarlsonTargetExponent_pos
    {sigma beta : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hbeta : beta < 1) :
    0 < (1 / 2 : ℝ) * (4 * sigma * (1 - sigma)) + sigma - beta := by
  have hproduct : 0 < (1 - sigma) * (2 * sigma - 1) :=
    mul_pos (sub_pos.mpr hsigmaOne) (sub_pos.mpr (by linarith))
  have hid :
      (1 / 2 : ℝ) * (4 * sigma * (1 - sigma)) + sigma - 1 =
        (1 - sigma) * (2 * sigma - 1) := by
    ring
  linarith

/-- Thin integration interface: if `M(x) >= x^theta` and one zero is reused at
most `x^overlap`, the polynomial window count beats a Carlson capacity of
height exponent `alpha` exactly when the net window exponent exceeds the
composed Carlson exponent. -/
theorem polynomialWindowCapacity_threshold_iff
    (theta overlap alpha sigma : ℝ) :
    theta - overlap > alpha * (4 * sigma * (1 - sigma)) ↔
      theta > overlap + alpha * (4 * sigma * (1 - sigma)) := by
  constructor <;> intro h <;> linarith

/-- The natural PR #119 height `alpha = 1/2` requires
`theta > overlap + 2 sigma (1-sigma)`. -/
theorem halfHeightWindowCapacity_threshold_iff
    (theta overlap sigma : ℝ) :
    theta - overlap > (1 / 2 : ℝ) * (4 * sigma * (1 - sigma)) ↔
      theta > overlap + 2 * sigma * (1 - sigma) := by
  constructor <;> intro h <;> nlinarith

end


end VKEdgePiOverTwo
end PrimeNumberTheorem
