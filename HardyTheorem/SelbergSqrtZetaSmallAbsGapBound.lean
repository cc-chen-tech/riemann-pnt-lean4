import HardyTheorem.SelbergSmallAbsBadSet
import HardyTheorem.SelbergSqrtZetaShortExpansion

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Square-root-zeta small windows reduced to a finite gap sum

This is the coefficient-specific mean-square side of Selberg's
small-absolute-mass estimate.  The absolute-mass function remains a parameter,
so the result can be combined with the analytic lower bound independently.
-/

/-- The diagonal-plus-frequency-gap expression controlling the square-root-
zeta short polynomial. -/
noncomputable def selbergSqrtZetaShortDirichletGapSum
    (N X : ℕ) (A B H : ℝ) : ℝ :=
  ∑ m ∈ Finset.Ioc 1 (N * X * X),
    ∑ n ∈ Finset.Ioc 1 (N * X * X),
      if m = n then
        (B - A) * Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency n)
      else
        2 * ‖MathlibAux.slidingExponentialCoefficient H
              (selbergSqrtZetaShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency m‖ *
            ‖MathlibAux.slidingExponentialCoefficient H
              (selbergSqrtZetaShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency n‖ /
          |selbergShortDirichletCollectedFrequency m -
            selbergShortDirichletCollectedFrequency n|

/-- The exact finite gap sum bounds the start-variable second moment of the
square-root-zeta short polynomial. -/
theorem integral_normSq_selbergSqrtZetaMollifiedShortDirichletPolynomial_le_gapSum'
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) {A B H : ℝ} :
    (∫ t in A..B,
        Complex.normSq
          (selbergSqrtZetaMollifiedShortDirichletPolynomial
            H N X t)) ≤
      selbergSqrtZetaShortDirichletGapSum N X A B H := by
  exact
    integral_normSq_selbergSqrtZetaMollifiedShortDirichletPolynomial_le_gapSum
      hN hX

/-- A pointwise lower bound for an arbitrary absolute-mass function converts
the square-root-zeta gap sum into a bad-start measure bound. -/
theorem volume_smallMassStarts_inter_Icc_le_sqrtZetaGapSum
    {absMass : ℝ → ℝ} {X N : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    {A B H eta R : ℝ} (hAB : A ≤ B)
    (hthreshold : 0 < H - eta - R)
    (hlower : ∀ t ∈ Icc A B,
      H -
          ‖selbergSqrtZetaMollifiedShortDirichletPolynomial
            H N X t‖ -
          R ≤ absMass t) :
    volume.real ({t | absMass t ≤ eta} ∩ Icc A B) ≤
      selbergSqrtZetaShortDirichletGapSum N X A B H /
        (H - eta - R) ^ 2 := by
  let Q : ℝ → ℂ := fun t =>
    selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t
  have hQeq : Q = fun t =>
      MathlibAux.exponentialPolynomial
        (Finset.Ioc 1 (N * X * X))
        (MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency)
        selbergShortDirichletCollectedFrequency t := by
    funext t
    dsimp only [Q]
    rw [selbergSqrtZetaMollifiedShortDirichletPolynomial_eq_slidingCollected
      hN hX, MathlibAux.slidingExponentialPolynomialIntegral_eq]
  have hQcont : Continuous Q := by
    rw [hQeq]
    unfold MathlibAux.exponentialPolynomial
    fun_prop
  have hQint : Integrable (fun t => Complex.normSq (Q t))
      (volume.restrict (Icc A B)) := by
    change IntegrableOn (fun t => Complex.normSq (Q t)) (Icc A B) volume
    exact (Complex.continuous_normSq.comp hQcont).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hQbound :
      (∫ t, Complex.normSq (Q t) ∂volume.restrict (Icc A B)) ≤
        selbergSqrtZetaShortDirichletGapSum N X A B H := by
    change (∫ t in Icc A B, Complex.normSq (Q t)) ≤ _
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hAB]
    exact
      integral_normSq_selbergSqrtZetaMollifiedShortDirichletPolynomial_le_gapSum'
        hN hX
  exact volume_smallMassStarts_inter_Icc_le_of_L2
    hthreshold hlower (by simpa only [Q] using hQint)
      (by simpa only [Q] using hQbound)

end HardyTheorem
