import HardyTheorem.SelbergSmallAbsBadSet
import HardyTheorem.SelbergShortDirichletMeanSquare

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Small Selberg windows reduced to one finite frequency-gap sum

This file composes the analytic lower bound for the mollified absolute mass,
the exact mean-square reduction for the short Dirichlet error, and the Markov
estimate for bad starts.  The only remaining input in the conclusion is an
explicit finite arithmetic sum.
-/

/-- The diagonal-plus-frequency-gap expression controlling the second moment
of the collected Selberg short polynomial. -/
noncomputable def selbergShortDirichletGapSum
    (N X : ℕ) (A B H : ℝ) : ℝ :=
  ∑ m ∈ Finset.Ioc 1 (N * X * X),
    ∑ n ∈ Finset.Ioc 1 (N * X * X),
      if m = n then
        (B - A) * Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency n)
      else
        2 * ‖MathlibAux.slidingExponentialCoefficient H
              (selbergShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency m‖ *
            ‖MathlibAux.slidingExponentialCoefficient H
              (selbergShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency n‖ /
          |selbergShortDirichletCollectedFrequency m -
            selbergShortDirichletCollectedFrequency n|

/-- The exact finite gap sum bounds the interval second moment. -/
theorem integral_normSq_selbergMollifiedShortDirichletPolynomial_le_gapSum'
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) {A B H : ℝ} :
    (∫ t in A..B,
        Complex.normSq
          (selbergMollifiedShortDirichletPolynomial H N X t)) ≤
      selbergShortDirichletGapSum N X A B H := by
  exact integral_normSq_selbergMollifiedShortDirichletPolynomial_le_gapSum
    hN hX

/-- Once a pointwise lower bound for the mollified absolute mass is available,
the starts with small absolute mass are bounded directly by the explicit
finite frequency-gap sum. -/
theorem volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_gapSum
    {X N : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    {A B H eta R : ℝ} (hAB : A ≤ B)
    (hthreshold : 0 < H - eta - R)
    (hlower : ∀ t ∈ Icc A B,
      H - ‖selbergMollifiedShortDirichletPolynomial H N X t‖ - R ≤
        selbergMoebiusAbsShortIntegral X H t) :
    volume.real
        (selbergSmallAbsoluteMassStarts X H eta ∩ Icc A B) ≤
      selbergShortDirichletGapSum N X A B H /
        (H - eta - R) ^ 2 := by
  let Q : ℝ → ℂ := fun t =>
    selbergMollifiedShortDirichletPolynomial H N X t
  have hQeq : Q = fun t =>
      MathlibAux.exponentialPolynomial
        (Finset.Ioc 1 (N * X * X))
        (MathlibAux.slidingExponentialCoefficient H
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency)
        selbergShortDirichletCollectedFrequency t := by
    funext t
    dsimp only [Q]
    rw [selbergMollifiedShortDirichletPolynomial_eq_slidingCollected hN hX,
      MathlibAux.slidingExponentialPolynomialIntegral_eq]
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
        selbergShortDirichletGapSum N X A B H := by
    change (∫ t in Icc A B, Complex.normSq (Q t)) ≤ _
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hAB]
    exact integral_normSq_selbergMollifiedShortDirichletPolynomial_le_gapSum'
      hN hX
  exact volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_of_shortDirichletL2
    hthreshold hlower (by simpa only [Q] using hQint)
      (by simpa only [Q] using hQbound)

/-- The first zeta approximation supplies the pointwise lower bound in the
preceding theorem.  Consequently the small-absolute-mass exceptional set is
controlled unconditionally by the explicit finite gap sum, provided the
displayed threshold is positive. -/
theorem exists_volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_gapSum :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H eta : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T →
        0 < H - eta - 4 * C * H * X / Real.sqrt T →
        volume.real
            (selbergSmallAbsoluteMassStarts X H eta ∩
              Icc T (2 * T - H)) ≤
          selbergShortDirichletGapSum
              (firstZetaApproximationCutoff T) X T (2 * T - H) H /
            (H - eta - 4 * C * H * X / Real.sqrt T) ^ 2 := by
  obtain ⟨C, T0, hC, hT0, hlower⟩ :=
    exists_selbergMoebiusAbsShortIntegral_ge_sub_shortDirichlet_coarse
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H eta hT hH hHT hthreshold
  have hN : 1 ≤ firstZetaApproximationCutoff T := by
    apply Nat.le_floor
    have hT1 : (1 : ℝ) ≤ T := hT0.trans hT
    simpa only [Nat.cast_one, firstZetaApproximationCutoff] using
      (show (1 : ℝ) ≤ 4 * T by linarith)
  apply volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_gapSum
    hN (by omega) (by linarith) hthreshold
  intro t ht
  exact hlower X hX T H t hT hH ht

end HardyTheorem
