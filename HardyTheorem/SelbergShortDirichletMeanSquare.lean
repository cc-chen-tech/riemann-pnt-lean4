import HardyTheorem.SelbergShortDirichletCollected
import MathlibAux.SlidingExponentialCoefficientBound

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-!
# Mean square reduction for the Selberg short Dirichlet error

After equal product frequencies have been collected and the constant term has
been removed, the short Dirichlet error is exactly a sliding integral of a
finite exponential polynomial with distinct frequencies.  Hence its second
moment is bounded by an explicit finite diagonal-plus-gap sum.
-/

/-- The short error is exactly the sliding integral of the collected
nonconstant polynomial. -/
theorem selbergMollifiedShortDirichletPolynomial_eq_slidingCollected
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (H t : ℝ) :
    selbergMollifiedShortDirichletPolynomial H N X t =
      MathlibAux.slidingExponentialPolynomialIntegral
        (Finset.Ioc 1 (N * X * X))
        (selbergShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency H t := by
  rw [selbergMollifiedShortDirichletPolynomial_eq_integral_expansion]
  unfold MathlibAux.slidingExponentialPolynomialIntegral
  apply intervalIntegral.integral_congr
  intro u _hu
  change selbergShortDirichletTriplePolynomial N X u - 1 = _
  rw [selbergShortDirichletTriplePolynomial_eq_collectedPolynomial,
    selbergShortDirichletCollectedPolynomial_sub_one_eq hN hX]

/-- The start-variable second moment of the Selberg short error is reduced to
the exact transformed coefficients and the gaps between the distinct
frequencies `-log k`. -/
theorem integral_normSq_selbergMollifiedShortDirichletPolynomial_le_gapSum
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) {A B H : ℝ} :
    (∫ t in A..B,
        Complex.normSq
          (selbergMollifiedShortDirichletPolynomial H N X t)) ≤
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
                selbergShortDirichletCollectedFrequency n| := by
  rw [show (fun t : ℝ => Complex.normSq
      (selbergMollifiedShortDirichletPolynomial H N X t)) =
      fun t : ℝ => Complex.normSq
        (MathlibAux.slidingExponentialPolynomialIntegral
          (Finset.Ioc 1 (N * X * X))
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency H t) by
    funext t
    rw [selbergMollifiedShortDirichletPolynomial_eq_slidingCollected hN hX]]
  apply MathlibAux.integral_normSq_slidingExponentialPolynomialIntegral_le
  intro m hm n hn hmn hfreq
  apply hmn
  apply selbergShortDirichletCollectedFrequency_injective_on_support
    (N := N) (X := X)
  · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hm).1.le,
      (Finset.mem_Ioc.mp hm).2⟩
  · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le,
      (Finset.mem_Ioc.mp hn).2⟩
  · exact hfreq

end HardyTheorem
