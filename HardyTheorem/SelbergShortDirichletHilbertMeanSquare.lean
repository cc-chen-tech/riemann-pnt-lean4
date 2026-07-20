import HardyTheorem.SelbergShortDirichletMeanSquare
import MathlibAux.NegativeLogDirichletPolynomialMeanSquare

open Complex MeasureTheory Set

namespace HardyTheorem

/-!
# Hilbert mean-square reduction for the Selberg short Dirichlet error

The collected short Dirichlet error is a negative-log exponential polynomial
whose coefficients are the exact sliding-window transforms of the collected
Dirichlet coefficients.  The logarithmic Hilbert inequality therefore bounds
its mean square by the transformed coefficient energy, with a loss linear in
the largest product index `N * X * X`.

This is only a finite-polynomial mean-square reduction.  No sharp estimate for
the transformed coefficient energy is asserted here.
-/

/-- The mean square of the Selberg short Dirichlet error is controlled by the
square energy of its exact sliding-window coefficients.  The factor consists
of the integration interval length and the standard logarithmic Hilbert loss
linear in the largest collected product index. -/
theorem integral_normSq_selbergMollifiedShortDirichletPolynomial_le_energy
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) {A B H : ℝ} :
    (∫ t in A..B,
        Complex.normSq
          (selbergMollifiedShortDirichletPolynomial H N X t)) ≤
      ((B - A) + 4 * (5 * Real.pi + 4) * ((N * X * X : ℕ) : ℝ)) *
        ∑ k ∈ Finset.Ioc 1 (N * X * X),
          Complex.normSq
            (MathlibAux.slidingExponentialCoefficient H
              (selbergShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency k) := by
  let Y : ℕ := N * X * X
  let s : Finset ℕ := Finset.Ioc 1 Y
  let transformedCoeff : ℕ → ℂ :=
    MathlibAux.slidingExponentialCoefficient H
      (selbergShortDirichletCollectedCoeff N X)
      selbergShortDirichletCollectedFrequency
  have hY : 0 < Y := by
    dsimp only [Y]
    exact Nat.mul_pos (Nat.mul_pos hN hX) hX
  have hpositive : ∀ k ∈ s, k ≠ 0 := by
    intro k hk
    have hkOne : 1 < k := (Finset.mem_Ioc.mp hk).1
    omega
  have hupper : ∀ k ∈ s, k ≤ Y := by
    intro k hk
    exact (Finset.mem_Ioc.mp hk).2
  have hraw :=
    MathlibAux.integral_normSq_negLogExponentialPolynomial_le_of_upper
      hY s transformedCoeff hpositive hupper (a := A) (b := B)
  change
    (∫ t in A..B,
        Complex.normSq
          (selbergMollifiedShortDirichletPolynomial H N X t)) ≤ _
  rw [show (fun t : ℝ => Complex.normSq
      (selbergMollifiedShortDirichletPolynomial H N X t)) =
      fun t : ℝ => Complex.normSq
        (MathlibAux.exponentialPolynomial s transformedCoeff
          (fun k => -Real.log k) t) by
    funext t
    congr 1
    rw [selbergMollifiedShortDirichletPolynomial_eq_slidingCollected hN hX,
      MathlibAux.slidingExponentialPolynomialIntegral_eq]
    rfl]
  simpa only [Y, s, transformedCoeff] using hraw

end HardyTheorem
