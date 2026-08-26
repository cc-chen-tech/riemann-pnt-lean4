import MathlibAux.DirichletPolynomialMeanSquare

open Complex MeasureTheory

namespace MathlibAux

/-!
# First moment of a finite exponential polynomial

This isolates the exact constant-term argument used on the right edge of
Selberg's S4 rectangle.  One distinguished zero-frequency coefficient is
removed exactly; every remaining frequency is bounded by elementary
integration of a complex exponential.
-/

/-- Removing a distinguished unit coefficient at frequency zero leaves a
sum of nonzero-frequency terms.  Its interval integral is bounded by the
sum of the reciprocal-frequency oscillatory envelopes. -/
theorem norm_intervalIntegral_exponentialPolynomial_sub_distinguished_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (i0 : ι)
    (hi0 : i0 ∈ s) (hcoeff : coeff i0 = 1) (hfreq0 : freq i0 = 0)
    (hfreq : ∀ i ∈ s.erase i0, freq i ≠ 0) {a b : ℝ} :
    ‖∫ t in a..b,
        (exponentialPolynomial s coeff freq t - 1)‖ ≤
      ∑ i ∈ s.erase i0, 2 * ‖coeff i‖ / |freq i| := by
  have hremove (t : ℝ) :
      exponentialPolynomial s coeff freq t - 1 =
        ∑ i ∈ s.erase i0,
          coeff i * Complex.exp (I * (freq i * t)) := by
    unfold exponentialPolynomial
    rw [← Finset.sum_erase_add _ _ hi0, hcoeff, hfreq0]
    simp
  rw [show (fun t : ℝ => exponentialPolynomial s coeff freq t - 1) =
      fun t : ℝ => ∑ i ∈ s.erase i0,
        coeff i * Complex.exp (I * (freq i * t)) by
      funext t
      exact hremove t]
  rw [intervalIntegral.integral_finsetSum]
  · calc
      ‖∑ i ∈ s.erase i0,
          ∫ t in a..b, coeff i * Complex.exp (I * (freq i * t))‖ ≤
          ∑ i ∈ s.erase i0,
            ‖∫ t in a..b,
              coeff i * Complex.exp (I * (freq i * t))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ s.erase i0, 2 * ‖coeff i‖ / |freq i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [intervalIntegral.integral_const_mul, norm_mul]
        calc
          ‖coeff i‖ *
              ‖∫ t in a..b, Complex.exp (I * (freq i * t))‖ ≤
              ‖coeff i‖ * (2 / |freq i|) := by
            gcongr
            exact norm_integral_cexp_linear_le (hfreq i hi)
          _ = 2 * ‖coeff i‖ / |freq i| := by ring
  · intro i hi
    apply Continuous.intervalIntegrable
    fun_prop

end MathlibAux
