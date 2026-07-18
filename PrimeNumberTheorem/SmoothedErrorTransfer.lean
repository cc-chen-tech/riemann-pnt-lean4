import PrimeNumberTheorem.RieszDifference

/-!
# Transferring smoothed approximation errors to Chebyshev psi

This module isolates the algebraic step needed after a finite-height
second-order explicit formula supplies approximations to the first Riesz mean.
In particular, callers can use the residue sum minus contour remainder from
`SecondOrderExplicitFormula` as `approx`. The approximation and its error may
both depend on the height parameter `T`.
-/

open Complex

namespace PrimeNumberTheorem

/-- If a complex approximation controls the first Riesz mean at `x` and
`x + h`, its real-part finite difference gives explicit endpoint bounds for
`chebyshevPsi`. The theorem is uniform in the smoothing width `h` and the
external height parameter `T`. -/
theorem chebyshevPsi_bounds_of_smoothedApproximation
    (approx : ℝ → ℝ → ℂ) (error : ℝ → ℝ → ℝ)
    {x h T : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hxError : ‖approx x T - (smoothedChebyshevPsi x : ℂ)‖ ≤ error x T)
    (hyError : ‖approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
      error (x + h) T) :
    chebyshevPsi x ≤
        ((approx (x + h) T).re - (approx x T).re +
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ∧
      ((approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ≤
        chebyshevPsi (x + h) := by
  have hxy : x < x + h := by linarith
  have hratio : 1 < (x + h) / x := (lt_div_iff₀ hx).2 (by linarith)
  have hlog : 0 < Real.log ((x + h) / x) := Real.log_pos hratio
  have hxReal : |(approx x T).re - smoothedChebyshevPsi x| ≤ error x T := by
    calc
      |(approx x T).re - smoothedChebyshevPsi x| =
          |(approx x T - (smoothedChebyshevPsi x : ℂ)).re| := by simp
      _ ≤ ‖approx x T - (smoothedChebyshevPsi x : ℂ)‖ := abs_re_le_norm _
      _ ≤ error x T := hxError
  have hyReal : |(approx (x + h) T).re - smoothedChebyshevPsi (x + h)| ≤
      error (x + h) T := by
    calc
      |(approx (x + h) T).re - smoothedChebyshevPsi (x + h)| =
          |(approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)).re| := by simp
      _ ≤ ‖approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)‖ :=
        abs_re_le_norm _
      _ ≤ error (x + h) T := hyError
  have hUpper : smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x ≤
      (approx (x + h) T).re - (approx x T).re +
        (error x T + error (x + h) T) := by
    rcases abs_le.mp hxReal with ⟨hxLower, hxUpper⟩
    rcases abs_le.mp hyReal with ⟨hyLower, hyUpper⟩
    linarith
  have hLower :
      (approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T) ≤
        smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x := by
    rcases abs_le.mp hxReal with ⟨hxLower, hxUpper⟩
    rcases abs_le.mp hyReal with ⟨hyLower, hyUpper⟩
    linarith
  have hRiesz := chebyshevPsi_le_rieszDifference_div_log_le hx hxy
  constructor
  · calc
      chebyshevPsi x ≤
          (smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x) /
            Real.log ((x + h) / x) := hRiesz.1
      _ ≤ ((approx (x + h) T).re - (approx x T).re +
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) := (div_le_div_iff_of_pos_right hlog).2 hUpper
  · calc
      ((approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ≤
          (smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x) /
            Real.log ((x + h) / x) := (div_le_div_iff_of_pos_right hlog).2 hLower
      _ ≤ chebyshevPsi (x + h) := hRiesz.2

end PrimeNumberTheorem
