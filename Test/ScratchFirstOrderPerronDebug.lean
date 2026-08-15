import PrimeNumberTheorem.PerronTruncation

private noncomputable def firstOrderBoundaryPrimitive (c u : ℝ) (w : ℝ) : ℂ :=
  Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
    ((c : ℂ) + 2 * Real.pi * w * Complex.I)

private lemma hasDerivAt_firstOrderBoundaryPrimitive
    {c u w : ℝ} (hc : 0 < c) :
    HasDerivAt (firstOrderBoundaryPrimitive c u)
      ((2 * Real.pi * Complex.I) *
        (u * firstOrderBoundaryPrimitive c u w -
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) w := by
  let H : ℂ → ℂ := fun z =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * z * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * z * Complex.I)
  have hden : (c : ℂ) + 2 * Real.pi * (w : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hH : HasDerivAt H
      ((2 * Real.pi * Complex.I) *
        (u * H w -
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) (w : ℂ) := by
    dsimp [H]
    convert (((Complex.hasDerivAt_exp
      (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).comp (w : ℂ)
        (((((hasDerivAt_id (w : ℂ)).const_mul (2 * Real.pi : ℂ)).mul_const Complex.I)
          |>.const_add (c : ℂ)).mul_const u)).div
            (((((hasDerivAt_id (w : ℂ)).const_mul (2 * Real.pi : ℂ)).mul_const Complex.I)
              |>.const_add (c : ℂ))) hden) using 1 <;>
      all_goals (trace_state; fail "STOP HERE")

set_option linter.unusedTactic false in
example : True := by trivial
