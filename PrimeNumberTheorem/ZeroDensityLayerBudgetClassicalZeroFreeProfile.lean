import PrimeNumberTheorem.PNTFiniteZeroSum

open Complex Filter Set Topology

namespace PrimeNumberTheorem

/-- The height-dependent right edge supplied by the proved classical
zero-free region after the bounded-height zeros have been absorbed into one
uniform constant. -/
noncomputable def classicalTruncationRightEdge (b T : ℝ) : ℝ :=
  1 - b / Real.log (T + 6)

/-- The classical zeta zero-free region gives an actual moving right edge for
every zero in the finite explicit-formula truncation.  The compact low-zero
patch is already included in the constant `b`. -/
theorem exists_classicalTruncationRightEdge_nontrivialZerosFinset :
    ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 4 ≤ T →
      ∀ rho ∈ nontrivialZerosFinset T,
        rho.re ≤ classicalTruncationRightEdge b T := by
  simpa [classicalTruncationRightEdge] using
    ExplicitFormulaAux.exists_nontrivialZero_re_le_one_sub_div_log_truncation

/-- If a truncation height has logarithmic scale
`alpha * sqrt (log x)`, the contour contribution has rate `alpha` while the
zero-free contribution has rate `b / alpha`.  Their common guaranteed rate is
the smaller of the two. -/
noncomputable def classicalDynamicBalancedRate (b alpha : ℝ) : ℝ :=
  min alpha (b / alpha)

theorem classicalDynamicBalancedRate_pos {b alpha : ℝ}
    (hb : 0 < b) (halpha : 0 < alpha) :
    0 < classicalDynamicBalancedRate b alpha := by
  exact lt_min halpha (div_pos hb halpha)

/-- No positive truncation parameter can make the competing contour and
zero-free rates simultaneously exceed `sqrt b`. -/
theorem classicalDynamicBalancedRate_le_sqrt {b alpha : ℝ}
    (hb : 0 < b) (halpha : 0 < alpha) :
    classicalDynamicBalancedRate b alpha ≤ Real.sqrt b := by
  by_cases hleft : alpha ≤ Real.sqrt b
  · exact (min_le_left alpha (b / alpha)).trans hleft
  · have hsqrt0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have hsquare : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
    have hquot : b / alpha ≤ Real.sqrt b := by
      apply (div_le_iff₀ halpha).2
      nlinarith
    exact (min_le_right alpha (b / alpha)).trans hquot

/-- The balanced choice `alpha = sqrt b` attains the upper bound exactly. -/
theorem classicalDynamicBalancedRate_sqrt {b : ℝ} (hb : 0 < b) :
    classicalDynamicBalancedRate b (Real.sqrt b) = Real.sqrt b := by
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsquare : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hdiv : b / Real.sqrt b = Real.sqrt b := by
    apply (div_eq_iff hsqrt.ne').2
    nlinarith
  simp [classicalDynamicBalancedRate, hdiv]

/-- Exact optimizer statement for the dynamic height exponent. -/
theorem classicalDynamicBalancedRate_isMax {b : ℝ} (hb : 0 < b) :
    IsGreatest
      (Set.range (classicalDynamicBalancedRate b))
      (Real.sqrt b) := by
  constructor
  · exact ⟨Real.sqrt b, classicalDynamicBalancedRate_sqrt hb⟩
  · rintro rate ⟨alpha, rfl⟩
    by_cases halpha : 0 < alpha
    · exact classicalDynamicBalancedRate_le_sqrt hb halpha
    · exact (min_le_left alpha (b / alpha)).trans
        ((le_of_not_gt halpha).trans (Real.sqrt_nonneg b))

/-- Both competing exponential errors are controlled by the exponential with
the balanced minimum rate. -/
theorem add_competing_exp_le_balanced_exp {b alpha u : ℝ}
    (halpha : 0 < alpha) (hu : 0 ≤ u) :
    Real.exp (-alpha * u) + Real.exp (-(b / alpha) * u) ≤
      2 * Real.exp (-(classicalDynamicBalancedRate b alpha) * u) := by
  have hleft :
      Real.exp (-alpha * u) ≤
        Real.exp (-(classicalDynamicBalancedRate b alpha) * u) := by
    apply Real.exp_le_exp.mpr
    have hrate :
        classicalDynamicBalancedRate b alpha ≤ alpha :=
      min_le_left alpha (b / alpha)
    simpa only [neg_mul] using
      neg_le_neg (mul_le_mul_of_nonneg_right hrate hu)
  have hright :
      Real.exp (-(b / alpha) * u) ≤
        Real.exp (-(classicalDynamicBalancedRate b alpha) * u) := by
    apply Real.exp_le_exp.mpr
    have hrate :
        classicalDynamicBalancedRate b alpha ≤ b / alpha :=
      min_le_right alpha (b / alpha)
    simpa only [neg_mul] using
      neg_le_neg (mul_le_mul_of_nonneg_right hrate hu)
  linarith

/-- At the optimizer, contour decay and zero-free decay coincide and the
combined error has the sharp arithmetic majorant
`2 * exp (-sqrt b * u)`. -/
theorem add_competing_exp_le_optimal_exp {b u : ℝ}
    (hb : 0 < b) (hu : 0 ≤ u) :
    Real.exp (-(Real.sqrt b) * u) +
        Real.exp (-(b / Real.sqrt b) * u) ≤
      2 * Real.exp (-(Real.sqrt b) * u) := by
  simpa [classicalDynamicBalancedRate_sqrt hb] using
    add_competing_exp_le_balanced_exp
      (b := b) (alpha := Real.sqrt b) (u := u) (Real.sqrt_pos.2 hb) hu

end PrimeNumberTheorem
