import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalBalancedFiniteZeroSum

open Complex Filter Set Topology

namespace PrimeNumberTheorem

/-- The optimal classical square-root-logarithmic height rate after imposing
the explicit-formula admissibility constraint `alpha ≤ 1`. -/
noncomputable def classicalAdmissibleBalancedRate (b : ℝ) : ℝ :=
  min 1 (Real.sqrt b)

theorem classicalAdmissibleBalancedRate_pos {b : ℝ} (hb : 0 < b) :
    0 < classicalAdmissibleBalancedRate b := by
  exact lt_min zero_lt_one (Real.sqrt_pos.2 hb)

theorem classicalAdmissibleBalancedRate_le_one (b : ℝ) :
    classicalAdmissibleBalancedRate b ≤ 1 :=
  min_le_left _ _

theorem classicalAdmissibleBalancedRate_le_sqrt (b : ℝ) :
    classicalAdmissibleBalancedRate b ≤ Real.sqrt b :=
  min_le_right _ _

/-- At the admissible optimizer, the zero-free decay rate is at least the
contour decay rate. -/
theorem classicalAdmissibleBalancedRate_le_zeroFreeRate
    {b : ℝ} (hb : 0 < b) :
    classicalAdmissibleBalancedRate b ≤
      b / classicalAdmissibleBalancedRate b := by
  have hrate :=
    classicalAdmissibleBalancedRate_le_sqrt b
  have hrate0 :
      0 ≤ classicalAdmissibleBalancedRate b :=
    (classicalAdmissibleBalancedRate_pos hb).le
  have hsquare : (Real.sqrt b) ^ 2 = b :=
    Real.sq_sqrt hb.le
  apply (le_div_iff₀ (classicalAdmissibleBalancedRate_pos hb)).2
  nlinarith

/-- The competing minimum rate at the admissible optimizer is exactly the
optimizer itself. -/
theorem classicalDynamicBalancedRate_admissible
    {b : ℝ} (hb : 0 < b) :
    classicalDynamicBalancedRate b
        (classicalAdmissibleBalancedRate b) =
      classicalAdmissibleBalancedRate b := by
  rw [classicalDynamicBalancedRate, min_eq_left]
  exact classicalAdmissibleBalancedRate_le_zeroFreeRate hb

/-- Every positive admissible height rate has common contour/zero-free rate
at most `min 1 (sqrt b)`. -/
theorem classicalDynamicBalancedRate_le_admissible
    {b alpha : ℝ} (hb : 0 < b)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1) :
    classicalDynamicBalancedRate b alpha ≤
      classicalAdmissibleBalancedRate b := by
  apply le_min
  · exact (min_le_left alpha (b / alpha)).trans halphaOne
  · exact classicalDynamicBalancedRate_le_sqrt hb halpha

/-- Exact constrained optimizer statement: `min 1 (sqrt b)` is admissible,
attains its own common rate, and dominates every other admissible choice. -/
theorem classicalAdmissibleBalancedRate_isOptimal {b : ℝ} (hb : 0 < b) :
    0 < classicalAdmissibleBalancedRate b ∧
      classicalAdmissibleBalancedRate b ≤ 1 ∧
      classicalDynamicBalancedRate b
          (classicalAdmissibleBalancedRate b) =
        classicalAdmissibleBalancedRate b ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
        classicalDynamicBalancedRate b alpha ≤
          classicalAdmissibleBalancedRate b := by
  exact ⟨
    classicalAdmissibleBalancedRate_pos hb,
    classicalAdmissibleBalancedRate_le_one b,
    classicalDynamicBalancedRate_admissible hb,
    fun alpha halpha halphaOne =>
      classicalDynamicBalancedRate_le_admissible
        hb halpha halphaOne
  ⟩

end PrimeNumberTheorem
