import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonTwoHeightSplit

/-!
# Actual zeta-zero realization of the Carlson two-height split

This module constructs the low- and high-ordinate pieces directly from the
finite set counted by Carlson.  It therefore avoids the impossible
requirement that a growing ordinate floor cover every fixed positive zero.

The low piece is counted only to the intermediate height.  Its denominator is
bounded from the positive real-part threshold.  The high piece is counted to
the outer height and gains the intermediate ordinate in the denominator.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Actual positive zeta zeros in one real strip, up to height `T`. -/
noncomputable def actualPositiveCarlsonStrip
    (sigma tau T : ℝ) : Finset ℂ :=
  (ZeroDensity.zeroDensityZerosFinset sigma T).filter
    fun rho => rho.re ≤ tau

/-- The low-ordinate part of an actual Carlson strip. -/
noncomputable def actualPositiveCarlsonLowStrip
    (sigma tau U : ℝ) : Finset ℂ :=
  actualPositiveCarlsonStrip sigma tau U

/-- The high-ordinate part between `U` and `T`. -/
noncomputable def actualPositiveCarlsonHighRectangle
    (sigma tau U T : ℝ) : Finset ℂ :=
  (actualPositiveCarlsonStrip sigma tau T).filter
    fun rho => U < rho.im

theorem mem_actualPositiveCarlsonStrip
    {rho : ℂ} {sigma tau T : ℝ} :
    rho ∈ actualPositiveCarlsonStrip sigma tau T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ T ∧
        sigma < rho.re ∧ rho.re ≤ tau := by
  simp only [actualPositiveCarlsonStrip, Finset.mem_filter,
    ZeroDensity.mem_zeroDensityZerosFinset]
  tauto

theorem mem_actualPositiveCarlsonLowStrip
    {rho : ℂ} {sigma tau U : ℝ} :
    rho ∈ actualPositiveCarlsonLowStrip sigma tau U ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ U ∧
        sigma < rho.re ∧ rho.re ≤ tau := by
  exact mem_actualPositiveCarlsonStrip

theorem mem_actualPositiveCarlsonHighRectangle
    {rho : ℂ} {sigma tau U T : ℝ} :
    rho ∈ actualPositiveCarlsonHighRectangle sigma tau U T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ T ∧
        sigma < rho.re ∧ rho.re ≤ tau ∧ U < rho.im := by
  simp only [actualPositiveCarlsonHighRectangle, Finset.mem_filter,
    mem_actualPositiveCarlsonStrip]
  tauto

/-- The actual strip is the disjoint union of its low and high ordinate
pieces. -/
theorem actualPositiveCarlsonStrip_eq_low_union_high
    {sigma tau U T : ℝ} (hUT : U ≤ T) :
    actualPositiveCarlsonStrip sigma tau T =
      actualPositiveCarlsonLowStrip sigma tau U ∪
        actualPositiveCarlsonHighRectangle sigma tau U T := by
  ext rho
  simp only [mem_actualPositiveCarlsonStrip,
    mem_actualPositiveCarlsonLowStrip,
    mem_actualPositiveCarlsonHighRectangle, Finset.mem_union]
  constructor
  · rintro ⟨hzero, him, himT, hreLower, hreUpper⟩
    by_cases himU : rho.im ≤ U
    · exact Or.inl ⟨hzero, him, himU, hreLower, hreUpper⟩
    · exact Or.inr
        ⟨hzero, him, himT, hreLower, hreUpper, lt_of_not_ge himU⟩
  · rintro (hlow | hhigh)
    · exact ⟨hlow.1, hlow.2.1, hlow.2.2.1.trans hUT,
        hlow.2.2.2.1, hlow.2.2.2.2⟩
    · exact ⟨hhigh.1, hhigh.2.1, hhigh.2.2.1,
        hhigh.2.2.2.1, hhigh.2.2.2.2.1⟩

theorem actualPositiveCarlsonLowStrip_disjoint_high
    (sigma tau U T : ℝ) :
    Disjoint
      (actualPositiveCarlsonLowStrip sigma tau U)
      (actualPositiveCarlsonHighRectangle sigma tau U T) := by
  rw [Finset.disjoint_left]
  intro rho hlow hhigh
  have hlow' : rho.im ≤ U :=
    (mem_actualPositiveCarlsonLowStrip.mp hlow).2.2.1
  have hhigh' : U < rho.im :=
    (mem_actualPositiveCarlsonHighRectangle.mp hhigh).2.2.2.2.2
  exact (not_lt_of_ge hlow') hhigh'

theorem analyticMultiplicityMass_le_zeroDensityCount_of_subset
    {s : Finset ℂ} {sigma T : ℝ}
    (hsubset : s ⊆ ZeroDensity.zeroDensityZerosFinset sigma T) :
    analyticMultiplicityMass s ≤
      (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
  unfold analyticMultiplicityMass
  calc
    (∑ rho ∈ s,
        (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
        ∑ rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T,
          (analyticOrderNatAt riemannZeta rho : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun rho _ _ =>
          (Nat.cast_nonneg (analyticOrderNatAt riemannZeta rho) :
            (0 : ℝ) ≤
              (analyticOrderNatAt riemannZeta rho : ℝ)))
    _ = (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
      simp [ZeroDensity.zeroDensityCount]

theorem actualPositiveCarlsonLowStrip_multiplicityMass_le
    (sigma tau U : ℝ) :
    analyticMultiplicityMass
        (actualPositiveCarlsonLowStrip sigma tau U) ≤
      (ZeroDensity.zeroDensityCount sigma U : ℝ) := by
  apply analyticMultiplicityMass_le_zeroDensityCount_of_subset
  exact Finset.filter_subset _ _

theorem actualPositiveCarlsonHighRectangle_multiplicityMass_le
    (sigma tau U T : ℝ) :
    analyticMultiplicityMass
        (actualPositiveCarlsonHighRectangle sigma tau U T) ≤
      (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
  apply analyticMultiplicityMass_le_zeroDensityCount_of_subset
  exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

/-- On the low piece, the positive real threshold itself bounds the kernel
denominator. -/
theorem norm_pntRelativeSimpleZeroKernel_le_realThreshold
    {x sigma tau : ℝ} (hx : 1 ≤ x) (hsigma : 0 < sigma)
    {rho : ℂ} (hreLower : sigma < rho.re) (hreUpper : rho.re ≤ tau) :
    ‖pntRelativeSimpleZeroKernel x rho‖ ≤
      x ^ (tau - 1) / sigma := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hreNorm : rho.re ≤ ‖rho‖ := by
    exact (le_abs_self rho.re).trans (Complex.abs_re_le_norm rho)
  have hsigmaNorm : sigma ≤ ‖rho‖ :=
    (le_of_lt hreLower).trans hreNorm
  have hnorm : 0 < ‖rho‖ := hsigma.trans_le hsigmaNorm
  have hrpow :
      x ^ (rho.re - 1) ≤ x ^ (tau - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx
      (sub_le_sub_right hreUpper 1)
  have hpow0 : 0 ≤ x ^ (tau - 1) :=
    Real.rpow_nonneg hx0.le _
  rw [norm_pntRelativeSimpleZeroKernel_eq hx0 rho]
  calc
    x ^ (rho.re - 1) / ‖rho‖ ≤
        x ^ (tau - 1) / ‖rho‖ :=
      div_le_div_of_nonneg_right hrpow (norm_nonneg rho)
    _ ≤ x ^ (tau - 1) / sigma := by
      exact (div_le_div_iff₀ hnorm hsigma).2
        (mul_le_mul_of_nonneg_left hsigmaNorm hpow0)

/-- Low-ordinate actual zeta kernels are controlled by the Carlson count at
the intermediate height. -/
theorem sum_norm_actualPositiveCarlsonLowStrip_le
    {x sigma tau U : ℝ} (hx : 1 ≤ x) (hsigma : 0 < sigma) :
    (∑ rho ∈ actualPositiveCarlsonLowStrip sigma tau U,
        ‖pntRelativeZeroContribution x rho‖) ≤
      (x ^ (tau - 1) / sigma) *
        (ZeroDensity.zeroDensityCount sigma U : ℝ) := by
  apply sum_norm_pntRelativeZeroContribution_le_kernel_mul_of_mass_le
  · exact div_nonneg (Real.rpow_nonneg (by positivity) _) hsigma.le
  · intro rho hrho
    have hmem := mem_actualPositiveCarlsonLowStrip.mp hrho
    exact norm_pntRelativeSimpleZeroKernel_le_realThreshold
      hx hsigma hmem.2.2.2.1 hmem.2.2.2.2
  · exact actualPositiveCarlsonLowStrip_multiplicityMass_le sigma tau U

/-- High-ordinate actual zeta kernels gain the intermediate ordinate in their
denominator. -/
theorem sum_norm_actualPositiveCarlsonHighRectangle_le
    {x sigma tau U T : ℝ} (hx : 1 ≤ x) (hU : 0 < U) :
    (∑ rho ∈ actualPositiveCarlsonHighRectangle sigma tau U T,
        ‖pntRelativeZeroContribution x rho‖) ≤
      (x ^ (tau - 1) / U) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
  apply sum_norm_pntRelativeZeroContribution_le_kernel_mul_of_mass_le
  · exact div_nonneg (Real.rpow_nonneg (by positivity) _) hU.le
  · intro rho hrho
    have hmem := mem_actualPositiveCarlsonHighRectangle.mp hrho
    exact norm_pntRelativeSimpleZeroKernel_le_rectangle
      hx hU (le_of_lt hmem.2.2.2.2.2) hmem.2.2.2.2.1
  · exact
      actualPositiveCarlsonHighRectangle_multiplicityMass_le
        sigma tau U T

/-- Low-height count budget, with the denominator supplied by the real
threshold. -/
noncomputable def actualCarlsonTwoHeightLowBudget
    (sigma tau gamma x : ℝ) : ℝ :=
  (x ^ (tau - 1) / sigma) *
    (ZeroDensity.zeroDensityCount sigma
      (carlsonPolynomialHeight gamma x) : ℝ)

/-- High-ordinate rectangular budget. -/
noncomputable def actualCarlsonTwoHeightHighBudget
    (sigma tau alpha gamma x : ℝ) : ℝ :=
  polynomialOrdinateRectangleKernel tau gamma x *
    (ZeroDensity.zeroDensityCount sigma
      (carlsonPolynomialHeight alpha x) : ℝ)

theorem sum_norm_actualPositiveCarlsonStrip_le_twoHeightBudget
    {x sigma tau alpha gamma : ℝ}
    (hx : 1 ≤ x) (hsigma : 0 < sigma) (hgammaAlpha : gamma ≤ alpha) :
    (∑ rho ∈ actualPositiveCarlsonStrip sigma tau
        (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖) ≤
      actualCarlsonTwoHeightLowBudget sigma tau gamma x +
        actualCarlsonTwoHeightHighBudget sigma tau alpha gamma x := by
  have hUT :
      carlsonPolynomialHeight gamma x ≤
        carlsonPolynomialHeight alpha x := by
    exact Real.rpow_le_rpow_of_exponent_le hx hgammaAlpha
  have hU : 0 < carlsonPolynomialHeight gamma x := by
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
  rw [actualPositiveCarlsonStrip_eq_low_union_high hUT,
    Finset.sum_union
      (actualPositiveCarlsonLowStrip_disjoint_high sigma tau
        (carlsonPolynomialHeight gamma x)
        (carlsonPolynomialHeight alpha x))]
  exact add_le_add
    (sum_norm_actualPositiveCarlsonLowStrip_le hx hsigma)
    (by
      simpa [actualCarlsonTwoHeightHighBudget,
        polynomialOrdinateRectangleKernel] using
        (sum_norm_actualPositiveCarlsonHighRectangle_le
          (sigma := sigma) (tau := tau)
          (U := carlsonPolynomialHeight gamma x)
          (T := carlsonPolynomialHeight alpha x) hx hU))

theorem tendsto_actualCarlsonTwoHeightLowBudget
    {sigma tau gamma epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hgamma : 0 < gamma) (hepsilon : 0 < epsilon)
    (hmargin :
      carlsonTwoHeightLowExponent sigma tau gamma + epsilon < 0) :
    Tendsto
      (actualCarlsonTwoHeightLowBudget sigma tau gamma)
      atTop (nhds 0) := by
  have hbase :=
    tendsto_dynamicCarlsonCount_mul_polynomialOrdinateRectangleKernel
      (sigma := sigma) (tau := tau) (alpha := gamma) (gamma := 0)
      hsigma hsigmaOne hgamma hepsilon (by
        simpa [carlsonTwoHeightLowExponent] using hmargin)
  have hscaled :
      Tendsto
        (fun x =>
          (1 / sigma) *
            ((ZeroDensity.zeroDensityCount sigma
              (carlsonPolynomialHeight gamma x) : ℝ) *
                polynomialOrdinateRectangleKernel tau 0 x))
        atTop (nhds 0) := by
    simpa using hbase.const_mul (1 / sigma)
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [actualCarlsonTwoHeightLowBudget,
    polynomialOrdinateRectangleKernel, Real.rpow_zero, div_one]
  ring

theorem tendsto_actualCarlsonTwoHeightHighBudget
    {sigma tau alpha gamma epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin :
      carlsonTwoHeightHighExponent sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (actualCarlsonTwoHeightHighBudget sigma tau alpha gamma)
      atTop (nhds 0) := by
  simpa [actualCarlsonTwoHeightHighBudget, mul_comm,
    carlsonTwoHeightHighExponent] using
    (tendsto_dynamicCarlsonCount_mul_polynomialOrdinateRectangleKernel
      (sigma := sigma) (tau := tau) (alpha := alpha) (gamma := gamma)
      hsigma hsigmaOne halpha hepsilon (by
        simpa [carlsonTwoHeightHighExponent] using hmargin))

/-- The actual multiplicity-weighted zeta kernels in the whole real strip
decay under the two-height exponent conditions. -/
theorem tendsto_sum_norm_actualPositiveCarlsonStrip_twoHeight
    {sigma tau alpha gamma epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hgammaAlpha : gamma ≤ alpha)
    (hepsilon : 0 < epsilon)
    (hlow :
      carlsonTwoHeightLowExponent sigma tau gamma + epsilon < 0)
    (hhigh :
      carlsonTwoHeightHighExponent sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (fun x =>
        ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
            (carlsonPolynomialHeight alpha x),
          ‖pntRelativeZeroContribution x rho‖)
      atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (fun x =>
          actualCarlsonTwoHeightLowBudget sigma tau gamma x +
            actualCarlsonTwoHeightHighBudget sigma tau alpha gamma x)
        atTop (nhds 0) :=
    by
      simpa using
        (tendsto_actualCarlsonTwoHeightLowBudget
          hsigma hsigmaOne hgamma hepsilon hlow).add
          (tendsto_actualCarlsonTwoHeightHighBudget
            hsigma hsigmaOne halpha hepsilon hhigh)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards with x
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact sum_norm_actualPositiveCarlsonStrip_le_twoHeightBudget
      hx (lt_trans (by norm_num) hsigma) hgammaAlpha

end PrimeNumberTheorem
