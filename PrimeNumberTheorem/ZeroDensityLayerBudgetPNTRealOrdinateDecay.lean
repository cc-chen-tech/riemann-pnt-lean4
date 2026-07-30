import PrimeNumberTheorem.ZeroDensityLayerBudgetPositiveZeroConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetRelativeKernelBound
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTGoodHeightAdapter

/-!
# Decay of the real-ordinate PNT zero residual

Positive-height density estimates leave zeros with imaginary part zero as a
residual.  No zero-free assertion on the real segment is needed here: once the
height is nonnegative, the residual finset is the fixed height-zero finset.
Every member has real part strictly below one, so its relative PNT kernel tends
to zero.  Finite summation then removes the whole residual.

The module also records that choosing explicit-formula depth `N = 0` makes the
finite trivial-zero contribution exactly zero.
-/

open Complex
open Filter
open scoped BigOperators

namespace PrimeNumberTheorem

/-- For nonnegative truncation height, the real-ordinate residual is the fixed
height-zero finset. -/
theorem realOrdinateNontrivialZerosFinset_eq_zeroHeight
    {T : ℝ} (hT : 0 ≤ T) :
    realOrdinateNontrivialZerosFinset T =
      realOrdinateNontrivialZerosFinset 0 := by
  classical
  ext ρ
  rw [mem_realOrdinateNontrivialZerosFinset,
    mem_realOrdinateNontrivialZerosFinset]
  constructor
  · rintro ⟨hρ, him⟩
    have hzero := (mem_nontrivialZerosFinset.mp hρ).1
    refine ⟨mem_nontrivialZerosFinset.mpr ⟨hzero, ?_⟩, him⟩
    simp [him]
  · rintro ⟨hρ, him⟩
    have hzero := (mem_nontrivialZerosFinset.mp hρ).1
    refine ⟨mem_nontrivialZerosFinset.mpr ⟨hzero, ?_⟩, him⟩
    simpa [him] using hT

/-- The norm of the relative simple kernel of one nontrivial zero tends to
zero solely from `Re rho < 1`. -/
theorem tendsto_norm_pntRelativeSimpleZeroKernel_atTop
    {ρ : ℂ} (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    Tendsto (fun x : ℝ => ‖pntRelativeSimpleZeroKernel x ρ‖)
      atTop (nhds 0) := by
  have hgap : 0 < 1 - ρ.re := sub_pos.mpr hρ.2.2
  have hrpow :
      Tendsto (fun x : ℝ => x ^ (ρ.re - 1) / ‖ρ‖)
        atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop hgap).div_const ‖ρ‖ using 1
    · funext x
      congr 2
      ring
    · simp
  apply hrpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (norm_pntRelativeSimpleZeroKernel_eq hx ρ).symm

/-- The multiplicity-weighted relative contribution of one nontrivial zero
tends to zero. -/
theorem tendsto_pntRelativeZeroContribution_atTop
    {ρ : ℂ} (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    Tendsto (fun x : ℝ => pntRelativeZeroContribution x ρ)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm,
    mul_zero] using
      (tendsto_norm_pntRelativeSimpleZeroKernel_atTop hρ).const_mul
        (analyticOrderNatAt riemannZeta ρ : ℝ)

/-- The complete height-zero real-ordinate residual tends to zero. -/
theorem tendsto_realOrdinateRelativeZeroResidual_zeroHeight :
    Tendsto
      (fun x : ℝ =>
        ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset 0,
          pntRelativeZeroContribution x ρ‖)
      atTop (nhds 0) := by
  have hsum :
      Tendsto
        (fun x : ℝ =>
          ∑ ρ ∈ realOrdinateNontrivialZerosFinset 0,
            pntRelativeZeroContribution x ρ)
        atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finset_sum (realOrdinateNontrivialZerosFinset 0)
        fun ρ hρ =>
          tendsto_pntRelativeZeroContribution_atTop
            (mem_nontrivialZerosFinset.mp
              (mem_realOrdinateNontrivialZerosFinset.mp hρ).1).1)
  exact tendsto_zero_iff_norm_tendsto_zero.mp hsum

/-- Any eventually nonnegative dynamic height has the same vanishing
real-ordinate residual. -/
theorem tendsto_realOrdinateRelativeZeroResidual_of_eventually_nonneg
    (height : ℝ → ℝ)
    (hheight : ∀ᶠ x in atTop, 0 ≤ height x) :
    Tendsto
      (fun x : ℝ =>
        ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset (height x),
          pntRelativeZeroContribution x ρ‖)
      atTop (nhds 0) := by
  apply tendsto_realOrdinateRelativeZeroResidual_zeroHeight.congr'
  filter_upwards [hheight] with x hx
  rw [realOrdinateNontrivialZerosFinset_eq_zeroHeight hx]

/-- At depth zero the explicit formula contains no finite trivial-zero terms. -/
theorem cofinalTrivialZeroContribution_zero (m : ℕ) :
    cofinalTrivialZeroContribution m 0 = 0 := by
  simp [cofinalTrivialZeroContribution,
    ExplicitFormulaAux.finiteTrivialZeroSum]

end PrimeNumberTheorem
