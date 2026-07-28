import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterKernelTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterSignedComplement

/-!
# Explicit coefficient mass for a finite visible cluster

For a finite set of zeros with real parts at most `beta`, the visible relative
PNT main term is bounded on `x ≥ 1` by

`finiteVisibleClusterCoefficientMass E * x ^ (beta - 1)`.

The coefficient mass retains analytic multiplicity and the exact `1 / ‖rho‖`
kernel weight.  This converts a functional perturbation hypothesis into a
finite numerical inequality, without claiming that the mass is automatically
small.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Multiplicity-weighted `1 / ‖rho‖` mass of a finite zero cluster. -/
noncomputable def finiteVisibleClusterCoefficientMass (E : Finset ℂ) : ℝ :=
  ∑ rho ∈ E, (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖

theorem finiteVisibleClusterCoefficientMass_nonneg (E : Finset ℂ) :
    0 ≤ finiteVisibleClusterCoefficientMass E := by
  unfold finiteVisibleClusterCoefficientMass
  positivity

/-- One actual relative PNT zero contribution is bounded by its exact
coefficient weight at every exponent cap `rho.re ≤ beta`. -/
theorem norm_pntRelativeZeroContribution_le_coefficient_mul_targetAmplitude
    {x beta : ℝ} (hx : 1 ≤ x) {rho : ℂ} (hre : rho.re ≤ beta) :
    ‖pntRelativeZeroContribution x rho‖ ≤
      ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
        targetZeroPowerAmplitude beta x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have htarget :
      0 < targetZeroPowerAmplitude beta x := by
    exact Real.rpow_pos_of_pos hxpos _
  have hexponent : rho.re - beta ≤ 0 := sub_nonpos.mpr hre
  have hpower : x ^ (rho.re - beta) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx hexponent
  have hweight :
      0 ≤ (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ := by
    positivity
  apply (div_le_iff₀ htarget).mp
  calc
    ‖pntRelativeZeroContribution x rho‖ /
          targetZeroPowerAmplitude beta x =
        ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
          x ^ (rho.re - beta) := by
      simpa [targetZeroPowerAmplitude] using
        norm_pntRelativeZeroContribution_div_targetAmplitude_eq
          hxpos rho
    _ ≤ ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) * 1 :=
      mul_le_mul_of_nonneg_left hpower hweight
    _ = (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ := mul_one _

/-- The complex visible sum of a finite capped cluster is bounded by its
coefficient mass, independently of the truncation schedule. -/
theorem norm_dynamicVisibleClusterPNTZeroSum_le_coefficientMass_mul_targetAmplitude
    (T : ℝ → ℝ) (E : Finset ℂ) {x beta : ℝ}
    (hx : 1 ≤ x) (hre : ∀ rho ∈ E, rho.re ≤ beta) :
    ‖dynamicVisibleClusterPNTZeroSum T E x‖ ≤
      finiteVisibleClusterCoefficientMass E *
        targetZeroPowerAmplitude beta x := by
  classical
  let A := nontrivialZerosFinset (T x)
  let weight : ℂ → ℝ :=
    fun rho => (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖
  have htargetNonneg :
      0 ≤ targetZeroPowerAmplitude beta x :=
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hx) _).le
  have hsubset : A.filter (fun rho => rho ∈ E) ⊆ E := by
    intro rho hrho
    exact (Finset.mem_filter.mp hrho).2
  have hmassSubset :
      (∑ rho ∈ A.filter (fun rho => rho ∈ E), weight rho) ≤
        ∑ rho ∈ E, weight rho := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro rho _ _
    dsimp [weight]
    positivity
  unfold dynamicVisibleClusterPNTZeroSum
  change
    ‖∑ rho ∈ A,
        if rho ∈ E then pntRelativeZeroContribution x rho else 0‖ ≤
      finiteVisibleClusterCoefficientMass E *
        targetZeroPowerAmplitude beta x
  calc
    ‖∑ rho ∈ A,
        if rho ∈ E then pntRelativeZeroContribution x rho else 0‖ ≤
        ∑ rho ∈ A,
          ‖if rho ∈ E then pntRelativeZeroContribution x rho else 0‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ rho ∈ A,
          if rho ∈ E then
            weight rho * targetZeroPowerAmplitude beta x
          else 0 := by
      apply Finset.sum_le_sum
      intro rho _
      by_cases hrho : rho ∈ E
      · simp only [hrho, if_true]
        exact
          norm_pntRelativeZeroContribution_le_coefficient_mul_targetAmplitude
            hx (hre rho hrho)
      · simp [hrho]
    _ =
        ∑ rho ∈ A.filter (fun rho => rho ∈ E),
          weight rho * targetZeroPowerAmplitude beta x := by
      rw [Finset.sum_filter]
    _ =
        (∑ rho ∈ A.filter (fun rho => rho ∈ E), weight rho) *
          targetZeroPowerAmplitude beta x := by
      rw [Finset.sum_mul]
    _ ≤
        (∑ rho ∈ E, weight rho) *
          targetZeroPowerAmplitude beta x :=
      mul_le_mul_of_nonneg_right hmassSubset htargetNonneg
    _ =
        finiteVisibleClusterCoefficientMass E *
          targetZeroPowerAmplitude beta x := by
      rfl

/-- Real visible mains satisfy the same coefficient-mass bound. -/
theorem abs_dynamicVisibleClusterPNTMain_le_coefficientMass_mul_targetAmplitude
    (T : ℝ → ℝ) (E : Finset ℂ) {x beta : ℝ}
    (hx : 1 ≤ x) (hre : ∀ rho ∈ E, rho.re ≤ beta) :
    |dynamicVisibleClusterPNTMain T E x| ≤
      finiteVisibleClusterCoefficientMass E *
        targetZeroPowerAmplitude beta x := by
  calc
    |dynamicVisibleClusterPNTMain T E x| ≤
        ‖dynamicVisibleClusterPNTZeroSum T E x‖ :=
      Complex.abs_re_le_norm
        (dynamicVisibleClusterPNTZeroSum T E x)
    _ ≤
        finiteVisibleClusterCoefficientMass E *
          targetZeroPowerAmplitude beta x :=
      norm_dynamicVisibleClusterPNTZeroSum_le_coefficientMass_mul_targetAmplitude
        T E hx hre

/-- Any strict numerical upper bound on the finite coefficient mass gives the
eventual strict perturbation budget required by seed-extension transfer. -/
theorem eventually_abs_dynamicVisibleClusterPNTMain_lt_loss_mul_targetAmplitude
    (T : ℝ → ℝ) (E : Finset ℂ) {beta loss : ℝ}
    (hre : ∀ rho ∈ E, rho.re ≤ beta)
    (hloss : finiteVisibleClusterCoefficientMass E < loss) :
    ∀ᶠ m : ℕ in atTop,
      |dynamicVisibleClusterPNTMain T E (m : ℝ)| <
        loss * targetZeroPowerAmplitude beta (m : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have htarget :
      0 < targetZeroPowerAmplitude beta (m : ℝ) := by
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hmReal) _
  exact
    lt_of_le_of_lt
      (abs_dynamicVisibleClusterPNTMain_le_coefficientMass_mul_targetAmplitude
        T E hmReal hre)
      (mul_lt_mul_of_pos_right hloss htarget)

end PrimeNumberTheorem
