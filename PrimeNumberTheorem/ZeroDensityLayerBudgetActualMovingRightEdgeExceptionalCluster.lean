import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPositiveOutsideClusterCapQuantitativeReverseZeroFree
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualExplicitFormulaClusterDecomposition

/-!
# Moving right-edge exceptional clusters

The exceptional zero cluster now grows with the explicit-formula height. At
each scale it contains every visible right-edge zero and every real-ordinate
zero, making the local outside-cluster real-part cap automatic.
-/

namespace PrimeNumberTheorem

/-- Every positive-ordinate nontrivial zero visible at `height x` and outside
the scale-dependent cluster has real part at most `upper`. -/
def MovingPositiveOutsideClusterRealPartCap
    (height : ℝ → ℝ)
    (cluster : ℝ → Finset ℂ)
    (upper : ℝ) : Prop :=
  ∀ x : ℝ, ∀ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho →
      0 < rho.im →
        rho.im ≤ height x →
          rho ∉ cluster x →
            rho.re ≤ upper

/-- At scale `x`, collect every right-edge zero visible below `height x` and
adjoin the complete finite real-ordinate zero slice. -/
noncomputable def movingRightEdgeExceptionalCluster
    (height : ℝ → ℝ) (beta x : ℝ) : Finset ℂ :=
  actualCarlsonAdjoinRealOrdinateZeros
    (rightEdgeNontrivialZerosFinset beta (height x))

/-- Increasing the height enlarges the moving exceptional cluster. -/
theorem movingRightEdgeExceptionalCluster_mono_height
    {height : ℝ → ℝ} {beta x y : ℝ}
    (hxy : height x ≤ height y) :
    movingRightEdgeExceptionalCluster height beta x ⊆
      movingRightEdgeExceptionalCluster height beta y := by
  intro rho hrho
  unfold movingRightEdgeExceptionalCluster at hrho ⊢
  unfold actualCarlsonAdjoinRealOrdinateZeros at hrho ⊢
  rcases Finset.mem_union.mp hrho with hright | hreal
  · apply Finset.mem_union_left
    rcases mem_rightEdgeNontrivialZerosFinset.mp hright with
      ⟨hzero, hheight, hre⟩
    exact mem_rightEdgeNontrivialZerosFinset.mpr
      ⟨hzero, hheight.trans hxy, hre⟩
  · exact Finset.mem_union_right _ hreal

/-- Every moving exceptional cluster is conjugation invariant. -/
theorem movingRightEdgeExceptionalCluster_conjugationInvariant
    (height : ℝ → ℝ) (beta x : ℝ) :
    IsConjugationInvariantCluster
      (movingRightEdgeExceptionalCluster height beta x) := by
  intro rho
  exact
    (actualCarlsonAdjoinRealOrdinateZeros_conjugationStable
      (rightEdgeNontrivialZerosFinset beta (height x))
      (fun z =>
        (rightEdgeNontrivialZerosFinset_conjugationInvariant
          beta (height x) z).symm)
      rho).symm

/-- The fixed real-ordinate nontrivial-zero slice is captured at every scale. -/
theorem realOrdinateNontrivialZerosFinset_subset_movingRightEdgeExceptionalCluster
    (height : ℝ → ℝ) (beta x : ℝ) :
    realOrdinateNontrivialZerosFinset 0 ⊆
      movingRightEdgeExceptionalCluster height beta x := by
  intro rho hrho
  unfold movingRightEdgeExceptionalCluster
  unfold actualCarlsonAdjoinRealOrdinateZeros
  exact Finset.mem_union_right _ hrho

/-- A visible positive-ordinate zero outside the moving right-edge cluster is
strictly left of `beta`. -/
theorem positiveNontrivialZero_re_lt_of_not_mem_movingRightEdgeExceptionalCluster
    {height : ℝ → ℝ} {beta x : ℝ} {rho : ℂ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im)
    (hheight : rho.im ≤ height x)
    (hout :
      rho ∉ movingRightEdgeExceptionalCluster height beta x) :
    rho.re < beta := by
  apply lt_of_not_ge
  intro hbeta
  apply hout
  unfold movingRightEdgeExceptionalCluster
  unfold actualCarlsonAdjoinRealOrdinateZeros
  apply Finset.mem_union_left
  apply mem_rightEdgeNontrivialZerosFinset.mpr
  refine ⟨hzero, ?_, hbeta⟩
  simpa [abs_of_pos him] using hheight

/-- The moving right-edge exceptional cluster has an automatic local positive
outside-cluster cap at `beta`. -/
theorem movingRightEdgeExceptionalCluster_positiveOutsideCap
    (height : ℝ → ℝ) (beta : ℝ) :
    MovingPositiveOutsideClusterRealPartCap
      height (movingRightEdgeExceptionalCluster height beta) beta := by
  intro x rho hzero him hheight hout
  exact
    (positiveNontrivialZero_re_lt_of_not_mem_movingRightEdgeExceptionalCluster
      hzero him hheight hout).le

/-- The visible main formed from the moving right-edge exceptional cluster. -/
noncomputable def movingRightEdgeVisibleClusterPNTMain
    (height : ℝ → ℝ) (beta x : ℝ) : ℝ :=
  dynamicVisibleClusterPNTMain
    height (movingRightEdgeExceptionalCluster height beta x) x

/-- The signed finite zero complement outside the moving right-edge cluster. -/
noncomputable def movingRightEdgeOutsideClusterPNTComplement
    (height : ℝ → ℝ) (beta x : ℝ) : ℝ :=
  dynamicOutsideClusterPNTComplement
    height (movingRightEdgeExceptionalCluster height beta x) x

/-- Exact actual explicit-formula decomposition around the scale-dependent
right-edge exceptional cluster. -/
theorem relativeChebyshevPsi0Error_eq_movingRightEdgeCluster_add_actualResiduals
    (height : ℝ → ℝ) (beta x : ℝ) :
    relativeChebyshevPsi0Error x =
      movingRightEdgeVisibleClusterPNTMain height beta x +
        (actualPNTClosedRealAxisRelativeTerm x +
          actualPNTExplicitFormulaRelativeRemainder height x +
          movingRightEdgeOutsideClusterPNTComplement height beta x) := by
  simpa [movingRightEdgeVisibleClusterPNTMain,
    movingRightEdgeOutsideClusterPNTComplement] using
    relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
      height (movingRightEdgeExceptionalCluster height beta x) x

end PrimeNumberTheorem
