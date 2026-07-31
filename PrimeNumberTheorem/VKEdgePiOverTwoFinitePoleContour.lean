import PrimeNumberTheorem.VKEdgePiOverTwoConcreteContourAssembly
import PrimeNumberTheorem.VKEdgePiOverTwoFinitePoleFilter

open Complex Polynomial
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- At its center, a localized Gaussian weight is the constant value of its
polynomial factor. -/
theorem localizedGaussianWeight_self
    (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedGaussianWeight A w m w = A.eval 0 := by
  simp [localizedGaussianWeight]

/-- The target-preserving finite-pole filter gives unit weight to the
distinguished zero. -/
theorem localizedGaussianWeight_targetPreservingPoleFilter_self
    (offsets : Finset ℂ) (w : ℂ) (m : ℝ) :
    localizedGaussianWeight
        (targetPreservingPoleFilter offsets) w m w = 1 := by
  rw [localizedGaussianWeight_self]
  exact targetPreservingPoleFilter_eval_zero offsets

/-- Every listed nonzero offset is annihilated exactly by the finite-pole
filter inside the concrete Gaussian residue weight. -/
theorem localizedGaussianWeight_targetPreservingPoleFilter_eq_zero
    {offsets : Finset ℂ} {w rho : ℂ} (m : ℝ)
    (hoffset : rho - w ∈ offsets) (hrho : rho ≠ w) :
    localizedGaussianWeight
        (targetPreservingPoleFilter offsets) w m rho = 0 := by
  unfold localizedGaussianWeight
  rw [targetPreservingPoleFilter_eval_eq_zero
    hoffset (sub_ne_zero.mpr hrho)]
  simp

/--
If the offset list contains every non-target member of a finite zero set,
the filtered analytic-multiplicity residue sum is exactly the multiplicity
of the distinguished zero.
-/
theorem localizedZeroResidueSum_targetPreservingPoleFilter_eq_multiplicity
    {zeros offsets : Finset ℂ} {w : ℂ} (m : ℝ)
    (hw : w ∈ zeros)
    (hoffsets :
      ∀ rho ∈ zeros, rho ≠ w → rho - w ∈ offsets) :
    localizedZeroResidueSum
        (targetPreservingPoleFilter offsets) w m zeros =
      (analyticOrderNatAt riemannZeta w : ℂ) := by
  unfold localizedZeroResidueSum
  rw [Finset.sum_eq_single w]
  · rw [localizedGaussianWeight_targetPreservingPoleFilter_self]
    ring
  · intro rho hrho hrhoNe
    rw [localizedGaussianWeight_targetPreservingPoleFilter_eq_zero
      m (hoffsets rho hrho hrhoNe) hrhoNe]
    simp
  · exact fun hwNot => (hwNot hw).elim

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
