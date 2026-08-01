import PrimeNumberTheorem.VKEdgeZeroClusterCoercivity
import PrimeNumberTheorem.VKEdgeHighZeroBucketEnergy

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Quantitative detect-or-count mass transfer

This module converts the absolute Gaussian coefficient mass of an actual
finite zeta-zero packet into the analytic-multiplicity mass counted by
Carlson-type bounds.  It does not assume simple zeros and does not claim a
lower bound for the number of distinct zeros.
-/

/-- In the non-growing real-part regime and above unit modulus, one frozen
Gaussian zero coefficient is bounded by its analytic multiplicity. -/
theorem norm_finiteZeroClusterCoefficientAt_le_analyticMultiplicity
    {beta a : ℝ} {rho : ℂ}
    (ha : 0 ≤ a) (hre : rho.re ≤ beta) (hnorm : 1 ≤ ‖rho‖) :
    ‖finiteZeroClusterCoefficientAt
        (analyticOrderNatAt (𝕜 := ℂ) riemannZeta) beta a rho‖ ≤
      (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) := by
  have hexponent : (rho.re - beta) * a ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hre) ha
  have hexpLe : Real.exp ((rho.re - beta) * a) ≤ 1 :=
    Real.exp_le_one_iff.mpr hexponent
  have hnormPos : 0 < ‖rho‖ := lt_of_lt_of_le zero_lt_one hnorm
  have hinvLe : ‖rho‖⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hnormPos).2 hnorm
  have hinvNonneg : 0 ≤ ‖rho‖⁻¹ := inv_nonneg.mpr (norm_nonneg rho)
  have hmultNonneg :
      0 ≤ (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) := by positivity
  unfold finiteZeroClusterCoefficientAt
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), RCLike.norm_natCast]
  calc
    (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) * ‖rho‖⁻¹ *
          Real.exp ((rho.re - beta) * a) ≤
        (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) * 1 *
          Real.exp ((rho.re - beta) * a) := by
      gcongr
    _ ≤ (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) * 1 * 1 := by
      gcongr
    _ = (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) := by ring

/-- The complete absolute Gaussian coefficient mass of a finite actual-zeta
packet is bounded by its analytic-multiplicity mass. -/
theorem sum_norm_finiteZeroClusterCoefficientAt_le_analyticMultiplicityMass
    (P : Finset ℂ) {beta a : ℝ}
    (ha : 0 ≤ a)
    (hre : ∀ rho ∈ P, rho.re ≤ beta)
    (hnorm : ∀ rho ∈ P, 1 ≤ ‖rho‖) :
    (∑ rho ∈ P,
        ‖finiteZeroClusterCoefficientAt
          (analyticOrderNatAt (𝕜 := ℂ) riemannZeta) beta a rho‖) ≤
      ∑ rho ∈ P,
        (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) := by
  exact Finset.sum_le_sum fun rho hrho =>
    norm_finiteZeroClusterCoefficientAt_le_analyticMultiplicity
      ha (hre rho hrho) (hnorm rho hrho)

/-- A quantitative Gaussian coefficient-mass lower bound is already a
quantitative Carlson-relevant analytic-multiplicity lower bound. -/
theorem gaussianCoefficientMass_lowerBound_to_analyticMultiplicityMass
    (P : Finset ℂ) {beta a mu : ℝ}
    (ha : 0 ≤ a)
    (hre : ∀ rho ∈ P, rho.re ≤ beta)
    (hnorm : ∀ rho ∈ P, 1 ≤ ‖rho‖)
    (hmass : mu ≤ ∑ rho ∈ P,
      ‖finiteZeroClusterCoefficientAt
        (analyticOrderNatAt (𝕜 := ℂ) riemannZeta) beta a rho‖) :
    mu ≤ ∑ rho ∈ P,
      (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) :=
  hmass.trans
    (sum_norm_finiteZeroClusterCoefficientAt_le_analyticMultiplicityMass
      P ha hre hnorm)

/-- Quantitative detect-or-count adapter.  The detection branch records a
genuinely new zero; the cluster branch records analytic-multiplicity mass,
not merely nonemptiness. -/
theorem newZero_or_gaussianCoefficientMass_to_detect_or_count
    (S P : Finset ℂ) {beta a mu : ℝ}
    (ha : 0 ≤ a)
    (hre : ∀ rho ∈ P, rho.re ≤ beta)
    (hnorm : ∀ rho ∈ P, 1 ≤ ‖rho‖)
    (hdetectOrMass :
      (∃ rho ∈ P, rho ∉ S) ∨
        mu ≤ ∑ rho ∈ P,
          ‖finiteZeroClusterCoefficientAt
            (analyticOrderNatAt (𝕜 := ℂ) riemannZeta) beta a rho‖) :
    (∃ rho ∈ P, rho ∉ S) ∨
      mu ≤ ∑ rho ∈ P,
        (analyticOrderNatAt (𝕜 := ℂ) riemannZeta rho : ℝ) := by
  rcases hdetectOrMass with hdetect | hmass
  · exact Or.inl hdetect
  · exact Or.inr
      (gaussianCoefficientMass_lowerBound_to_analyticMultiplicityMass
        P ha hre hnorm hmass)

end
end VKEdgePiOverTwo
end PrimeNumberTheorem
