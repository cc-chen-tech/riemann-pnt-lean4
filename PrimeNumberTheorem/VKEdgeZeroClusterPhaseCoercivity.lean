import Mathlib.Algebra.Order.Chebyshev
import PrimeNumberTheorem.VKEdgeZeroClusterCoercivity

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Phase coercivity for equal-ordinate zero clusters

For zeros in the critical strip with a common positive ordinate, the
coefficients `m(ρ) exp ((re ρ - beta) a) / ρ` all have nonpositive imaginary
part.  Quantitatively, when `1 ≤ im ρ` and `0 < re ρ ≤ 1`, at least half of
each coefficient norm survives in that common direction.  Thus collecting
equal frequencies cannot hide the cluster energy by phase cancellation.
-/

/-- A coefficient attached to a zero with `0 < re ρ ≤ 1 ≤ im ρ` has at
least half of its norm in the negative imaginary direction. -/
theorem half_norm_finiteZeroClusterCoefficientAt_le_neg_im
    {multiplicity : ℂ → ℕ} {beta a gamma : ℝ} {rho : ℂ}
    (hre : 0 < rho.re) (hre1 : rho.re ≤ 1)
    (him : rho.im = gamma) (hgamma : 1 ≤ gamma) :
    (1 / 2 : ℝ) * ‖finiteZeroClusterCoefficientAt multiplicity beta a rho‖ ≤
      -(finiteZeroClusterCoefficientAt multiplicity beta a rho).im := by
  let weight : ℝ :=
    (multiplicity rho : ℝ) * Real.exp ((rho.re - beta) * a)
  have hweight : 0 ≤ weight := by
    dsimp [weight]
    positivity
  have hgamma_pos : 0 < gamma := lt_of_lt_of_le zero_lt_one hgamma
  have hrho : rho ≠ 0 := by
    intro hrho
    have : rho.im = 0 := by simp [hrho]
    linarith
  have hnorm_pos : 0 < ‖rho‖ := norm_pos_iff.mpr hrho
  have hre_sq_le_gamma_sq : rho.re ^ 2 ≤ gamma ^ 2 := by
    nlinarith
  have hnorm_sq_le : ‖rho‖ ^ 2 ≤ (2 * gamma) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, him]
    nlinarith [sq_nonneg gamma]
  have hnorm_le : ‖rho‖ ≤ 2 * gamma := by
    apply (sq_le_sq₀ (norm_nonneg rho) (by positivity)).mp
    simpa using hnorm_sq_le
  have hinv :
      (1 / 2 : ℝ) * ‖rho⁻¹‖ ≤ -(rho⁻¹).im := by
    rw [norm_inv, Complex.inv_im, him,
      Complex.normSq_eq_norm_sq]
    simp only [neg_div, neg_neg]
    rw [inv_eq_one_div]
    rw [show (1 / 2 : ℝ) * (1 / ‖rho‖) =
        (1 / 2 : ℝ) / ‖rho‖ by ring]
    apply (div_le_div_iff₀ hnorm_pos (sq_pos_of_pos hnorm_pos)).2
    nlinarith
  have hcoeff :
      finiteZeroClusterCoefficientAt multiplicity beta a rho =
        (weight : ℂ) * rho⁻¹ := by
    simp only [finiteZeroClusterCoefficientAt, weight, ofReal_mul]
    push_cast
    ring
  rw [hcoeff, norm_mul, Complex.mul_im]
  simp only [ofReal_re, ofReal_im, zero_mul, add_zero, norm_real,
    Real.norm_eq_abs, abs_of_nonneg hweight]
  have hscaled := mul_le_mul_of_nonneg_left hinv hweight
  nlinarith

/-- After collecting every zero with a fixed positive ordinate, at least half
of the sum of the individual coefficient norms survives.  In particular,
equal ordinates do not create an uncontrolled cancellation loss. -/
theorem
    half_sum_norm_finiteZeroClusterCoefficientAt_le_norm_mergedFrequencyCoefficient
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a gamma : ℝ}
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (hgamma : 1 ≤ gamma) :
    (1 / 2 : ℝ) *
          ∑ rho ∈ S.filter (fun rho => rho.im = gamma),
            ‖finiteZeroClusterCoefficientAt multiplicity beta a rho‖ ≤
      ‖MathlibAux.mergedFrequencyCoefficient S
          (finiteZeroClusterCoefficientAt multiplicity beta a)
          Complex.im gamma‖ := by
  classical
  let fiber := S.filter (fun rho => rho.im = gamma)
  let coeff := finiteZeroClusterCoefficientAt multiplicity beta a
  have hterm :
      ∀ rho ∈ fiber, (1 / 2 : ℝ) * ‖coeff rho‖ ≤ -(coeff rho).im := by
    intro rho hrho
    have hmem := (Finset.mem_filter.mp hrho)
    exact half_norm_finiteZeroClusterCoefficientAt_le_neg_im
      (hre rho hmem.1).1 (hre rho hmem.1).2 hmem.2 hgamma
  have hsum :
      (1 / 2 : ℝ) * ∑ rho ∈ fiber, ‖coeff rho‖ ≤
        ∑ rho ∈ fiber, -(coeff rho).im := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  rw [MathlibAux.mergedFrequencyCoefficient]
  change (1 / 2 : ℝ) * ∑ rho ∈ fiber, ‖coeff rho‖ ≤
    ‖∑ rho ∈ fiber, coeff rho‖
  calc
    (1 / 2 : ℝ) * ∑ rho ∈ fiber, ‖coeff rho‖ ≤
        ∑ rho ∈ fiber, -(coeff rho).im := hsum
    _ = -(∑ rho ∈ fiber, coeff rho).im := by
      rw [Complex.im_sum, Finset.sum_neg_distrib]
    _ ≤ |(∑ rho ∈ fiber, coeff rho).im| := neg_le_abs _
    _ ≤ ‖∑ rho ∈ fiber, coeff rho‖ := Complex.abs_im_le_norm _

/-- The diagonal energy after merging equal ordinates controls one quarter
of the sum of the squared fiber masses.  This is the collision-safe energy
form of the common-phase estimate. -/
theorem quarter_sum_sameOrdinateFiberMass_sq_le_mergedFrequencyEnergy
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a : ℝ}
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (him : ∀ rho ∈ S, 1 ≤ rho.im) :
    (1 / 4 : ℝ) *
          ∑ gamma ∈ MathlibAux.mergedFrequencySupport S Complex.im,
            (∑ rho ∈ S.filter (fun rho => rho.im = gamma),
              ‖finiteZeroClusterCoefficientAt
                multiplicity beta a rho‖) ^ 2 ≤
      ∑ gamma ∈ MathlibAux.mergedFrequencySupport S Complex.im,
        ‖MathlibAux.mergedFrequencyCoefficient S
            (finiteZeroClusterCoefficientAt multiplicity beta a)
            Complex.im gamma‖ ^ 2 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro gamma hgamma
  have hgamma_one : 1 ≤ gamma := by
    rw [MathlibAux.mergedFrequencySupport] at hgamma
    rcases Finset.mem_image.mp hgamma with ⟨rho, hrho, hrhoGamma⟩
    rw [← hrhoGamma]
    exact him rho hrho
  have hfiber :=
    half_sum_norm_finiteZeroClusterCoefficientAt_le_norm_mergedFrequencyCoefficient
      (S := S) (multiplicity := multiplicity) (beta := beta) (a := a)
      (gamma := gamma) hre hgamma_one
  have hmass :
      0 ≤ ∑ rho ∈ S.filter (fun rho => rho.im = gamma),
        ‖finiteZeroClusterCoefficientAt multiplicity beta a rho‖ := by
    positivity
  have hmerged :
      0 ≤ ‖MathlibAux.mergedFrequencyCoefficient S
        (finiteZeroClusterCoefficientAt multiplicity beta a)
        Complex.im gamma‖ := norm_nonneg _
  nlinarith

/-- A global form of phase coercivity: the total coefficient mass is
controlled by the merged diagonal energy, with only the number of distinct
ordinates as a loss. -/
theorem totalCoefficientMass_sq_le_four_card_mul_mergedFrequencyEnergy
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a : ℝ}
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (him : ∀ rho ∈ S, 1 ≤ rho.im) :
    (∑ rho ∈ S,
        ‖finiteZeroClusterCoefficientAt multiplicity beta a rho‖) ^ 2 ≤
      4 * (MathlibAux.mergedFrequencySupport S Complex.im).card *
        ∑ gamma ∈ MathlibAux.mergedFrequencySupport S Complex.im,
          ‖MathlibAux.mergedFrequencyCoefficient S
              (finiteZeroClusterCoefficientAt multiplicity beta a)
              Complex.im gamma‖ ^ 2 := by
  classical
  let support := MathlibAux.mergedFrequencySupport S Complex.im
  let coeff := finiteZeroClusterCoefficientAt multiplicity beta a
  have hmaps : ∀ rho ∈ S, rho.im ∈ support := by
    intro rho hrho
    exact Finset.mem_image_of_mem Complex.im hrho
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun rho => ‖coeff rho‖)
  have hhalf :
      (1 / 2 : ℝ) * ∑ rho ∈ S, ‖coeff rho‖ ≤
        ∑ gamma ∈ support,
          ‖MathlibAux.mergedFrequencyCoefficient S coeff
              Complex.im gamma‖ := by
    calc
      (1 / 2 : ℝ) * ∑ rho ∈ S, ‖coeff rho‖ =
          (1 / 2 : ℝ) *
            ∑ gamma ∈ support,
              ∑ rho ∈ S.filter (fun rho => rho.im = gamma),
                ‖coeff rho‖ := by rw [hfiber]
      _ = ∑ gamma ∈ support,
            (1 / 2 : ℝ) *
              ∑ rho ∈ S.filter (fun rho => rho.im = gamma),
                ‖coeff rho‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ gamma ∈ support,
            ‖MathlibAux.mergedFrequencyCoefficient S coeff
                Complex.im gamma‖ := by
        apply Finset.sum_le_sum
        intro gamma hgamma
        have hgamma_one : 1 ≤ gamma := by
          dsimp [support, MathlibAux.mergedFrequencySupport] at hgamma
          rcases Finset.mem_image.mp hgamma with ⟨rho, hrho, hrhoGamma⟩
          rw [← hrhoGamma]
          exact him rho hrho
        exact
          half_sum_norm_finiteZeroClusterCoefficientAt_le_norm_mergedFrequencyCoefficient
            (S := S) (multiplicity := multiplicity)
            (beta := beta) (a := a) (gamma := gamma)
            hre hgamma_one
  have hcauchy :
      (∑ gamma ∈ support,
          ‖MathlibAux.mergedFrequencyCoefficient S coeff
              Complex.im gamma‖) ^ 2 ≤
        (support.card : ℝ) *
          ∑ gamma ∈ support,
            ‖MathlibAux.mergedFrequencyCoefficient S coeff
                Complex.im gamma‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmass_nonneg :
      0 ≤ (1 / 2 : ℝ) * ∑ rho ∈ S, ‖coeff rho‖ := by positivity
  have hmerged_nonneg :
      0 ≤ ∑ gamma ∈ support,
        ‖MathlibAux.mergedFrequencyCoefficient S coeff
            Complex.im gamma‖ := by positivity
  have hsquare :
      ((1 / 2 : ℝ) * ∑ rho ∈ S, ‖coeff rho‖) ^ 2 ≤
        (∑ gamma ∈ support,
          ‖MathlibAux.mergedFrequencyCoefficient S coeff
              Complex.im gamma‖) ^ 2 :=
    (sq_le_sq₀ hmass_nonneg hmerged_nonneg).2 hhalf
  change (∑ rho ∈ S, ‖coeff rho‖) ^ 2 ≤
    4 * support.card *
      ∑ gamma ∈ support,
        ‖MathlibAux.mergedFrequencyCoefficient S coeff
            Complex.im gamma‖ ^ 2
  calc
    (∑ rho ∈ S, ‖coeff rho‖) ^ 2 =
        4 * ((1 / 2 : ℝ) * ∑ rho ∈ S, ‖coeff rho‖) ^ 2 := by ring
    _ ≤ 4 *
        (∑ gamma ∈ support,
          ‖MathlibAux.mergedFrequencyCoefficient S coeff
              Complex.im gamma‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by norm_num)
    _ ≤ 4 * ((support.card : ℝ) *
        ∑ gamma ∈ support,
          ‖MathlibAux.mergedFrequencyCoefficient S coeff
              Complex.im gamma‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcauchy (by norm_num)
    _ = 4 * support.card *
        ∑ gamma ∈ support,
          ‖MathlibAux.mergedFrequencyCoefficient S coeff
              Complex.im gamma‖ ^ 2 := by ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
