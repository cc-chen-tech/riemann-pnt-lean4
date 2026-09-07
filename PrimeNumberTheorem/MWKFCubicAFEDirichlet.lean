import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import PrimeNumberTheorem.MWKFCubicAFEVerticalDecay

open Complex Filter
open scoped ComplexConjugate

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Absolutely convergent Dirichlet expansion of the cubic AFE line

On `re z > 1/2`, both shifted zeta factors lie in their half-plane of
absolute convergence.  This file records the exact gamma normalization and
the resulting double Dirichlet series before any integral interchange.
-/

theorem one_sub_cubicCriticalPoint_eq_conj (t : ℝ) :
    1 - cubicCriticalPoint t = conj (cubicCriticalPoint t) := by
  apply Complex.ext
  · norm_num [cubicCriticalPoint]
  · simp [cubicCriticalPoint]

/-- The classical zeta product on the critical line is the real norm square. -/
theorem riemannZeta_cubicCriticalPoint_mul_one_sub_eq_normSq (t : ℝ) :
    riemannZeta (cubicCriticalPoint t) *
        riemannZeta (1 - cubicCriticalPoint t) =
      (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ) := by
  rw [one_sub_cubicCriticalPoint_eq_conj, riemannZeta_conj]
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- Product of the two archimedean factors in the symmetric AFE. -/
noncomputable def cubicAFEGammaProduct (t : ℝ) (z : ℂ) : ℂ :=
  Gammaℝ (cubicCriticalPoint t + z) *
    Gammaℝ (1 - cubicCriticalPoint t + z)

private theorem completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

theorem cubicAFEGammaProduct_zero_ne (t : ℝ) :
    cubicAFEGammaProduct t 0 ≠ 0 := by
  apply mul_ne_zero
  · apply Gammaℝ_ne_zero_of_re_pos
    norm_num [cubicCriticalPoint]
  · apply Gammaℝ_ne_zero_of_re_pos
    norm_num [cubicCriticalPoint]

/-- Exact removal of the fixed gamma factors at the critical point. -/
theorem completedRiemannZeta_product_eq_gamma_mul_normSq (t : ℝ) :
    completedRiemannZeta (cubicCriticalPoint t) *
        completedRiemannZeta (1 - cubicCriticalPoint t) =
      cubicAFEGammaProduct t 0 *
        (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ) := by
  rw [completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos
      (by norm_num [cubicCriticalPoint]),
    completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos
      (by norm_num [cubicCriticalPoint])]
  rw [show Gammaℝ (cubicCriticalPoint t) * riemannZeta (cubicCriticalPoint t) *
      (Gammaℝ (1 - cubicCriticalPoint t) *
        riemannZeta (1 - cubicCriticalPoint t)) =
      (Gammaℝ (cubicCriticalPoint t) *
        Gammaℝ (1 - cubicCriticalPoint t)) *
      (riemannZeta (cubicCriticalPoint t) *
        riemannZeta (1 - cubicCriticalPoint t)) by ring,
    riemannZeta_cubicCriticalPoint_mul_one_sub_eq_normSq]
  simp [cubicAFEGammaProduct]

/-- The `(m,n)` term of the absolutely convergent shifted double Dirichlet
series, indexed from zero but using the positive integers `m+1,n+1`. -/
noncomputable def cubicAFEDirichletTerm
    (t : ℝ) (z : ℂ) (p : ℕ × ℕ) : ℂ :=
  (1 / (p.1 + 1 : ℂ) ^ (cubicCriticalPoint t + z)) *
    (1 / (p.2 + 1 : ℂ) ^ (1 - cubicCriticalPoint t + z))

private theorem summable_norm_shifted_zetaSeries
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ ↦ ‖1 / (n + 1 : ℂ) ^ s‖) := by
  rw [summable_norm_iff]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2
      (Complex.summable_one_div_nat_cpow.mpr hs)

/-- Absolute convergence of the exact two-variable Dirichlet family on the
physical AFE line. -/
theorem summable_norm_cubicAFEDirichletTerm
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) :
    Summable (fun p : ℕ × ℕ ↦ ‖cubicAFEDirichletTerm t z p‖) := by
  have hs : 1 < (cubicCriticalPoint t + z).re := by
    norm_num [cubicCriticalPoint]
    linarith
  have hu : 1 < (1 - cubicCriticalPoint t + z).re := by
    norm_num [cubicCriticalPoint]
    linarith
  have hleft := summable_norm_shifted_zetaSeries hs
  have hright := summable_norm_shifted_zetaSeries hu
  simpa [cubicAFEDirichletTerm, norm_mul] using hleft.mul_norm hright

/-- Exact product expansion of the two completed zeta factors on the
absolutely convergent AFE line. -/
theorem completedRiemannZeta_shifted_product_eq_tsum
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) :
    completedRiemannZeta (cubicCriticalPoint t + z) *
        completedRiemannZeta (1 - cubicCriticalPoint t + z) =
      cubicAFEGammaProduct t z *
        ∑' p : ℕ × ℕ, cubicAFEDirichletTerm t z p := by
  have hs : 1 < (cubicCriticalPoint t + z).re := by
    norm_num [cubicCriticalPoint]
    linarith
  have hu : 1 < (1 - cubicCriticalPoint t + z).re := by
    norm_num [cubicCriticalPoint]
    linarith
  have hleftNorm := summable_norm_shifted_zetaSeries hs
  have hrightNorm := summable_norm_shifted_zetaSeries hu
  rw [completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos (zero_lt_one.trans hs),
    completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos (zero_lt_one.trans hu),
    zeta_eq_tsum_one_div_nat_add_one_cpow hs,
    zeta_eq_tsum_one_div_nat_add_one_cpow hu]
  rw [show
      (Gammaℝ (cubicCriticalPoint t + z) *
          ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (cubicCriticalPoint t + z)) *
        (Gammaℝ (1 - cubicCriticalPoint t + z) *
          ∑' n : ℕ, 1 / (n + 1 : ℂ) ^
            (1 - cubicCriticalPoint t + z)) =
      cubicAFEGammaProduct t z *
        ((∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (cubicCriticalPoint t + z)) *
          (∑' n : ℕ, 1 / (n + 1 : ℂ) ^
            (1 - cubicCriticalPoint t + z))) by
        simp only [cubicAFEGammaProduct]
        ring,
    tsum_mul_tsum_of_summable_norm hleftNorm hrightNorm]
  rfl

/-- One normalized summand of the pole-cancelled AFE integrand. -/
noncomputable def cubicAFENormalizedDirichletTerm
    (t : ℝ) (z : ℂ) (p : ℕ × ℕ) : ℂ :=
  (cubicAFEKernelG t z * cubicAFEGammaProduct t z /
      cubicAFEGammaProduct t 0 / z) *
    cubicAFEDirichletTerm t z p

/-- Pointwise equality between the normalized completed AFE integrand and
the absolutely convergent double Dirichlet series on `re z > 1/2`. -/
theorem cubicAFECompletedIntegrand_div_gamma_eq_tsum
    (t : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) :
    cubicAFECompletedIntegrand t z / cubicAFEGammaProduct t 0 =
      ∑' p : ℕ × ℕ, cubicAFENormalizedDirichletTerm t z p := by
  have hsplus : cubicCriticalPoint t + z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [cubicCriticalPoint] at hre
    linarith
  have huplus : 1 - cubicCriticalPoint t + z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [cubicCriticalPoint] at hre
    linarith
  have husub : 1 - cubicCriticalPoint t - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [cubicCriticalPoint] at hre
    linarith
  have hssub : cubicCriticalPoint t - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [cubicCriticalPoint] at hre
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  rw [cubicAFECompletedIntegrand, cubicAFECompletedExtension_eq t z
      hsplus husub huplus hssub]
  rw [show cubicAFEKernelG t z *
        completedRiemannZeta (cubicCriticalPoint t + z) *
          completedRiemannZeta (1 - cubicCriticalPoint t + z) =
      cubicAFEKernelG t z *
        (completedRiemannZeta (cubicCriticalPoint t + z) *
          completedRiemannZeta (1 - cubicCriticalPoint t + z)) by ring,
    completedRiemannZeta_shifted_product_eq_tsum t hz]
  simp only [cubicAFENormalizedDirichletTerm, tsum_mul_left]
  field_simp [cubicAFEGammaProduct_zero_ne t, hz0]

end MWKFCubic
end PrimeNumberTheorem
