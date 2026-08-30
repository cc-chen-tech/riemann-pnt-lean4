import PrimeNumberTheorem.MWKFCubicAFEPhysicalPoisson
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Complex Set
open scoped ContDiff FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

#check CubicProgressionCutoff
#check cubicAFEProgressionCutoffSummand
#check contDiff_cubicAFEProgressionCutoffSummand
#check cubicAFEProgressionSchwartz
#check cubicAFEProgressionCutoff_poisson
#check cubicAFEProgressionCutoff_poisson_inverseResidue

-- An explicit nonzero cutoff whose CLOSED support avoids both singular
-- boundaries. This catches an accidentally vacuous cutoff specification.
theorem cubicProgressionCutoff_exists_value_one :
    ∃ χ : CubicProgressionCutoff 6 10 (-1), χ 2 = 1 := by
  let f : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hs : tsupport (f : ℝ → ℝ) ⊆ cubicAFEProgressionDomain 6 10 (-1) := by
    rw [f.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    dsimp [f] at hx
    norm_num [cubicAFEProgressionDomain, Nat.gcd]
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨⟨f, f.contDiff, f.hasCompactSupport, hs⟩, ?_⟩
  exact f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)

#print axioms cubicProgressionCutoff_exists_value_one

-- Fixed-parameter Poisson must retain the exact Jacobian and phase. No
-- assumed smoothness, summability, or Schwartz property of the kernel.
#check (@cubicAFEProgressionCutoff_poisson :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < d → 0 < e →
    ∀ {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ), 1 / 2 < X →
      ∀ {s : ℝ}, 0 < s → ∀ a : ℝ,
        (∑' n : ℤ, cubicAFEProgressionCutoffSummand W T X V χ t (a + s * n)) =
          (s⁻¹ : ℂ) * ∑' h : ℤ,
            𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t) ((h : ℝ) / s) *
              Complex.exp (2 * (Real.pi : ℂ) * I * (h : ℂ) * (a : ℂ) / (s : ℂ)))

-- The actual inverse residue must give the MINUS sign and the reduced
-- modulus, with no hypothesis that delta is a unit modulo that modulus.
#check (@cubicAFEProgressionCutoff_poisson_inverseResidue :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < d → 0 < e →
    ∀ {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ), 1 / 2 < X →
      (∑' n : ℤ, cubicAFEProgressionCutoffSummand W T X V χ t
        (-(δ : ℝ) * (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℝ) +
          ((e / Nat.gcd d e : ℕ) : ℝ) * n)) =
        (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
          𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t)
            ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ)) *
            Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
              (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
                ((e / Nat.gcd d e : ℕ) : ℂ)))

end PrimeNumberTheorem.MWKFCubic
