import PrimeNumberTheorem.MWKFCubicAFEDyadicTimeIntegral

open Complex Set MeasureTheory

namespace PrimeNumberTheorem.MWKFCubic

-- Missing finite-support/time-integral proofs must not be supplied as
-- assumptions of the actual dyadic Poisson expression.
#check cubicAFEProgressionDyadicIndices
#check cubicAFEProgressionDyadicCutoff_zero_of_not_mem_indices
#check integrable_cubicAFECombinedSummandFinite
#check integral_tsum_cubicAFEDyadicProgression
#check integrable_cubicAFEDyadicPoissonTerm
#check integral_cubicAFEDyadicPoissonTerm_eq
#check cubicAFEProgressionIntegral_eq_dyadicPoisson

-- The support set retains exact progression admissibility, including a
-- positive second index, instead of merely bounding the first coordinate.
example : (⟨4, by norm_num [cubicAFEProgression, cubicAFEProgressionNumerator, Nat.gcd]⟩ :
    cubicAFEProgression 6 10 (-2)) ∈ cubicAFEProgressionDyadicIndices 6 10 (-2) 1 := by
  rw [mem_cubicAFEProgressionDyadicIndices]
  norm_num

example : (⟨9, by norm_num [cubicAFEProgression, cubicAFEProgressionNumerator, Nat.gcd]⟩ :
    cubicAFEProgression 6 10 (-2)) ∉ cubicAFEProgressionDyadicIndices 6 10 (-2) 2 := by
  rw [mem_cubicAFEProgressionDyadicIndices]
  norm_num

example : ¬ (1 ∈ cubicAFEProgression 6 10 (-8)) := by
  norm_num [cubicAFEProgression, cubicAFEProgressionNumerator, Nat.gcd]

-- Pointwise finite support, not a presumed uniform Fourier majorant.
#check (@integral_tsum_cubicAFEDyadicProgression :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, d ≠ 0 → ∀ (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ),
      (∫ t : ℝ, ∑' m : cubicAFEProgression d e δ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) =
        ∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
          (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
            cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val))

#check (@cubicAFEProgressionIntegral_eq_dyadicPoisson :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, 0 < d → ∀ (he : 0 < e) (δ : ℤ),
      (∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
        cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) =
        ∑' jk : ℕ × ℕ, ∫ t : ℝ, cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t)

end PrimeNumberTheorem.MWKFCubic
