import PrimeNumberTheorem.ZeroDensityLayerBudgetAntiCancellation

namespace PrimeNumberTheorem

open ZeroForcedOscillation

example :
    (10 : ℝ) - 3 - 2 ≤ ‖((5 : ℝ) : ℂ)‖ := by
  have h := norm_error_ge_main_sub_complement_remainder
    (((5 : ℝ) : ℂ))
    (((10 : ℝ) : ℂ))
    (((-3 : ℝ) : ℂ))
    (((-2 : ℝ) : ℂ))
    (by norm_num)
  norm_num at h ⊢

example
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β L X : ℝ)
    (hL : 0 < L) (hre : ∀ ρ ∈ S, ρ.re = β) :
    ∃ y ∈ Set.Ioo X (X + L),
      Real.exp (β * y) ^ 2 *
          ((∑ ρ ∈ S, ‖(multiplicity ρ : ℂ) * ρ⁻¹‖ ^ 2) -
            offDiagonalBound S
                (fun ρ => (multiplicity ρ : ℂ) * ρ⁻¹) Complex.im / L) ≤
        ‖∑ ρ ∈ S,
            (multiplicity ρ : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ‖ ^ 2 :=
  exists_far_sqNorm_equalRealPart_zeroPackage_ge
    S multiplicity β L hL hre X

example
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β L X : ℝ)
    (hL : 0 < L) (hre : ∀ ρ ∈ S, ρ.re = β) :
    ∃ y ∈ Set.Ioo X (X + L),
      Real.sqrt
          (Real.exp (β * y) ^ 2 *
            ((∑ ρ ∈ S, ‖(multiplicity ρ : ℂ) * ρ⁻¹‖ ^ 2) -
              offDiagonalBound S
                  (fun ρ => (multiplicity ρ : ℂ) * ρ⁻¹) Complex.im / L)) ≤
        ‖∑ ρ ∈ S,
            (multiplicity ρ : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ‖ :=
  exists_far_norm_equalRealPart_zeroPackage_ge
    S multiplicity β L hL hre X

end PrimeNumberTheorem
