import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamic
import PrimeNumberTheorem.ZeroForcedOscillation

open scoped BigOperators

namespace PrimeNumberTheorem

open ZeroForcedOscillation

/--
An equal-real-part finite zero cluster has a mean-square witness after every
starting scale `X`, on every interval of fixed positive logarithmic length.

This is the precise unsigned anti-cancellation statement: the package cannot
remain below its diagonal-minus-off-diagonal amplitude on all large scales.
-/
theorem exists_far_sqNorm_equalRealPart_zeroPackage_ge
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β L : ℝ)
    (hL : 0 < L) (hre : ∀ ρ ∈ S, ρ.re = β) (X : ℝ) :
    ∃ y ∈ Set.Ioo X (X + L),
      Real.exp (β * y) ^ 2 *
          ((∑ ρ ∈ S, ‖(multiplicity ρ : ℂ) * ρ⁻¹‖ ^ 2) -
            offDiagonalBound S
                (fun ρ => (multiplicity ρ : ℂ) * ρ⁻¹) Complex.im / L) ≤
        ‖∑ ρ ∈ S,
            (multiplicity ρ : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ‖ ^ 2 := by
  have hinterval : X < X + L := by linarith
  rcases exists_mem_Ioo_sqNorm_equalRealPart_zeroPackage_ge
      S multiplicity β hinterval hre with
    ⟨y, hy, hpoint⟩
  refine ⟨y, hy, ?_⟩
  simpa only [add_sub_cancel_left] using hpoint

/--
Square-root form of `exists_far_sqNorm_equalRealPart_zeroPackage_ge`.

When the displayed amplitude is positive this is a nontrivial pointwise
lower bound; when it is nonpositive the statement remains valid but
degenerate, making the missing positivity input explicit.
-/
theorem exists_far_norm_equalRealPart_zeroPackage_ge
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β L : ℝ)
    (hL : 0 < L) (hre : ∀ ρ ∈ S, ρ.re = β) (X : ℝ) :
    ∃ y ∈ Set.Ioo X (X + L),
      Real.sqrt
          (Real.exp (β * y) ^ 2 *
            ((∑ ρ ∈ S, ‖(multiplicity ρ : ℂ) * ρ⁻¹‖ ^ 2) -
              offDiagonalBound S
                  (fun ρ => (multiplicity ρ : ℂ) * ρ⁻¹) Complex.im / L)) ≤
        ‖∑ ρ ∈ S,
            (multiplicity ρ : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ‖ := by
  rcases exists_far_sqNorm_equalRealPart_zeroPackage_ge
      S multiplicity β L hL hre X with
    ⟨y, hy, hpoint⟩
  refine ⟨y, hy, ?_⟩
  calc
    Real.sqrt
        (Real.exp (β * y) ^ 2 *
          ((∑ ρ ∈ S, ‖(multiplicity ρ : ℂ) * ρ⁻¹‖ ^ 2) -
            offDiagonalBound S
                (fun ρ => (multiplicity ρ : ℂ) * ρ⁻¹) Complex.im / L))
        ≤ Real.sqrt
            (‖∑ ρ ∈ S,
                (multiplicity ρ : ℂ) *
                  ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ‖ ^ 2) :=
      Real.sqrt_le_sqrt hpoint
    _ = ‖∑ ρ ∈ S,
            (multiplicity ρ : ℂ) *
              ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ‖ :=
      Real.sqrt_sq (norm_nonneg _)

/--
Abstract transfer from a dominant package to the actual error.

Concrete complementary-layer theorems plug into `complement`; no ownership
of their source module is required here.
-/
theorem norm_error_ge_main_sub_complement_remainder
    (error main complement remainder : ℂ)
    (hdecomp : error = main + complement + remainder) :
    ‖main‖ - ‖complement‖ - ‖remainder‖ ≤ ‖error‖ := by
  have hmain : main = error - (complement + remainder) := by
    rw [hdecomp]
    abel
  have hmain_norm :
      ‖main‖ ≤ ‖error‖ + ‖complement‖ + ‖remainder‖ := by
    calc
      ‖main‖ = ‖error - (complement + remainder)‖ := by rw [hmain]
      _ ≤ ‖error‖ + ‖complement + remainder‖ := norm_sub_le _ _
      _ ≤ ‖error‖ + (‖complement‖ + ‖remainder‖) := by
        gcongr
        exact norm_add_le _ _
      _ = ‖error‖ + ‖complement‖ + ‖remainder‖ := by ring
  linarith

end PrimeNumberTheorem
