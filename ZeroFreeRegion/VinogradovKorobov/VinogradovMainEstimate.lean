import ZeroFreeRegion.VinogradovKorobov.VinogradovCongruence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The total weight `1 + ... + k` of the degree-`k` Vinogradov system. -/
def vinogradovCriticalWeight (k : ℕ) : ℕ := k * (k + 1) / 2

/-- A quantitative Vinogradov mean-value estimate with the standard two main
terms and an `X^ε` loss.  The constant `C` is uniform in `X`. -/
def VinogradovMeanValueEstimate (k s : ℕ) (ε C : ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ C ∧
    ∀ X : ℕ, 1 ≤ X →
      (vinogradovSolutionCountNat k s X : ℝ) ≤
        C * Real.rpow (X : ℝ) ε *
          ((X : ℝ) ^ s +
            (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k))

/-- The elementary diagonal argument proves the standard mean-value shape in
the range `s ≤ k`, with no `X^ε` loss and constant `s!`. -/
theorem vinogradovMeanValueEstimate_diagonal (k s : ℕ) (hsk : s ≤ k) :
    VinogradovMeanValueEstimate k s 0 s.factorial := by
  refine ⟨le_rfl, by positivity, ?_⟩
  intro X hX
  have hcount := vinogradovSolutionCountNat_le_diagonal k s X hsk
  have hcountR :
      (vinogradovSolutionCountNat k s X : ℝ) ≤
        (s.factorial : ℝ) * (X : ℝ) ^ s := by
    exact_mod_cast hcount
  calc
    (vinogradovSolutionCountNat k s X : ℝ) ≤
        (s.factorial : ℝ) * (X : ℝ) ^ s := hcountR
    _ ≤ (s.factorial : ℝ) * Real.rpow (X : ℝ) 0 *
          ((X : ℝ) ^ s +
            (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k)) := by
      have hrpow : Real.rpow (X : ℝ) 0 = 1 := Real.rpow_zero _
      rw [hrpow, mul_one, mul_add]
      exact le_add_of_nonneg_right (by positivity)

/-- Any verified mean-value estimate transfers directly to the normalized
finite Weyl moment once the finite modulus is large enough to avoid
wraparound. -/
theorem norm_normalizedVinogradovMomentMod_le_of_meanValueEstimate
    (Q k s X : ℕ) [NeZero Q] {ε C : ℝ}
    (hest : VinogradovMeanValueEstimate k s ε C)
    (hX : 1 ≤ X) (hQ : s * X ^ k < Q) :
    ‖normalizedVinogradovMomentMod Q k s X‖ ≤
      C * Real.rpow (X : ℝ) ε *
        ((X : ℝ) ^ s +
          (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k)) := by
  rw [normalizedVinogradovMomentMod_eq_natCount_of_topScale
    Q k s X hX hQ]
  simpa only [Complex.norm_natCast] using hest.2.2 X hX

end

end ZeroFreeRegion.VinogradovKorobov
