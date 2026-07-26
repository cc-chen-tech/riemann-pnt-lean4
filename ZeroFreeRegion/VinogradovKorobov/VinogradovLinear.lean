import ZeroFreeRegion.VinogradovKorobov.VinogradovMomentMonotonicity

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

@[simp] theorem vinogradovCriticalWeight_one :
    vinogradovCriticalWeight 1 = 1 := by
  simp [vinogradovCriticalWeight]

/-- The standard Vinogradov mean-value estimate is fully proved in degree
one, for every moment, with no epsilon loss and constant one. -/
theorem vinogradovMeanValueEstimate_linear (s : ℕ) :
    VinogradovMeanValueEstimate 1 s 0 1 := by
  refine ⟨le_rfl, by norm_num, ?_⟩
  intro X hX
  simp only [one_mul, vinogradovCriticalWeight_one]
  cases s with
  | zero =>
      have hcount := vinogradovSolutionCountNat_le_total 1 0 X
      have hcountR :
          (vinogradovSolutionCountNat 1 0 X : ℝ) ≤ 1 := by
        have hcountR' :
            (vinogradovSolutionCountNat 1 0 X : ℝ) ≤ (X : ℝ) ^ 0 := by
          exact_mod_cast hcount
        simpa using hcountR'
      simpa using hcountR.trans (show (1 : ℝ) ≤ 1 + 1 by norm_num)
  | succ n =>
      have hcount := vinogradovSolutionCountNat_le_firstPower 1 n X (by norm_num)
      have hcountR :
          (vinogradovSolutionCountNat 1 (n + 1) X : ℝ) ≤
            (X : ℝ) ^ (2 * n + 1) := by
        exact_mod_cast hcount
      have hexp : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
      rw [hexp]
      have hnonneg : 0 ≤ (X : ℝ) ^ (n + 1) := by positivity
      have hadd :
          (X : ℝ) ^ (2 * n + 1) ≤
            (X : ℝ) ^ (n + 1) + (X : ℝ) ^ (2 * n + 1) := by
        linarith
      simpa [Real.rpow_def] using hcountR.trans hadd

end

end ZeroFreeRegion.VinogradovKorobov
