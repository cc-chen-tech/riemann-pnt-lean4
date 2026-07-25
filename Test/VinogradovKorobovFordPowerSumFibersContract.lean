import ZeroFreeRegion.VinogradovKorobov.FordPowerSumFibers

open scoped BigOperators NNReal

open ZeroFreeRegion.VinogradovKorobov

#check vinogradovPowerSumVectorNat
#check vinogradovPowerSumVectorSupport
#check vinogradovPowerSumMultiplicity
#check isVinogradovSolutionNat_iff_powerSumVector_eq
#check sum_vinogradovPowerSumMultiplicity_eq
#check sum_sq_vinogradovPowerSumMultiplicity_eq_solutionCountNat
#check nnnorm_fordPowerSumWeightedAmplitude_pow_le

example (k r X : ℕ) :
    ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
      vinogradovPowerSumMultiplicity k r X c = X ^ r :=
  sum_vinogradovPowerSumMultiplicity_eq k r X

example (k r X : ℕ) :
    ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
      vinogradovPowerSumMultiplicity k r X c ^ 2 =
        vinogradovSolutionCountNat k r X :=
  sum_sq_vinogradovPowerSumMultiplicity_eq_solutionCountNat k r X

example (k r s X : ℕ) (hs : 1 ≤ s)
    (amplitude : (Fin k → ℕ) → ℂ) :
    ‖∑ c ∈ vinogradovPowerSumVectorSupport k r X,
        (vinogradovPowerSumMultiplicity k r X c : ℂ) * amplitude c‖₊ ^
          (2 * s) ≤
      (X ^ r : ℝ≥0) ^ (2 * (s - 1)) *
        (vinogradovSolutionCountNat k r X : ℝ≥0) *
          ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
            ‖amplitude c‖₊ ^ (2 * s) :=
  nnnorm_fordPowerSumWeightedAmplitude_pow_le k r s X hs amplitude
