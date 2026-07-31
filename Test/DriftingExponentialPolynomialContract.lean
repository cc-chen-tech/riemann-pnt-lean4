import MathlibAux.DriftingExponentialPolynomial

open Complex
open scoped Interval

namespace Test

#check
  (MathlibAux.driftingExponentialPolynomial :
    ∀ {ι : Type*} [DecidableEq ι],
      Finset ι → (ι → ℂ) → (ι → ℝ) → (ι → ℝ) → ℝ → ℝ → ℂ)

#check
  (MathlibAux.mergedFrequencySupport :
    ∀ {ι : Type*} [DecidableEq ι],
      Finset ι → (ι → ℝ) → Finset ℝ)

#check
  (MathlibAux.mergedFrequencyCoefficient :
    ∀ {ι : Type*} [DecidableEq ι],
      Finset ι → (ι → ℂ) → (ι → ℝ) → ℝ → ℂ)

#check
  (@MathlibAux.exponentialPolynomial_eq_mergedFrequencyPolynomial :
    ∀ {ι : Type*} [DecidableEq ι]
      (S : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ),
      MathlibAux.exponentialPolynomial S coeff freq t =
        MathlibAux.exponentialPolynomial
          (MathlibAux.mergedFrequencySupport S freq)
          (MathlibAux.mergedFrequencyCoefficient S coeff freq)
          id t)

#check
  (@MathlibAux.norm_driftingExponentialPolynomial_sub_exponentialPolynomial_le :
    ∀ {ι : Type*} [DecidableEq ι]
      {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
      {a delta t : ℝ},
      0 ≤ delta →
      a ≤ t →
      (∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0) →
      ‖MathlibAux.driftingExponentialPolynomial
          S coeff freq drift a t -
        MathlibAux.exponentialPolynomial S coeff freq t‖ ≤
        (1 - Real.exp (-delta * (t - a))) *
          ∑ i ∈ S, ‖coeff i‖)

#check
  (@MathlibAux.integral_normSq_driftingExponentialPolynomial_ge :
    ∀ {ι : Type*} [DecidableEq ι]
      {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
      {a L delta : ℝ},
      0 ≤ L →
      0 ≤ delta →
      (∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0) →
      Set.InjOn freq ↑S →
      (1 / 2 : ℝ) *
          (L * ∑ i ∈ S, ‖coeff i‖ ^ 2 -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              S coeff freq) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ i ∈ S, ‖coeff i‖) ^ 2 ≤
        ∫ t in a..(a + L),
          ‖MathlibAux.driftingExponentialPolynomial
            S coeff freq drift a t‖ ^ 2)

#check
  (@MathlibAux.integral_normSq_driftingExponentialPolynomial_pos :
    ∀ {ι : Type*} [DecidableEq ι]
      {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
      {a L delta : ℝ},
      0 ≤ L →
      0 ≤ delta →
      (∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0) →
      Set.InjOn freq ↑S →
      PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
            S coeff freq +
          2 * L * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ i ∈ S, ‖coeff i‖) ^ 2 <
        L * ∑ i ∈ S, ‖coeff i‖ ^ 2 →
      0 <
        ∫ t in a..(a + L),
          ‖MathlibAux.driftingExponentialPolynomial
            S coeff freq drift a t‖ ^ 2)

#check
  (@MathlibAux.integral_normSq_driftingExponentialPolynomial_ge_merged :
    ∀ {ι : Type*} [DecidableEq ι]
      {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
      {a L delta : ℝ},
      0 ≤ L →
      0 ≤ delta →
      (∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0) →
      (1 / 2 : ℝ) *
          (L *
              ∑ u ∈ MathlibAux.mergedFrequencySupport S freq,
                ‖MathlibAux.mergedFrequencyCoefficient
                    S coeff freq u‖ ^ 2 -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              (MathlibAux.mergedFrequencySupport S freq)
              (MathlibAux.mergedFrequencyCoefficient S coeff freq) id) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ i ∈ S, ‖coeff i‖) ^ 2 ≤
        ∫ t in a..(a + L),
          ‖MathlibAux.driftingExponentialPolynomial
            S coeff freq drift a t‖ ^ 2)

#check
  (@MathlibAux.integral_normSq_driftingExponentialPolynomial_pos_merged :
    ∀ {ι : Type*} [DecidableEq ι]
      {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
      {a L delta : ℝ},
      0 ≤ L →
      0 ≤ delta →
      (∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0) →
      PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
            (MathlibAux.mergedFrequencySupport S freq)
            (MathlibAux.mergedFrequencyCoefficient S coeff freq) id +
          2 * L * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ i ∈ S, ‖coeff i‖) ^ 2 <
        L *
          ∑ u ∈ MathlibAux.mergedFrequencySupport S freq,
            ‖MathlibAux.mergedFrequencyCoefficient
                S coeff freq u‖ ^ 2 →
      0 <
        ∫ t in a..(a + L),
          ‖MathlibAux.driftingExponentialPolynomial
            S coeff freq drift a t‖ ^ 2)

end Test
