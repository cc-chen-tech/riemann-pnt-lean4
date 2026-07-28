import MathlibAux.DriftingExponentialPolynomialHilbert

open Complex MeasureTheory Set
open scoped BigOperators Interval

#check @MathlibAux.exponentialPolynomialLocalSeparationEnergy
#check @MathlibAux.abs_intervalIntegral_normSq_exponentialPolynomial_sub_diagonal_le_localSeparation
#check @MathlibAux.integral_normSq_driftingExponentialPolynomial_ge_merged_localSeparation

example
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (hfreq : Set.InjOn freq (S : Set ι)) :
    |(∫ t in a..b,
          ‖MathlibAux.exponentialPolynomial S coeff freq t‖ ^ 2) -
        (b - a) * ∑ i ∈ S, ‖coeff i‖ ^ 2| ≤
      4 * Real.pi *
        MathlibAux.exponentialPolynomialLocalSeparationEnergy
          S coeff freq :=
  MathlibAux.abs_intervalIntegral_normSq_exponentialPolynomial_sub_diagonal_le_localSeparation
    hS hfreq

example
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
    {a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hdrift : ∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0)
    (hsupport : (MathlibAux.mergedFrequencySupport S freq).Nontrivial) :
    (1 / 2 : ℝ) *
          (L *
              ∑ u ∈ MathlibAux.mergedFrequencySupport S freq,
                ‖MathlibAux.mergedFrequencyCoefficient S coeff freq u‖ ^ 2 -
            4 * Real.pi *
              MathlibAux.exponentialPolynomialLocalSeparationEnergy
                (MathlibAux.mergedFrequencySupport S freq)
                (MathlibAux.mergedFrequencyCoefficient S coeff freq) id) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ i ∈ S, ‖coeff i‖) ^ 2 ≤
      ∫ t in a..(a + L),
        ‖MathlibAux.driftingExponentialPolynomial
          S coeff freq drift a t‖ ^ 2 :=
  MathlibAux.integral_normSq_driftingExponentialPolynomial_ge_merged_localSeparation
    hL hdelta hdrift hsupport
