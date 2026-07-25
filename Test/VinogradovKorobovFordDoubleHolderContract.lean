import ZeroFreeRegion.VinogradovKorobov.FordDoubleHolder

open scoped BigOperators NNReal

open ZeroFreeRegion.VinogradovKorobov

#check NNReal.pow_two_mul_sum_le_mass_mul_sq_mul_moment
#check nnnorm_sum_natCast_mul_pow_le_fordDoubleHolder

example {ι : Type*} (S : Finset ι) (mass value : ι → ℝ≥0)
    (s : ℕ) (hs : 1 ≤ s) :
    (∑ i ∈ S, mass i * value i) ^ (2 * s) ≤
      (∑ i ∈ S, mass i) ^ (2 * (s - 1)) *
        (∑ i ∈ S, mass i ^ 2) *
          ∑ i ∈ S, value i ^ (2 * s) :=
  NNReal.pow_two_mul_sum_le_mass_mul_sq_mul_moment
    S mass value s hs

example {ι : Type*} (S : Finset ι) (multiplicity : ι → ℕ)
    (value : ι → ℂ) (s : ℕ) (hs : 1 ≤ s) :
    ‖∑ i ∈ S, (multiplicity i : ℂ) * value i‖₊ ^ (2 * s) ≤
      (∑ i ∈ S, (multiplicity i : ℝ≥0)) ^ (2 * (s - 1)) *
        (∑ i ∈ S, (multiplicity i : ℝ≥0) ^ 2) *
          ∑ i ∈ S, ‖value i‖₊ ^ (2 * s) :=
  nnnorm_sum_natCast_mul_pow_le_fordDoubleHolder
    S multiplicity value s hs
