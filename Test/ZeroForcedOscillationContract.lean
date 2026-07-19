import PrimeNumberTheorem.ZeroForcedOscillation

open Complex Set
open scoped ComplexConjugate

open PrimeNumberTheorem.ZeroForcedOscillation

example (ρ : ℂ) (β y : ℝ) (hρ : ρ.re = β) :
    ((Real.exp y : ℝ) : ℂ) ^ ρ =
      ((Real.exp (β * y) : ℝ) : ℂ) * exp (I * (ρ.im * y)) :=
  realExp_cpow_eq_growth_mul_oscillation ρ β y hρ

example (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β y : ℝ)
    (hre : ∀ ρ ∈ S, ρ.re = β) :
    (∑ ρ ∈ S,
        (multiplicity ρ : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ) =
      ((Real.exp (β * y) : ℝ) : ℂ) *
        multiplicityWeightedExponentialPolynomial S multiplicity
          (fun ρ => ρ⁻¹) Complex.im y :=
  equalRealPart_zeroPackage_eq_exponentialPolynomial S multiplicity β y hre

example {c d : ℂ} {u v a b : ℝ} (huv : u ≠ v) :
    (∫ t in a..b,
        conj (c * exp (I * (u * t))) * (d * exp (I * (v * t)))) =
      conj c * d *
        ((exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)) /
          (I * (v - u))) :=
  intervalIntegral_offDiagonal_eq c d huv

example {c d : ℂ} {u v a b : ℝ} (huv : u ≠ v) :
    ‖∫ t in a..b,
        conj (c * exp (I * (u * t))) * (d * exp (I * (v * t)))‖ ≤
      2 * ‖c‖ * ‖d‖ / |v - u| :=
  norm_intervalIntegral_offDiagonal_le c d huv

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) {a b : ℝ} (hω : Set.InjOn ω ↑S) :
    |(∫ t in a..b, ‖exponentialPolynomial S c ω t‖ ^ 2) -
        (b - a) * ∑ i ∈ S, ‖c i‖ ^ 2| ≤
      offDiagonalBound S c ω :=
  abs_intervalIntegral_sqNorm_exponentialPolynomial_sub_diagonal_le S c ω hω

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) {a b : ℝ} (hab : a < b)
    (hω : Set.InjOn ω ↑S) :
    ∃ t ∈ Set.Ioo a b,
      (∑ i ∈ S, ‖c i‖ ^ 2) - offDiagonalBound S c ω / (b - a) ≤
        ‖exponentialPolynomial S c ω t‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_exponentialPolynomial_ge S c ω hab hω

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (multiplicity : ι → ℕ) (c : ι → ℂ) (ω : ι → ℝ)
    {a b : ℝ} (hω : Set.InjOn ω ↑S) :
    |(∫ t in a..b,
          ‖multiplicityWeightedExponentialPolynomial S multiplicity c ω t‖ ^ 2) -
        (b - a) * ∑ i ∈ S, ‖(multiplicity i : ℂ) * c i‖ ^ 2| ≤
      offDiagonalBound S (fun i => (multiplicity i : ℂ) * c i) ω :=
  abs_intervalIntegral_sqNorm_multiplicityWeightedExponentialPolynomial_sub_diagonal_le
    S multiplicity c ω hω

example (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β : ℝ)
    {a b : ℝ} (hab : a < b) (hre : ∀ ρ ∈ S, ρ.re = β) :
    ∃ y ∈ Set.Ioo a b,
      Real.exp (β * y) ^ 2 *
          ((∑ ρ ∈ S, ‖(multiplicity ρ : ℂ) * ρ⁻¹‖ ^ 2) -
            offDiagonalBound S
                (fun ρ => (multiplicity ρ : ℂ) * ρ⁻¹) Complex.im /
              (b - a)) ≤
        ‖∑ ρ ∈ S,
            (multiplicity ρ : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_equalRealPart_zeroPackage_ge
    S multiplicity β hab hre
