import PrimeNumberTheorem.ZeroForcedOscillation

open Complex Set
open scoped ComplexConjugate

open PrimeNumberTheorem.ZeroForcedOscillation

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
