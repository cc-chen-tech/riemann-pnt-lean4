import PrimeNumberTheorem.MWKFCubicStructural

open scoped ArithmeticFunction BigOperators

namespace PrimeNumberTheorem.MWKFCubic

#check (@gcd_scaled_eq_iff_coprime :
  ∀ {q r s : ℕ}, 0 < q →
    (Nat.gcd (q * r) (q * s) = q ↔ Nat.Coprime r s))

#check (@gcd_extraction :
  ∀ {d e : ℕ}, Nat.gcd d e ≠ 0 →
    d = Nat.gcd d e * (d / Nat.gcd d e) ∧
    e = Nat.gcd d e * (e / Nat.gcd d e) ∧
    Nat.Coprime (d / Nat.gcd d e) (e / Nat.gcd d e))

#check (@coprime_diagonal_parameterization :
  ∀ {m n r s : ℕ}, 0 < r → Nat.Coprime r s →
    (m * s = n * r ↔ ∃ l : ℕ, m = l * r ∧ n = l * s))

#check (@diagonal_eq_iff_exists_scale :
  ∀ {d e m n : ℕ}, 0 < d → 0 < e →
    (m * e = n * d ↔
      ∃ l : ℕ,
        m = l * (d / Nat.gcd d e) ∧
        n = l * (e / Nat.gcd d e)))

#check (@shifted_eq_complementary_divisor :
  ∀ {m A k l r n c : ℕ},
    m ≤ r * n * c →
    (m + A * k * l = r * n * c ↔ A * k * l = r * n * c - m))

#check (@sum_partition_by_shell :
  ∀ {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M]
    (s : Finset ι) (shell : ι → κ) (f : ι → M),
    ∑ i ∈ s, f i =
      ∑ k ∈ s.image shell, ∑ i ∈ s.filter (fun i ↦ shell i = k), f i)

#check (@sum_moebius_convolution_divisors :
  ∀ n : ℕ,
    ∑ d ∈ n.divisors,
      ((ArithmeticFunction.moebius * ArithmeticFunction.moebius) d : ℤ) =
        ArithmeticFunction.moebius n)

end PrimeNumberTheorem.MWKFCubic
