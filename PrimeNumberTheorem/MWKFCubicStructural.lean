import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

open scoped ArithmeticFunction BigOperators

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Exact finite structure in the cubic MWKF reduction

These lemmas formalize the finite gcd extraction, shifted equation, and
Mobius level recombination used before any analytic estimate is applied.
-/

/-- Scaling two residual moduli by a positive common gcd gives gcd exactly
`q` precisely when the residual moduli are coprime. -/
theorem gcd_scaled_eq_iff_coprime
    {q r s : ℕ} (hq : 0 < q) :
    Nat.gcd (q * r) (q * s) = q ↔ Nat.Coprime r s := by
  rw [Nat.gcd_mul_left]
  constructor
  · intro h
    have hmul : q * Nat.gcd r s = q * 1 := by simpa using h
    exact Nat.mul_left_cancel hq hmul
  · intro h
    rw [h.gcd_eq_one, mul_one]

/-- Exact extraction of the common gcd from a nonzero pair. -/
theorem gcd_extraction
    {d e : ℕ} (hq : Nat.gcd d e ≠ 0) :
    d = Nat.gcd d e * (d / Nat.gcd d e) ∧
    e = Nat.gcd d e * (e / Nat.gcd d e) ∧
    Nat.Coprime (d / Nat.gcd d e) (e / Nat.gcd d e) := by
  have hdvdD : Nat.gcd d e ∣ d := Nat.gcd_dvd_left d e
  have hdvdE : Nat.gcd d e ∣ e := Nat.gcd_dvd_right d e
  refine ⟨?_, ?_, Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero hq)⟩
  · simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdvdD).symm
  · simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdvdE).symm

/-- With the natural support condition, the additive shifted equation and
the complementary-divisor equation are literally equivalent. -/
theorem shifted_eq_complementary_divisor
    {m A k l r n c : ℕ} (hm : m ≤ r * n * c) :
    m + A * k * l = r * n * c ↔
      A * k * l = r * n * c - m := by
  omega

/-- Exact finite reindexing by the first active tail/shell label.  Every
original tuple occurs in exactly one fiber, so no tail contribution is spent
twice in the global cancellation ledger. -/
theorem sum_partition_by_shell
    {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M]
    (s : Finset ι) (shell : ι → κ) (f : ι → M) :
    ∑ i ∈ s, f i =
      ∑ k ∈ s.image shell, ∑ i ∈ s.filter (fun i ↦ shell i = k), f i := by
  classical
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image shell) (g := shell) (f := f)
    (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- The finite level coefficient `mu * mu`, summed over divisors, recombines
exactly to `mu`.  This is the geometric identity
`((mu * mu) * 1)(n) = mu(n)`; it is not a newform projector statement. -/
theorem sum_moebius_convolution_divisors (n : ℕ) :
    ∑ d ∈ n.divisors,
      ((ArithmeticFunction.moebius * ArithmeticFunction.moebius) d : ℤ) =
        ArithmeticFunction.moebius n := by
  let μ : ArithmeticFunction ℤ := ArithmeticFunction.moebius
  have hinv : μ * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) = 1 :=
    ArithmeticFunction.moebius_mul_coe_zeta
  have hfun :
      (μ * μ) * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) = μ := by
    rw [mul_assoc, hinv, mul_one]
  change ∑ d ∈ n.divisors, (μ * μ) d = μ n
  rw [← ArithmeticFunction.coe_mul_zeta_apply]
  exact congrArg (fun f : ArithmeticFunction ℤ ↦ f n) hfun

end MWKFCubic
end PrimeNumberTheorem
