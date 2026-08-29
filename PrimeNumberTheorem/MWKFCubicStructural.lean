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

/-- On coprime residual moduli, the multiplicative diagonal has one and only
one common scale.  The positivity of `r` is exactly what permits cancellation
after Euclid's lemma extracts `r ∣ m`. -/
theorem coprime_diagonal_parameterization
    {m n r s : ℕ} (hr : 0 < r) (hrs : Nat.Coprime r s) :
    m * s = n * r ↔ ∃ l : ℕ, m = l * r ∧ n = l * s := by
  constructor
  · intro h
    have hr_dvd_ms : r ∣ m * s := by
      refine ⟨n, ?_⟩
      simpa [Nat.mul_comm] using h
    have hr_dvd_m : r ∣ m := (hrs.dvd_mul_right).mp hr_dvd_ms
    obtain ⟨l, hl⟩ := hr_dvd_m
    have hcancel : r * (l * s) = r * n := by
      calc
        r * (l * s) = (r * l) * s := by ac_rfl
        _ = m * s := by rw [hl]
        _ = n * r := h
        _ = r * n := by ac_rfl
    have hls : l * s = n := Nat.mul_left_cancel hr hcancel
    exact ⟨l, by simpa [Nat.mul_comm] using hl, hls.symm⟩
  · rintro ⟨l, rfl, rfl⟩
    ac_rfl

/-- After extracting `q=gcd(d,e)`, the original diagonal `m e = n d` is
exactly the coprime ray `m=l(d/q)`, `n=l(e/q)`. -/
theorem diagonal_eq_iff_exists_scale
    {d e m n : ℕ} (hd : 0 < d) (_he : 0 < e) :
    m * e = n * d ↔
      ∃ l : ℕ,
        m = l * (d / Nat.gcd d e) ∧
        n = l * (e / Nat.gcd d e) := by
  let q := Nat.gcd d e
  let r := d / q
  let s := e / q
  have hq : 0 < q := Nat.gcd_pos_of_pos_left e hd
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  obtain ⟨hdq, heq, hrs⟩ := gcd_extraction (d := d) (e := e) hq0
  have hdqr : d = q * r := by simpa [q, r] using hdq
  have heqs : e = q * s := by simpa [q, s] using heq
  have hrs' : Nat.Coprime r s := by simpa [q, r, s] using hrs
  have hr : 0 < r := by
    rw [Nat.pos_iff_ne_zero]
    intro hr0
    rw [hr0, mul_zero] at hdqr
    omega
  have hscaled : m * e = n * d ↔ m * s = n * r := by
    constructor
    · intro h
      apply Nat.mul_left_cancel hq
      calc
        q * (m * s) = m * (q * s) := by ac_rfl
        _ = m * e := by rw [← heqs]
        _ = n * d := h
        _ = n * (q * r) := by rw [hdqr]
        _ = q * (n * r) := by ac_rfl
    · intro h
      calc
        m * e = m * (q * s) := by rw [heqs]
        _ = q * (m * s) := by ac_rfl
        _ = q * (n * r) := by rw [h]
        _ = n * (q * r) := by ac_rfl
        _ = n * d := by rw [← hdqr]
  rw [hscaled]
  exact coprime_diagonal_parameterization hr hrs'

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
