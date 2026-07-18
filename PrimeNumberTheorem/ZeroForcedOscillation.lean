import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Complex Set
open scoped ComplexConjugate Interval

namespace PrimeNumberTheorem.ZeroForcedOscillation

noncomputable section

/-- A finite complex exponential polynomial with coefficients and real
frequencies kept as independent data. -/
def exponentialPolynomial {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, c i * Complex.exp (Complex.I * (ω i * t))

/-- The ordered off-diagonal budget. Each unordered pair occurs twice. -/
def offDiagonalBound {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (ω : ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i,
    2 * ‖c i‖ * ‖c j‖ / |ω j - ω i|

/-- Multiplicity is an explicit natural-number factor in each coefficient;
the supporting finset records distinct frequencies, not analytic order. -/
def multiplicityWeightedExponentialPolynomial {ι : Type*} (S : Finset ι)
    (multiplicity : ι → ℕ) (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  exponentialPolynomial S (fun i => (multiplicity i : ℂ) * c i) ω t

private lemma offDiagonal_integrand_eq
    (c d : ℂ) (u v t : ℝ) :
    conj (c * exp (I * (u * t))) * (d * exp (I * (v * t))) =
      conj c * d * exp ((I * (v - u)) * t) := by
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, conj_I, conj_ofReal, neg_mul]
  calc
    conj c * exp (-(I * (u * t))) * (d * exp (I * (v * t))) =
        conj c * d * (exp (-(I * (u * t))) * exp (I * (v * t))) := by ring
    _ = conj c * d * exp (-(I * (u * t)) + I * (v * t)) := by
      rw [exp_add]
    _ = conj c * d * exp ((I * (v - u)) * t) := by
      congr 2
      ring

/-- Exact integral of one ordered off-diagonal product. -/
theorem intervalIntegral_offDiagonal_eq
    (c d : ℂ) {u v a b : ℝ} (huv : u ≠ v) :
    (∫ t in a..b,
        conj (c * exp (I * (u * t))) * (d * exp (I * (v * t)))) =
      conj c * d *
        ((exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)) /
          (I * (v - u))) := by
  simp_rw [offDiagonal_integrand_eq]
  calc
    (∫ t in a..b, conj c * d * exp ((I * (v - u)) * t)) =
        conj c * d * (∫ t in a..b, exp ((I * (v - u)) * t)) := by
      exact intervalIntegral.integral_const_mul
        (a := a) (b := b) (conj c * d)
          (fun t : ℝ => exp ((I * (v - u)) * t))
    _ = conj c * d *
        ((exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)) /
          (I * (v - u))) := by
      rw [integral_exp_mul_complex]
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact huv (by linarith)

/-- An ordered off-diagonal pair contributes at most
`2 * ‖c‖ * ‖d‖ / |v-u|`, independently of the interval length. -/
theorem norm_intervalIntegral_offDiagonal_le
    (c d : ℂ) {u v a b : ℝ} (huv : u ≠ v) :
    ‖∫ t in a..b,
        conj (c * exp (I * (u * t))) * (d * exp (I * (v * t)))‖ ≤
      2 * ‖c‖ * ‖d‖ / |v - u| := by
  rw [intervalIntegral_offDiagonal_eq c d huv]
  rw [norm_mul, norm_mul, norm_conj, norm_div]
  have hnum :
      ‖exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)‖ ≤ 2 := by
    calc
      ‖exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)‖ ≤
          ‖exp ((I * (v - u)) * b)‖ + ‖exp ((I * (v - u)) * a)‖ :=
        norm_sub_le _ _
      _ = 2 := by norm_num [norm_exp]
  have hden : ‖I * ((v : ℂ) - (u : ℂ))‖ = |v - u| := by
    calc
      ‖I * ((v : ℂ) - (u : ℂ))‖ =
          ‖I‖ * ‖(v : ℂ) - (u : ℂ)‖ := norm_mul _ _
      _ = ‖((v - u : ℝ) : ℂ)‖ := by simp
      _ = |v - u| := by rw [norm_real, Real.norm_eq_abs]
  rw [hden]
  have hpos : 0 < |v - u| := abs_pos.mpr (sub_ne_zero.mpr huv.symm)
  calc
    ‖c‖ * ‖d‖ *
          (‖exp ((I * (v - u)) * b) - exp ((I * (v - u)) * a)‖ / |v - u|) ≤
        ‖c‖ * ‖d‖ * (2 / |v - u|) := by
      gcongr
    _ = 2 * ‖c‖ * ‖d‖ / |v - u| := by ring

end

end PrimeNumberTheorem.ZeroForcedOscillation
