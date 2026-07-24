import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound

open Complex Set
open scoped BigOperators

open PrimeNumberTheorem
open PrimeNumberTheorem.ZeroForcedOscillation

example (T : ℝ) (hT : nontrivialZerosFinset T = ∅) :
    maximalZeroRealPart T = 0 :=
  maximalZeroRealPart_eq_zero_of_empty T hT

example {ρ : ℂ} {T : ℝ} (hρ : ρ ∈ nontrivialZerosFinset T) :
    ρ.re ≤ maximalZeroRealPart T :=
  re_le_maximalZeroRealPart hρ

example {ρ : ℂ} {T : ℝ} :
    ρ ∈ maximalRealPartZeroPackage T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧
        |ρ.im| ≤ T ∧ ρ.re = maximalZeroRealPart T :=
  mem_maximalRealPartZeroPackage

example (T : ℝ) (hT : (nontrivialZerosFinset T).Nonempty) :
    (maximalRealPartZeroPackage T).Nonempty :=
  maximalRealPartZeroPackage_nonempty T hT

example (T : ℝ) :
    0 < maximalComplementaryRealPartGap T :=
  maximalComplementaryRealPartGap_pos T

example {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T)) :
    ρ.re ≤ maximalZeroRealPart T - maximalComplementaryRealPartGap T :=
  re_le_maximalZeroRealPart_sub_gap hρ

example (T : ℝ) :
    complementaryZeroPackage T (maximalZeroRealPart T) = ∅ ∨
      (0 < maximalComplementaryRealPartGap T ∧
        ∀ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
          ρ.re ≤ maximalZeroRealPart T - maximalComplementaryRealPartGap T) :=
  complementaryZeroPackage_maximal_eq_empty_or_pos_gap T

example {ρ : ℂ} {T β : ℝ} :
    ρ ∈ complementaryZeroPackage T β ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T ∧ ρ.re ≠ β :=
  mem_complementaryZeroPackage

example (x : ℝ) (hx : 0 < x) (ρ : ℂ) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ ρ / ρ‖ = (m : ℝ) * x ^ ρ.re / ‖ρ‖ :=
  norm_natCast_mul_cpow_div x hx ρ m

example (T β B y : ℝ) (hy : 0 ≤ y)
    (hdom : ∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ B) :
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
      Real.exp (B * y) *
        ∑ ρ ∈ complementaryZeroPackage T β,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  norm_complementaryZeroPackageContribution_le_exp_mul_sum_of_re_le
    T β B y hy hdom

example (T β y : ℝ) (hy : 0 ≤ y)
    (hdom : ∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ β) :
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
      Real.exp (β * y) *
        ∑ ρ ∈ complementaryZeroPackage T β,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  norm_complementaryZeroPackageContribution_le_exp_mul_sum T β y hy hdom

example (T β δ y : ℝ) (hy : 0 ≤ y)
    (hgap : ∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ β - δ) :
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
      Real.exp ((β - δ) * y) *
        ∑ ρ ∈ complementaryZeroPackage T β,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum T β δ y hy hgap

example (T β : ℝ) :
    0 ≤ ∑ ρ ∈ complementaryZeroPackage T β,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  sum_complementary_multiplicity_div_norm_nonneg T β

example (T β : ℝ) :
    ∑ ρ ∈ complementaryZeroPackage T β,
        (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  sum_complementary_multiplicity_div_norm_le_sum_nontrivialZerosFinset T β

example (T β δ y : ℝ) (hy : 0 ≤ y)
    (hgap : ∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ β - δ) :
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
      Real.exp ((β - δ) * y) *
        ∑ ρ ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum_nontrivialZerosFinset
    T β δ y hy hgap

example (T y : ℝ) (hy : 0 ≤ y) :
    ‖complementaryZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ≤
      Real.exp ((maximalZeroRealPart T -
          maximalComplementaryRealPartGap T) * y) *
        ∑ ρ ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  norm_complementaryZeroPackageContribution_le_exp_maximal_gap_mul_sum_nontrivialZerosFinset
    T y hy

example (y : ℝ) (hy : 0 ≤ y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ≤
        Real.exp ((maximalZeroRealPart T -
            maximalComplementaryRealPartGap T) * y) *
          (C * (1 + Real.log (T + 6)) ^ 2) :=
  exists_norm_complementaryZeroPackageContribution_le_exp_maximal_gap_mul_log_sq
    y hy

-- Small sanity checks: the per-term identity at zero multiplicity and at `ρ = 0`.

example (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    ‖((0 : ℕ) : ℂ) * (x : ℂ) ^ ρ / ρ‖ = 0 := by
  rw [norm_natCast_mul_cpow_div x hx ρ 0]
  simp

example (x : ℝ) (hx : 0 < x) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ (0 : ℂ) / (0 : ℂ)‖ = 0 := by
  rw [norm_natCast_mul_cpow_div x hx 0 m]
  simp
