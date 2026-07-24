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
    maximalRealPartZeroPackage T ⊆ nontrivialZerosFinset T :=
  maximalRealPartZeroPackage_subset_nontrivialZerosFinset T

example (T : ℝ) :
    (maximalRealPartZeroPackage T).card ≤
      (nontrivialZerosFinset T).card :=
  card_maximalRealPartZeroPackage_le_card_nontrivialZerosFinset T

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
    ((maximalRealPartZeroPackage T).card : ℝ) ≤
      C * T * (1 + Real.log (T + 6)) :=
  exists_card_maximalRealPartZeroPackage_le_mul_log

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

example (y T : ℝ) :
    ‖zeroPackageUncontrolledRemainder y T (maximalZeroRealPart T)‖ ≤
      ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ +
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ :=
  norm_zeroPackageUncontrolledRemainder_le_complementary_add_approximation y T

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T → ∀ {a b : ℝ},
    0 < a → a < b →
      ∃ y ∈ Set.Ioo a b,
        Real.exp (maximalZeroRealPart T * y) ^ 2 *
            ((∑ ρ ∈ maximalRealPartZeroPackage T,
                ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
              offDiagonalBound (maximalRealPartZeroPackage T)
                (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
                Complex.im / (b - a)) ≤
          ‖equalRealPartZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ ^ 2 ∧
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ -
            (Real.exp ((maximalZeroRealPart T -
                maximalComplementaryRealPartGap T) * y) *
              (C * (1 + Real.log (T + 6)) ^ 2) +
              ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                (chebyshevPsi0 (Real.exp y) : ℂ)‖) -
            (Real.log (2 * Real.pi) +
              (1 / 2 : ℝ) * Real.exp (-2 * y) /
                (1 - Real.exp (-2 * y))) ≤
          ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  exists_C_forall_fixedHeight_maximalZeroPackage_transfers_to_psi0_error

example (T : ℝ) :
    0 ≤ maximalZeroPackageEnergy T :=
  maximalZeroPackageEnergy_nonneg T

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    0 < maximalZeroPackageEnergy T :=
  maximalZeroPackageEnergy_pos T hpackage

example (T : ℝ) :
    0 ≤ maximalZeroPackageOffDiagonalBound T :=
  maximalZeroPackageOffDiagonalBound_nonneg T

example (T : ℝ) :
    0 ≤ maximalZeroPackageIntervalLengthThreshold T :=
  maximalZeroPackageIntervalLengthThreshold_nonneg T

example (T : ℝ) :
    maximalZeroPackageIntervalLengthThreshold T <
      maximalZeroPackageCanonicalIntervalLength T :=
  maximalZeroPackageIntervalLengthThreshold_lt_canonical T

example (T : ℝ) :
    0 < maximalZeroPackageMinimumImaginarySpacing T :=
  maximalZeroPackageMinimumImaginarySpacing_pos T

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    maximalZeroPackageIntervalLengthThreshold T ≤
      maximalZeroPackageCoefficientAwareSpacingThreshold T :=
  maximalZeroPackageIntervalLengthThreshold_le_coefficientAwareSpacingThreshold
    T hpackage

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    maximalZeroPackageCoefficientAwareSpacingThreshold T ≤
      2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
        maximalZeroPackageMinimumImaginarySpacing T :=
  maximalZeroPackageCoefficientAwareSpacingThreshold_le_card_sub_one_div_spacing
    T hpackage

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    maximalZeroPackageIntervalLengthThreshold T ≤
      2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
        maximalZeroPackageMinimumImaginarySpacing T :=
  maximalZeroPackageIntervalLengthThreshold_le_card_sub_one_div_spacing
    T hpackage

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    maximalZeroPackageCanonicalIntervalLength T ≤
      2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T + 1 :=
  maximalZeroPackageCanonicalIntervalLength_le_card_sub_one_div_spacing
    T hpackage

example : ∃ C T0 : ℝ, 0 ≤ C ∧ 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
    maximalZeroPackageCanonicalIntervalLength T ≤
      2 * (C * T * (1 + Real.log (T + 6))) /
          maximalZeroPackageMinimumImaginarySpacing T + 1 :=
  exists_C_T0_forall_maximalZeroPackageCanonicalIntervalLength_le_mul_log_div_spacing

example (T a b : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (hlength : maximalZeroPackageIntervalLengthThreshold T < b - a) :
    0 < maximalZeroPackageEnergy T -
      maximalZeroPackageOffDiagonalBound T / (b - a) :=
  maximalZeroPackageMeanSquareBracket_pos T hpackage hlength

example (T a b y : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (hlength : maximalZeroPackageIntervalLengthThreshold T < b - a) :
    0 < maximalZeroPackageMeanSquareMain T (b - a) y :=
  maximalZeroPackageMeanSquareMain_pos T y hpackage hlength

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
    (maximalRealPartZeroPackage T).Nonempty → ∀ {a b : ℝ},
      0 < a → maximalZeroPackageIntervalLengthThreshold T < b - a →
        ∃ y ∈ Set.Ioo a b,
          0 < maximalZeroPackageMeanSquareMain T (b - a) y ∧
          0 < Real.sqrt (maximalZeroPackageMeanSquareMain T (b - a) y) ∧
          Real.sqrt (maximalZeroPackageMeanSquareMain T (b - a) y) -
              (Real.exp ((maximalZeroRealPart T -
                  maximalComplementaryRealPartGap T) * y) *
                (C * (1 + Real.log (T + 6)) ^ 2) +
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖) -
              (Real.log (2 * Real.pi) +
                (1 / 2 : ℝ) * Real.exp (-2 * y) /
                  (1 - Real.exp (-2 * y))) ≤
            ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  exists_C_forall_fixedHeight_maximalZeroPackage_strict_lower_bound

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
    (maximalRealPartZeroPackage T).Nonempty → ∀ {a : ℝ},
      0 < a →
        ∃ y ∈ Set.Ioo a (a + maximalZeroPackageCanonicalIntervalLength T),
          0 < maximalZeroPackageMeanSquareMain T
              (maximalZeroPackageCanonicalIntervalLength T) y ∧
          0 < Real.sqrt (maximalZeroPackageMeanSquareMain T
                (maximalZeroPackageCanonicalIntervalLength T) y) ∧
          Real.sqrt (maximalZeroPackageMeanSquareMain T
                (maximalZeroPackageCanonicalIntervalLength T) y) -
              (Real.exp ((maximalZeroRealPart T -
                  maximalComplementaryRealPartGap T) * y) *
                (C * (1 + Real.log (T + 6)) ^ 2) +
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖) -
              (Real.log (2 * Real.pi) +
                (1 / 2 : ℝ) * Real.exp (-2 * y) /
                  (1 - Real.exp (-2 * y))) ≤
            ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  exists_C_forall_fixedHeight_maximalZeroPackage_strict_lower_bound_on_canonical_interval

example :
    ∃ T0 : ℝ, 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      (nontrivialZerosFinset T).Nonempty :=
  exists_eventually_nontrivialZerosFinset_nonempty

example :
    ∃ T0 : ℝ, 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      (maximalRealPartZeroPackage T).Nonempty :=
  exists_eventually_maximalRealPartZeroPackage_nonempty

example (K T : ℝ) (hK : 0 ≤ K) (hT : 8 ≤ T) :
    0 ≤ movingHeightApproximationBudget K T :=
  movingHeightApproximationBudget_nonneg K T hK hT

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      ∀ {a : ℝ}, 0 < a →
        ∃ y ∈ Set.Ioo a (a + maximalZeroPackageCanonicalIntervalLength T),
          ∃ K : ℝ, 0 ≤ K ∧
            (∀ U : ℝ, 8 ≤ U →
              ‖explicitFormulaApproxWithMultiplicity (Real.exp y) U -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
                movingHeightApproximationBudget K U) ∧
            0 < maximalZeroPackageMeanSquareMain T
                (maximalZeroPackageCanonicalIntervalLength T) y ∧
            0 < Real.sqrt (maximalZeroPackageMeanSquareMain T
                (maximalZeroPackageCanonicalIntervalLength T) y) ∧
            Real.sqrt (maximalZeroPackageMeanSquareMain T
                  (maximalZeroPackageCanonicalIntervalLength T) y) -
                (Real.exp ((maximalZeroRealPart T -
                    maximalComplementaryRealPartGap T) * y) *
                  (C * (1 + Real.log (T + 6)) ^ 2) +
                  movingHeightApproximationBudget K T) -
                (Real.log (2 * Real.pi) +
                  (1 / 2 : ℝ) * Real.exp (-2 * y) /
                    (1 - Real.exp (-2 * y))) ≤
              ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  exists_C_T0_forall_movingHeight_maximalZeroPackage_quantitative_lower_bound

-- Small sanity checks: the per-term identity at zero multiplicity and at `ρ = 0`.

example (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    ‖((0 : ℕ) : ℂ) * (x : ℂ) ^ ρ / ρ‖ = 0 := by
  rw [norm_natCast_mul_cpow_div x hx ρ 0]
  simp

example (x : ℝ) (hx : 0 < x) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ (0 : ℂ) / (0 : ℂ)‖ = 0 := by
  rw [norm_natCast_mul_cpow_div x hx 0 m]
  simp
