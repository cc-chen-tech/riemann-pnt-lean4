import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval

open PrimeNumberTheorem
open PrimeNumberTheorem.DirichletPolynomial
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

example (T y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-(maximalZeroRealPart T) * y) *
        ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ≤
      Real.exp (-maximalComplementaryRealPartGap T * y) *
        ∑ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  normalized_norm_complementaryZeroPackageContribution_le_exp_neg_gap_mul_sum
    T y hy

example (T : ℝ) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-(maximalZeroRealPart T) * y) *
          ‖complementaryZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖)
      Filter.atTop (nhds 0) :=
  tendsto_normalized_norm_complementaryZeroPackageContribution_atTop T

example (τ : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ((∀ᶠ y : ℝ in Filter.atTop, 0 ≤ y) →
        (∀ᶠ y : ℝ in Filter.atTop, 4 ≤ τ y) →
        Filter.Tendsto
          (fun y : ℝ =>
            Real.exp (-maximalComplementaryRealPartGap (τ y) * y) *
              (C * (1 + Real.log (τ y + 6)) ^ 2))
          Filter.atTop (nhds 0) →
        Filter.Tendsto
          (fun y : ℝ =>
            Real.exp (-(maximalZeroRealPart (τ y)) * y) *
              ‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖)
          Filter.atTop (nhds 0)) :=
  exists_C_tendsto_normalized_norm_complementaryZeroPackageContribution_along_moving_height_of_majorant
    τ

example (C : ℝ) (τ gap : ℝ → ℝ)
    (hτ : ∀ᶠ y : ℝ in Filter.atTop, 4 ≤ τ y)
    (hmargin :
      Filter.Tendsto
        (fun y : ℝ =>
          gap y * y - 2 * Real.log (1 + Real.log (τ y + 6)))
        Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-gap y * y) *
          (C * (1 + Real.log (τ y + 6)) ^ 2))
      Filter.atTop (nhds 0) :=
  tendsto_gap_log_sq_majorant_of_margin_atTop C τ gap hτ hmargin

example (τ : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ((∀ᶠ y : ℝ in Filter.atTop, 0 ≤ y) →
        (∀ᶠ y : ℝ in Filter.atTop, 4 ≤ τ y) →
        Filter.Tendsto
          (fun y : ℝ =>
            maximalComplementaryRealPartGap (τ y) * y -
              2 * Real.log (1 + Real.log (τ y + 6)))
          Filter.atTop Filter.atTop →
        Filter.Tendsto
          (fun y : ℝ =>
            Real.exp (-(maximalZeroRealPart (τ y)) * y) *
              ‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖)
          Filter.atTop (nhds 0)) :=
  exists_C_tendsto_normalized_norm_complementaryZeroPackageContribution_along_moving_height_of_gap_log_sq_margin_atTop
    τ

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

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) -
        (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2| ≤
      4 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n :=
  abs_finiteExponentialMeanSquare_sub_diagonal_le_localSeparation
    hS homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {n : ι}
    (hS : S.Nontrivial) (hn : n ∈ S) :
    minimumPositiveFrequencySpacing S omega ≤
      localFrequencySeparation S omega n :=
  minimumPositiveFrequencySpacing_le_localFrequencySeparation hS hn

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    (∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n) ≤
      (∑ n ∈ S, ‖c n‖ ^ 2) /
        minimumPositiveFrequencySpacing S omega :=
  sum_sqNorm_div_localFrequencySeparation_le_div_minimumSpacing
    hS homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) -
        (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2| ≤
      4 * Real.pi * (∑ n ∈ S, ‖c n‖ ^ 2) /
        minimumPositiveFrequencySpacing S omega :=
  abs_finiteExponentialMeanSquare_sub_diagonal_le_minimumSpacing
    hS homega

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ} :
    |(∫ y in a..b,
        ‖finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y‖ ^ 2) -
        (b - a) * maximalZeroPackageEnergy T| ≤
      4 * Real.pi * maximalZeroPackageEnergy T /
        maximalZeroPackageMinimumImaginarySpacing T :=
  abs_maximalZeroPackageFiniteExponentialMeanSquare_sub_diagonal_le
    T hpackage

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (hab : a < b)
    (homega : Set.InjOn omega (S : Set ι)) :
    ∃ t ∈ Set.Ioo a b,
      (∑ n ∈ S, ‖c n‖ ^ 2) -
          (4 * Real.pi * (∑ n ∈ S, ‖c n‖ ^ 2) /
            minimumPositiveFrequencySpacing S omega) / (b - a) ≤
        ‖finiteExponentialSum S c omega t‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_finiteExponentialSum_ge_hilbert
    hS hab homega

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Set.Ioo a b,
      Real.exp (maximalZeroRealPart T * y) ^ 2 *
          (maximalZeroPackageEnergy T -
            (4 * Real.pi * maximalZeroPackageEnergy T /
              maximalZeroPackageMinimumImaginarySpacing T) / (b - a)) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_ge_hilbert
    T hpackage hab

example (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ}
    (hlength :
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T < b - a) :
    ∃ y ∈ Set.Ioo a b,
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_hilbert
    T hpackage hlength

example (T L y : ℝ) :
    maximalZeroPackageHilbertMeanSquareMain T L y =
      Real.exp (maximalZeroRealPart T * y) ^ 2 *
        (maximalZeroPackageEnergy T -
          (4 * Real.pi * maximalZeroPackageEnergy T /
            maximalZeroPackageMinimumImaginarySpacing T) / L) := rfl

example (T a b y : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    (hlength :
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T < b - a) :
    0 < maximalZeroPackageHilbertMeanSquareMain T (b - a) y :=
  maximalZeroPackageHilbertMeanSquareMain_pos T y hpackage hlength

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
    (maximalRealPartZeroPackage T).Nontrivial → ∀ {a b : ℝ},
      0 < a →
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T < b - a →
        ∃ y ∈ Set.Ioo a b,
          0 < maximalZeroPackageHilbertMeanSquareMain T (b - a) y ∧
          0 < Real.sqrt
            (maximalZeroPackageHilbertMeanSquareMain T (b - a) y) ∧
          Real.sqrt
                (maximalZeroPackageHilbertMeanSquareMain T (b - a) y) -
              (Real.exp ((maximalZeroRealPart T -
                  maximalComplementaryRealPartGap T) * y) *
                (C * (1 + Real.log (T + 6)) ^ 2) +
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖) -
              (Real.log (2 * Real.pi) +
                (1 / 2 : ℝ) * Real.exp (-2 * y) /
                  (1 - Real.exp (-2 * y))) ≤
            ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  exists_C_forall_fixedHeight_maximalZeroPackage_hilbert_lower_bound

example (T : ℝ) :
    maximalZeroPackageHilbertIntervalLengthThreshold T =
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T := rfl

example (T : ℝ) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageUnifiedIntervalLengthThreshold T + 1 := rfl

example (T L y : ℝ) :
    maximalZeroPackageUnifiedMeanSquareMain T L y =
      if (maximalRealPartZeroPackage T).Nontrivial then
        if maximalZeroPackageIntervalLengthThreshold T ≤
            maximalZeroPackageHilbertIntervalLengthThreshold T then
          maximalZeroPackageMeanSquareMain T L y
        else
          maximalZeroPackageHilbertMeanSquareMain T L y
      else
        maximalZeroPackageMeanSquareMain T L y := rfl

example (T : ℝ) (hcard : (maximalRealPartZeroPackage T).card = 1) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageCanonicalIntervalLength T :=
  maximalZeroPackageUnifiedCanonical_eq_exact_of_card_eq_one T hcard

example (T : ℝ)
    (hpackage : ¬(maximalRealPartZeroPackage T).Nontrivial) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageCanonicalIntervalLength T :=
  maximalZeroPackageUnifiedCanonical_eq_exact_of_not_nontrivial T hpackage

example
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (hnontrivial : (maximalRealPartZeroPackage T).Nontrivial) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T ≤
      min
        (2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T)
        (maximalZeroPackageHilbertIntervalLengthThreshold T) + 1 :=
  maximalZeroPackageUnifiedCanonicalIntervalLength_le_min_pairwise_hilbert
    T hpackage hnontrivial

example (T : ℝ) :
    maximalZeroPackageHilbertIntervalLengthThreshold T <
        2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T ↔
      8 ≤ (maximalRealPartZeroPackage T).card :=
  maximalZeroPackageHilbertIntervalLengthThreshold_lt_pairwise_iff T

example
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    {a b : ℝ}
    (hlength : maximalZeroPackageIntervalLengthThreshold T < b - a) :
    ∃ y ∈ Set.Ioo a b,
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_exact
    T hpackage hlength

example
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (a : ℝ) :
    ∃ y ∈ Set.Ioo a
        (a + maximalZeroPackageUnifiedCanonicalIntervalLength T),
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_on_unified_canonical
    T hpackage a

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
    (maximalRealPartZeroPackage T).Nonempty → ∀ {a : ℝ}, 0 < a →
      ∃ y ∈ Set.Ioo a
          (a + maximalZeroPackageUnifiedCanonicalIntervalLength T),
        0 < maximalZeroPackageUnifiedMeanSquareMain T
            (maximalZeroPackageUnifiedCanonicalIntervalLength T) y ∧
        0 < Real.sqrt (maximalZeroPackageUnifiedMeanSquareMain T
              (maximalZeroPackageUnifiedCanonicalIntervalLength T) y) ∧
        Real.sqrt (maximalZeroPackageUnifiedMeanSquareMain T
                (maximalZeroPackageUnifiedCanonicalIntervalLength T) y) -
              (Real.exp ((maximalZeroRealPart T -
                  maximalComplementaryRealPartGap T) * y) *
                (C * (1 + Real.log (T + 6)) ^ 2) +
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖) -
              (Real.log (2 * Real.pi) +
                (1 / 2 : ℝ) * Real.exp (-2 * y) /
                  (1 - Real.exp (-2 * y))) ≤
            ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  exists_C_forall_fixedHeight_maximalZeroPackage_unified_lower_bound_on_canonical_interval

example (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    0 < maximalZeroRealPart T :=
  maximalZeroRealPart_pos_of_maximalRealPartZeroPackage_nonempty T hpackage

example (β : ℝ) (hβ : 0 < β) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-β * y) * ‖zeroPackageClosedTerms y‖)
      Filter.atTop (nhds 0) :=
  tendsto_normalized_norm_zeroPackageClosedTerms_atTop β hβ

example (T : ℝ) (hβ : 0 < maximalZeroRealPart T) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-maximalZeroRealPart T * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ +
            ‖zeroPackageClosedTerms y‖))
      Filter.atTop (nhds 0) :=
  tendsto_normalized_fixedHeight_complementary_add_closedTerms_atTop T hβ

example (T y : ℝ) :
    ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ -
        ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ -
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ -
        ‖zeroPackageClosedTerms y‖ ≤
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  norm_zeroPackage_sub_complementary_sub_approximation_sub_closed_le_psi0 T y

example (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    0 < maximalZeroPackageCanonicalNormalizedAmplitude T :=
  maximalZeroPackageCanonicalNormalizedAmplitude_pos T hpackage

example (T a : ℝ) :
    ∃ y ∈ Set.Ioo a
        (a + maximalZeroPackageCanonicalIntervalLength T),
      maximalZeroPackageCanonicalNormalizedAmplitude T ≤
        Real.exp (-maximalZeroRealPart T * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ :=
  exists_mem_Ioo_normalized_maximalZeroPackageContribution_ge_canonicalAmplitude
    T a

example (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    ∃ A : ℝ, ∀ a : ℝ, A ≤ a →
      (∀ y ∈ Set.Ioo a
          (a + maximalZeroPackageCanonicalIntervalLength T),
        Real.exp (-maximalZeroRealPart T * y) *
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ <
          maximalZeroPackageCanonicalNormalizedAmplitude T / 2) →
      ∃ y ∈ Set.Ioo a
          (a + maximalZeroPackageCanonicalIntervalLength T),
        0 <
          ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  exists_eventually_fixedHeight_psi0_error_pos_of_approximation_small
    T hpackage

example (τ : ℝ → ℝ) (y : ℝ)
    (hvisible :
      maximalZeroPackageCanonicalNormalizedAmplitude (τ y) ≤
        Real.exp (-maximalZeroRealPart (τ y) * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖)
    (hbudget :
      Real.exp (-maximalZeroRealPart (τ y) * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) (τ y) -
                (chebyshevPsi0 (Real.exp y) : ℂ)‖ +
            ‖zeroPackageClosedTerms y‖) <
        maximalZeroPackageCanonicalNormalizedAmplitude (τ y)) :
    0 <
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  psi0_error_pos_of_movingHeight_visible_point_and_exact_budget
    τ y hvisible hbudget

example (τ : ℝ → ℝ) (y K : ℝ) (hheight : 8 ≤ τ y)
    (hvisible :
      maximalZeroPackageCanonicalNormalizedAmplitude (τ y) ≤
        Real.exp (-maximalZeroRealPart (τ y) * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖)
    (happrox :
      ∀ U : ℝ, 8 ≤ U →
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) U -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
          movingHeightApproximationBudget K U)
    (hbudget :
      Real.exp (-maximalZeroRealPart (τ y) * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖ +
            movingHeightApproximationBudget K (τ y) +
            ‖zeroPackageClosedTerms y‖) <
        maximalZeroPackageCanonicalNormalizedAmplitude (τ y)) :
    0 <
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  psi0_error_pos_of_movingHeight_visible_point_and_approximation_budget
    τ y K hheight hvisible happrox hbudget

example (τ : ℝ → ℝ) (y : ℝ) (hy : 0 < y) (hheight : 8 ≤ τ y)
    (hvisible :
      maximalZeroPackageCanonicalNormalizedAmplitude (τ y) ≤
        Real.exp (-maximalZeroRealPart (τ y) * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ U : ℝ, 8 ≤ U →
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) U -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
          movingHeightApproximationBudget K U) ∧
      (Real.exp (-maximalZeroRealPart (τ y) * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖ +
            movingHeightApproximationBudget K (τ y) +
            ‖zeroPackageClosedTerms y‖) <
          maximalZeroPackageCanonicalNormalizedAmplitude (τ y) →
        0 <
          ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖) :=
  exists_K_movingHeight_psi0_error_pos_of_visible_point_and_budget
    τ y hy hheight hvisible

example (K : ℝ → ℝ) (K0 κ lam β : ℝ)
    (hK0 : 0 ≤ K0) (hlam : 0 < lam) (hrate : κ < lam + β)
    (hK :
      ∀ᶠ y : ℝ in Filter.atTop,
        0 ≤ K y ∧ K y ≤ K0 * Real.exp (κ * y)) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-β * y) *
          movingHeightApproximationBudget (K y) (Real.exp (lam * y)))
      Filter.atTop (nhds 0) :=
  tendsto_normalized_movingHeightApproximationBudget_exp_atTop
    K K0 κ lam β hK0 hlam hrate hK

example (K : ℝ → ℝ) (K0 κ lam β gap : ℝ)
    (hK0 : 0 ≤ K0) (hlam : 0 < lam) (hrate : κ < lam + β)
    (hgap : 0 < gap)
    (hK :
      ∀ᶠ y : ℝ in Filter.atTop,
        0 ≤ K y ∧ K y ≤ K0 * Real.exp (κ * y)) :
    ∀ᶠ y : ℝ in Filter.atTop,
      Real.exp (-β * y) *
          movingHeightApproximationBudget (K y) (Real.exp (lam * y)) <
        gap :=
  eventually_normalized_movingHeightApproximationBudget_exp_lt_gap
    K K0 κ lam β gap hK0 hlam hrate hgap hK

example :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {x : ℝ}, 1 < x →
      ∀ {T U : ℝ}, 4 ≤ T → T ≤ U → U ≤ T + 3 →
        ‖explicitFormulaApproxWithMultiplicity x T -
            explicitFormulaApproxWithMultiplicity x U‖ ≤
          2 * Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) :=
  exists_uniform_norm_explicitFormulaApproxWithMultiplicity_sub_le_log_div_of_le_add_three

example {x Cs Cg : ℝ} (hx : 1 < x) (hCs : 0 ≤ Cs) (hCg : 0 ≤ Cg)
    (hselected :
      ∀ A : ℝ, 8 ≤ A →
        ∃ U ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight U ∧
          ‖explicitFormulaApproxWithMultiplicity x U -
              (chebyshevPsi0 x : ℂ)‖ ≤
            Cs * (1 + Real.log (A + 6)) ^ 2 / U)
    (hgap :
      ∀ {T U : ℝ}, 4 ≤ T → T ≤ U → U ≤ T + 3 →
        ‖explicitFormulaApproxWithMultiplicity x T -
            explicitFormulaApproxWithMultiplicity x U‖ ≤
          2 * Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2))
    (T : ℝ) (hT : 8 ≤ T) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        (chebyshevPsi0 x : ℂ)‖ ≤
      movingHeightApproximationBudget (Cs + 4 * Cg * x) T :=
  norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_structural_allHeights
    hx hCs hCg hselected hgap T hT

example :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {x : ℝ}, 1 < x →
      ∃ Cs : ℝ, 0 ≤ Cs ∧
        (∀ A : ℝ, 8 ≤ A →
          ∃ U ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight U ∧
            ‖explicitFormulaApproxWithMultiplicity x U -
                (chebyshevPsi0 x : ℂ)‖ ≤
              Cs * (1 + Real.log (A + 6)) ^ 2 / U) ∧
        ∀ T : ℝ, 8 ≤ T →
          ‖explicitFormulaApproxWithMultiplicity x T -
              (chebyshevPsi0 x : ℂ)‖ ≤
            movingHeightApproximationBudget (Cs + 4 * Cg * x) T :=
  exists_uniform_gap_constant_forall_exists_structural_allHeights_certificate

example (Cs : ℝ → ℝ) (Cg Cs0 κ lam β : ℝ)
    (hCg : 0 ≤ Cg) (hCs0 : 0 ≤ Cs0) (hkappa : 1 ≤ κ)
    (hlam : 0 < lam) (hrate : κ < lam + β)
    (hCs :
      ∀ᶠ y : ℝ in Filter.atTop,
        0 ≤ Cs y ∧ Cs y ≤ Cs0 * Real.exp (κ * y)) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-β * y) *
          movingHeightApproximationBudget
            (Cs y + 4 * Cg * Real.exp y) (Real.exp (lam * y)))
      Filter.atTop (nhds 0) :=
  tendsto_normalized_structural_allHeights_budget_exp_atTop
    Cs Cg Cs0 κ lam β hCg hCs0 hkappa hlam hrate hCs

example {x Cp : ℝ} (hCp : 0 ≤ Cp)
    (hbound :
      ∀ W : ℝ, 1 ≤ W →
        ‖(∫ w : ℝ in (-W)..W,
            (x : ℂ) ^ perronLine 2 w *
              (-deriv riemannZeta (perronLine 2 w) /
                riemannZeta (perronLine 2 w)) /
                  perronLine 2 w) -
            (chebyshevPsi0 x : ℂ)‖ ≤ Cp / W) :
    PerronResidualCertificate x Cp :=
  ⟨hCp, hbound⟩

example {x : ℝ} (hx : 0 < x) :
    ∃ Cp : ℝ, PerronResidualCertificate x Cp :=
  exists_perronResidualCertificate hx

example {x A T Ch Cp : ℝ} {N : ℕ}
    (hx : 2 ≤ x) (hA : 8 ≤ A) (hTmem : T ∈ Set.Icc A (A + 1))
    (hgood : ExplicitFormulaAux.goodHeight T) (hCh : 0 ≤ Ch)
    (hhorizontal :
      ∀ {a : ℝ}, a ≤ -1 →
        ‖(∫ σ : ℝ in a..2,
              ExplicitFormulaResidues.explicitFormulaIntegrand
                x ((σ : ℂ) + I * (-T))) -
            (∫ σ : ℝ in a..2,
              ExplicitFormulaResidues.explicitFormulaIntegrand
                x ((σ : ℂ) + I * T))‖ ≤
          Ch * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T)
    (hCp : PerronResidualCertificate x Cp) :
    ‖(∑ p ∈ ExplicitFormulaAux.finiteTrivialZeroSum (2 * (N : ℝ)),
          -((x : ℂ) ^ p) / p) +
        ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
          ∑ ρ ∈ nontrivialZerosFinset T,
            -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
        (chebyshevPsi0 x : ℂ)‖ ≤
      (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp) *
          (1 + Real.log (A + 6)) ^ 2 / T +
        (((ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
          ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
          x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
          (2 * Real.pi) :=
  norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_of_uniform_horizontal_of_perronResidual
    hx hA hTmem hgood hCh hhorizontal hCp

example :
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ {x : ℝ}, 2 ≤ x →
      ∀ {Cp : ℝ}, PerronResidualCertificate x Cp →
        ∀ A : ℝ, 8 ≤ A →
          ∃ T ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight T ∧
            ‖explicitFormulaApproxWithMultiplicity x T -
                (chebyshevPsi0 x : ℂ)‖ ≤
              (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp + 2) *
                (1 + Real.log (A + 6)) ^ 2 / T :=
  exists_uniform_contour_constant_selectedHeight_of_perronResidual

example :
    ∃ Ch Cg : ℝ, 0 ≤ Ch ∧ 0 ≤ Cg ∧ ∀ {x : ℝ}, 2 ≤ x →
      ∀ {Cp : ℝ}, PerronResidualCertificate x Cp →
        (∀ A : ℝ, 8 ≤ A →
          ∃ U ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight U ∧
            ‖explicitFormulaApproxWithMultiplicity x U -
                (chebyshevPsi0 x : ℂ)‖ ≤
              (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp + 2) *
                (1 + Real.log (A + 6)) ^ 2 / U) ∧
        ∀ T : ℝ, 8 ≤ T →
          ‖explicitFormulaApproxWithMultiplicity x T -
              (chebyshevPsi0 x : ℂ)‖ ≤
            movingHeightApproximationBudget
              (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp + 2 +
                4 * Cg * x) T :=
  exists_uniform_contour_gap_constants_structural_allHeights_of_perronResidual

example (Cp : ℝ → ℝ) (Ch Cg Cp0 κ lam β : ℝ)
    (hCh : 0 ≤ Ch) (hCg : 0 ≤ Cg) (hCp0 : 0 ≤ Cp0)
    (hkappa : 2 ≤ κ) (hlam : 0 < lam) (hrate : κ < lam + β)
    (hCp :
      ∀ᶠ y : ℝ in Filter.atTop,
        0 ≤ Cp y ∧ Cp y ≤ Cp0 * Real.exp (κ * y)) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-β * y) *
          movingHeightApproximationBudget
            (Ch * (Real.exp y) ^ (2 : ℝ) +
                2 * Real.pi * Cp y + 2 +
              4 * Cg * Real.exp y)
            (Real.exp (lam * y)))
      Filter.atTop (nhds 0) :=
  tendsto_normalized_structural_allHeights_budget_of_perronResidual_exp_atTop
    Cp Ch Cg Cp0 κ lam β hCh hCg hCp0 hkappa hlam hrate hCp

example (Cp : ℝ → ℝ) (Cp0 κ lam β : ℝ)
    (hCp0 : 0 ≤ Cp0) (hkappa : 2 ≤ κ)
    (hlam : 0 < lam) (hrate : κ < lam + β)
    (hcertificate :
      ∀ᶠ y : ℝ in Filter.atTop,
        PerronResidualCertificate (Real.exp y) (Cp y))
    (hCpBound :
      ∀ᶠ y : ℝ in Filter.atTop,
        Cp y ≤ Cp0 * Real.exp (κ * y)) :
    ∃ Ch Cg : ℝ, 0 ≤ Ch ∧ 0 ≤ Cg ∧
      (∀ᶠ y : ℝ in Filter.atTop,
        ∀ T : ℝ, 8 ≤ T →
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
            movingHeightApproximationBudget
              (Ch * (Real.exp y) ^ (2 : ℝ) +
                  2 * Real.pi * Cp y + 2 +
                4 * Cg * Real.exp y) T) ∧
      Filter.Tendsto
        (fun y : ℝ =>
          Real.exp (-β * y) *
            movingHeightApproximationBudget
              (Ch * (Real.exp y) ^ (2 : ℝ) +
                  2 * Real.pi * Cp y + 2 +
                4 * Cg * Real.exp y)
              (Real.exp (lam * y)))
        Filter.atTop (nhds 0) :=
  exists_uniform_contour_gap_constants_eventually_allHeights_and_tendsto_of_perronResidual
    Cp Cp0 κ lam β hCp0 hkappa hlam hrate hcertificate hCpBound

example :
    ∃ Cp0 : ℝ, 0 ≤ Cp0 ∧ ∀ m : ℕ, 2 ≤ m →
      PerronResidualCertificate (m : ℝ) (Cp0 * (m : ℝ) ^ 5) :=
  exists_uniform_nat_perronResidualCertificate

example (y : ℝ) (hy : 0 ≤ y) :
    y ≤ upperNaturalLogSample y ∧
      upperNaturalLogSample y - y < Real.exp (-y) :=
  upperNaturalLogSample_mem_short_interval y hy

example (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    ∃ Cp0 A : ℝ, 0 ≤ Cp0 ∧ ∀ a : ℝ, A ≤ a →
      ∃ m : ℕ, 2 ≤ m ∧
        Real.log (m : ℝ) ∈
          Set.Ioo a (a + maximalZeroPackageCanonicalIntervalLength T + 1) ∧
        PerronResidualCertificate (m : ℝ) (Cp0 * (m : ℝ) ^ 5) ∧
        maximalZeroPackageCanonicalNormalizedAmplitude T / 2 ≤
          Real.exp (-maximalZeroRealPart T * Real.log (m : ℝ)) *
            ‖equalRealPartZeroPackageContribution (m : ℝ) T
              (maximalZeroRealPart T)‖ :=
  exists_uniform_nat_perronResidualCertificate_and_eventually_visible
    T hpackage

example (lam β : ℝ) (hlam : 0 < lam) (hrate : 5 < lam + β) :
    ∃ Cp0 Ch Cg : ℝ, 0 ≤ Cp0 ∧ 0 ≤ Ch ∧ 0 ≤ Cg ∧
      (∀ᶠ y : ℝ in Filter.atTop,
        let m := upperNaturalLogSampleNat y
        PerronResidualCertificate (m : ℝ) (Cp0 * (m : ℝ) ^ 5) ∧
          ∀ T : ℝ, 8 ≤ T →
            ‖explicitFormulaApproxWithMultiplicity (m : ℝ) T -
                (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
              movingHeightApproximationBudget
                (Ch * (m : ℝ) ^ (2 : ℝ) +
                    2 * Real.pi * (Cp0 * (m : ℝ) ^ 5) + 2 +
                  4 * Cg * (m : ℝ)) T) ∧
      Filter.Tendsto
        (fun y : ℝ =>
          let m := upperNaturalLogSampleNat y
          Real.exp (-β * Real.log (m : ℝ)) *
            movingHeightApproximationBudget
              (Ch * (m : ℝ) ^ (2 : ℝ) +
                  2 * Real.pi * (Cp0 * (m : ℝ) ^ 5) + 2 +
                4 * Cg * (m : ℝ))
              (Real.exp (lam * Real.log (m : ℝ))))
        Filter.atTop (nhds 0) :=
  exists_uniform_contour_gap_constants_eventually_natLogSamples_and_tendsto
    lam β hlam hrate

-- Small sanity checks: the per-term identity at zero multiplicity and at `ρ = 0`.

example (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    ‖((0 : ℕ) : ℂ) * (x : ℂ) ^ ρ / ρ‖ = 0 := by
  rw [norm_natCast_mul_cpow_div x hx ρ 0]
  simp

example (x : ℝ) (hx : 0 < x) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ (0 : ℂ) / (0 : ℂ)‖ = 0 := by
  rw [norm_natCast_mul_cpow_div x hx 0 m]
  simp
