import PrimeNumberTheorem.VKEdgeCosineModelAnnihilator

open Complex MeasureTheory Set
open PrimeNumberTheorem VKEdgePiOverTwo

#check symmetricFrequencyAnnihilator
#check annihilatedNormalizedPsiError

#check (symmetricFrequencyAnnihilator_cosinePairModel :
  ∀ h gamma m lambda phase y : ℝ,
    symmetricFrequencyAnnihilator h gamma
        (cosinePairModel m lambda phase) y =
      2 * (Real.cos (lambda * h) - Real.cos (gamma * h)) *
        cosinePairModel m lambda phase y)

#check (symmetricFrequencyAnnihilator_cosineModelPair_eq_zero :
  ∀ h gamma m phase y : ℝ,
    symmetricFrequencyAnnihilator h gamma
        (cosinePairModel m gamma phase) y = 0)

#check (annihilatedNormalizedPsiError_eq_modelResidual :
  ∀ (rho : ℂ) (h y : ℝ),
    annihilatedNormalizedPsiError rho h y =
      symmetricFrequencyAnnihilator h rho.im
        (normalizedPsiModelResidual rho) y)

#check (annihilatedNormalizedPsiError_eq_threeScale :
  ∀ (rho : ℂ) (h y : ℝ),
    annihilatedNormalizedPsiError rho h y =
      ‖rho‖ * Real.exp (-rho.re * y) *
        (Real.exp (-rho.re * h) *
            (chebyshevPsi (Real.exp (y + h)) - Real.exp (y + h)) -
          2 * Real.cos (rho.im * h) *
            (chebyshevPsi (Real.exp y) - Real.exp y) +
          Real.exp (rho.re * h) *
            (chebyshevPsi (Real.exp (y - h)) - Real.exp (y - h))))

#check (sq_symmetricFrequencyAnnihilator_le :
  ∀ (f : ℝ → ℝ) (h gamma y : ℝ),
    symmetricFrequencyAnnihilator h gamma f y ^ 2 ≤
      12 * (f (y + h) ^ 2 + f y ^ 2 + f (y - h) ^ 2))

#check (integral_sq_symmetricFrequencyAnnihilator_le_of_shifted :
  ∀ {f : ℝ → ℝ} {s : Set ℝ} {h gamma E : ℝ},
    IntegrableOn (fun y => f (y + h) ^ 2) s →
    IntegrableOn (fun y => f y ^ 2) s →
    IntegrableOn (fun y => f (y - h) ^ 2) s →
    IntegrableOn
      (fun y => symmetricFrequencyAnnihilator h gamma f y ^ 2) s →
    (∫ y in s, f (y + h) ^ 2) ≤ E →
    (∫ y in s, f y ^ 2) ≤ E →
    (∫ y in s, f (y - h) ^ 2) ≤ E →
    (∫ y in s, symmetricFrequencyAnnihilator h gamma f y ^ 2) ≤
      36 * E)

#check (
  integral_annihilatedNormalizedPsiError_sq_le_of_modelResidual_shifts :
  ∀ {rho : ℂ} {s : Set ℝ} {h E : ℝ},
    IntegrableOn
      (fun y => normalizedPsiModelResidual rho (y + h) ^ 2) s →
    IntegrableOn (fun y => normalizedPsiModelResidual rho y ^ 2) s →
    IntegrableOn
      (fun y => normalizedPsiModelResidual rho (y - h) ^ 2) s →
    IntegrableOn
      (fun y => annihilatedNormalizedPsiError rho h y ^ 2) s →
    (∫ y in s, normalizedPsiModelResidual rho (y + h) ^ 2) ≤ E →
    (∫ y in s, normalizedPsiModelResidual rho y ^ 2) ≤ E →
    (∫ y in s, normalizedPsiModelResidual rho (y - h) ^ 2) ≤ E →
    (∫ y in s, annihilatedNormalizedPsiError rho h y ^ 2) ≤
      36 * E)

#check (exists_mem_expandedInterval_sq_gt_of_detector_energy_pos :
  ∀ {f : ℝ → ℝ} {a b h gamma : ℝ},
    a < b →
    IntegrableOn
      (fun y => symmetricFrequencyAnnihilator h gamma f y ^ 2)
      (Icc a b) →
    0 <
      ∫ y in Icc a b,
        symmetricFrequencyAnnihilator h gamma f y ^ 2 →
    ∃ z ∈ Icc (a - |h|) (b + |h|),
      (∫ y in Icc a b,
          symmetricFrequencyAnnihilator h gamma f y ^ 2) /
          (72 * (b - a)) <
        f z ^ 2)

#check (
  exists_mem_expandedInterval_normalizedPsiModelResidual_sq_gt :
  ∀ {rho : ℂ} {a b h : ℝ},
    a < b →
    IntegrableOn
      (fun y => annihilatedNormalizedPsiError rho h y ^ 2)
      (Icc a b) →
    0 <
      ∫ y in Icc a b,
        annihilatedNormalizedPsiError rho h y ^ 2 →
    ∃ z ∈ Icc (a - |h|) (b + |h|),
      (∫ y in Icc a b,
          annihilatedNormalizedPsiError rho h y ^ 2) /
          (72 * (b - a)) <
        normalizedPsiModelResidual rho z ^ 2)

#check (no_positive_lower_bound_on_pure_cosine_model :
  ∀ {h gamma m phase C a b : ℝ},
    0 < C →
    a < b →
    ¬ C * (b - a) ≤
      ∫ y in Icc a b,
        symmetricFrequencyAnnihilator h gamma
          (cosinePairModel m gamma phase) y ^ 2)

#check (symmetricFrequencyAnnihilator_cosinePairModel_eq_zero_iff :
  ∀ {h gamma m lambda phase y : ℝ},
    m ≠ 0 →
    Real.cos (lambda * y - phase) ≠ 0 →
    (symmetricFrequencyAnnihilator h gamma
        (cosinePairModel m lambda phase) y = 0 ↔
      Real.cos (lambda * h) = Real.cos (gamma * h)))
