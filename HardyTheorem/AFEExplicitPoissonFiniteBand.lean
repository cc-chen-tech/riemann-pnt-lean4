import HardyTheorem.AFEExplicitPoissonFirstDerivative
import HardyTheorem.AFEEndpointHarmonic

/-! Explicit harmonic bounds for finite nonstationary Poisson bands. -/

open Complex Set MeasureTheory
open scoped BigOperators

namespace HardyTheorem.AFE

private theorem norm_mode_le_firstGap
    {C₁ sigma x N t g : ℝ} {k : ℤ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 ≤ t) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hgap : ∀ u ∈ Icc (x - 1) (N + 1), g ≤ |weightedPoissonVelocity t k u|) :
    ‖explicitPoissonMode sigma x N t k‖ ≤ 16 * C₁ * (x - 1) ^ (-sigma) / g := by
  have ha : 0 < x - 1 := by linarith
  apply norm_explicitMellin_phaseIntegral_le_firstDerivative hs hx hxN hg hC₁0 hC₁
  · intro u hu
    unfold weightedPoissonPhase
    exact (contDiffAt_const.mul (Real.contDiffAt_log.mpr hu.ne')).sub
      (contDiffAt_const.mul contDiffAt_id)
  · left
    intro u hu v hv huv
    rw [(weightedPoissonPhase_hasDerivAt_velocity t k (ha.trans_le hu.1).ne').deriv,
      (weightedPoissonPhase_hasDerivAt_velocity t k (ha.trans_le hv.1).ne').deriv]
    have hdiv := div_le_div_of_nonneg_left ht (ha.trans_le hu.1) huv
    simp only [weightedPoissonVelocity, neg_div]
    linarith
  · intro u hu
    rw [(weightedPoissonPhase_hasDerivAt_velocity t k (ha.trans_le hu.1).ne').deriv]
    exact hgap u hu

private theorem norm_mode_positive_le
    {C₁ sigma x N t : ℝ} {m : ℕ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) (hm : 1 ≤ m) :
    ‖explicitPoissonMode sigma x N t (m : ℤ)‖ ≤
      (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) * (m : ℝ)⁻¹ := by
  have ha : 0 < x - 1 := by linarith
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hp := norm_mode_le_firstGap (g := 2 * Real.pi * m)
    hs hx hxN ht (by positivity) hC₁0 hC₁ (by
      intro u hu
      simpa only [Int.cast_natCast] using
        frequency_le_abs_weightedPoissonVelocity_of_nonneg_frequency
          ht (ha.trans_le hu.1) (Int.natCast_nonneg m))
  refine hp.trans_eq ?_
  field_simp
  ring

/-- All positive Poisson modes up to a finite cutoff cost only a harmonic sum. -/
theorem sum_norm_explicitPoissonMode_positive_le_log
    {C₁ sigma x N t : ℝ} (M : ℕ)
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ m ∈ Finset.Icc 1 M, ‖explicitPoissonMode sigma x N t (m : ℤ)‖) ≤
      (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) * (1 + Real.log M) := by
  have ha : 0 < x - 1 := by linarith
  have hsum : (∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹) ≤ 1 + Real.log M := by
    have h := harmonic_le_one_add_log M
    rw [harmonic_eq_sum_Icc] at h
    simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 M,
        (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) * (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_mode_positive_le hs hx hxN ht hC₁0 hC₁ (Finset.mem_Icc.mp hm).1
    _ = (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) *
        ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Negative modes beyond the left endpoint frequency, omitting its nearest
upper integer. This is a finite-band bound, not a sum of all negative modes. -/
theorem sum_norm_explicitPoissonMode_above_endpoint_le_log
    {C₁ sigma x N t : ℝ} (M : ℕ)
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 ≤ t)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ j ∈ Finset.Icc 1 M,
      ‖explicitPoissonMode sigma x N t
        (-((Nat.floor (t / (2 * Real.pi * (x - 1))) + 1 + j : ℕ) : ℤ))‖) ≤
      (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) * (1 + Real.log M) := by
  have ha : 0 < x - 1 := by linarith
  let beta := t / (2 * Real.pi * (x - 1))
  have hb0 : 0 ≤ beta := by dsimp only [beta]; positivity
  have hscale : 2 * Real.pi * beta = t / (x - 1) := by
    dsimp only [beta]
    field_simp
  have hfloor : beta < (Nat.floor beta : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one beta
  have hpoint (j : ℕ) (hj : j ∈ Finset.Icc 1 M) :
      ‖explicitPoissonMode sigma x N t (-((Nat.floor beta + 1 + j : ℕ) : ℤ))‖ ≤
        (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) *
          (((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta)⁻¹ := by
    have hj0 : 0 < (j : ℝ) := by
      exact_mod_cast (show 0 < j by have := (Finset.mem_Icc.mp hj).1; omega)
    have hdiff : 0 < ((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta := by linarith
    have hden : 2 * Real.pi * (Nat.floor beta + 1 + j : ℕ) - t / (x - 1) =
        2 * Real.pi * (((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta) := by
      rw [← hscale]
      push_cast
      ring
    have hg : 0 < 2 * Real.pi * (Nat.floor beta + 1 + j : ℕ) - t / (x - 1) := by
      rw [hden]
      positivity
    have hp := norm_mode_le_firstGap
      (k := -((Nat.floor beta + 1 + j : ℕ) : ℤ)) hs hx hxN ht hg hC₁0 hC₁ (by
        intro u hu
        exact right_endpoint_gap_le_abs_weightedPoissonVelocity_neg_nat
          ha ht hu (by linarith))
    rw [hden] at hp
    refine hp.trans_eq ?_
    field_simp
    ring
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 M,
        (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) *
          (((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta)⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = (8 * C₁ * (x - 1) ^ (-sigma) / Real.pi) *
        ∑ j ∈ Finset.Icc 1 M, (((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_reciprocal_above_floor_le_one_add_log beta hb0 M) (by positivity)

end HardyTheorem.AFE
