import HardyTheorem.HardyPhaseStationaryScale
import HardyTheorem.HardyPhaseWindowCoeffDerivative

open Complex
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

private theorem inv_sqrt_sq_nat {n : ℕ} (hn : 0 < n) :
    ((Real.sqrt n)⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hn.le : (0 : ℝ) ≤ n)]

/-- A central multiplicative annulus has uniformly bounded reciprocal mass.
The cardinality estimate is derived from the upper endpoint, so it does not
depend on an ambient Dirichlet cutoff. -/
theorem sum_inv_nat_central_annulus_le
    (s : Finset ℕ) {r : ℝ} (hscale : 1 ≤ r)
    (hlower : ∀ n ∈ s, r / 8 ≤ n)
    (hupper : ∀ n ∈ s, (n : ℝ) ≤ 8 * r) :
    (∑ n ∈ s, ((n : ℝ))⁻¹) ≤ 64 := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hscale
  have hpoint : ∀ n ∈ s, ((n : ℝ))⁻¹ ≤ 8 * r⁻¹ := by
    intro n hn
    calc
      ((n : ℝ))⁻¹ ≤ (r / 8)⁻¹ :=
        inv_anti₀ (div_pos hr (by norm_num)) (hlower n hn)
      _ = 8 * r⁻¹ := by field_simp [hr.ne']
  have hsubset : s ⊆ Finset.Icc 1 (Nat.floor (8 * r)) := by
    intro n hn
    simp only [Finset.mem_Icc]
    constructor
    · have hnreal : 0 < (n : ℝ) :=
        (div_pos hr (by norm_num : (0 : ℝ) < 8)).trans_le (hlower n hn)
      exact_mod_cast hnreal
    · exact Nat.le_floor (hupper n hn)
  have hcard : (s.card : ℝ) ≤ 8 * r := by
    have hcardNat : s.card ≤ Nat.floor (8 * r) := by
      calc
        s.card ≤ (Finset.Icc 1 (Nat.floor (8 * r))).card :=
          Finset.card_le_card hsubset
        _ = Nat.floor (8 * r) := by simp
    calc
      (s.card : ℝ) ≤ ((Nat.floor (8 * r) : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ ≤ 8 * r := Nat.floor_le (by positivity)
  calc
    (∑ n ∈ s, ((n : ℝ))⁻¹) ≤ ∑ n ∈ s, 8 * r⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = (s.card : ℝ) * (8 * r⁻¹) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (8 * r) * (8 * r⁻¹) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 64 := by
      field_simp [hr.ne']
      ring

/-- The derivative energy of the slow Hardy window coefficients is uniformly
bounded on the central multiplicative annulus around the stationary scale. -/
theorem sum_normSq_deriv_hardyPhaseWindowCoeff_central_annulus_le
    (s : Finset ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta)
    (hscale : 1 ≤ hardyPhaseStationaryScale t)
    (hlower : ∀ n ∈ s, hardyPhaseStationaryScale t / 8 ≤ n)
    (hupper : ∀ n ∈ s, (n : ℝ) ≤ 8 * hardyPhaseStationaryScale t) :
    (∑ n ∈ s,
      Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
      4 * delta ^ 4 / t ^ 2 := by
  let C : ℝ := delta ^ 4 / (16 * t ^ 2)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpoint : ∀ n ∈ s,
      Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t) ≤
        C * ((n : ℝ))⁻¹ := by
    intro n hnmem
    have hnreal : 0 < (n : ℝ) :=
      (div_pos (lt_of_lt_of_le zero_lt_one hscale)
        (by norm_num : (0 : ℝ) < 8)).trans_le (hlower n hnmem)
    have hn : 0 < n := by exact_mod_cast hnreal
    have hnorm := norm_deriv_hardyPhaseWindowCoeff_le hn hdelta ht
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖deriv (hardyPhaseWindowCoeff n delta) t‖ ^ 2 ≤
          ((Real.sqrt n)⁻¹ * delta ^ 2 / (4 * t)) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
      _ = C * ((n : ℝ))⁻¹ := by
        dsimp only [C]
        rw [div_pow, mul_pow, inv_sqrt_sq_nat hn]
        field_simp [ht.ne']
        ring
  have hreciprocal : (∑ n ∈ s, ((n : ℝ))⁻¹) ≤ 64 :=
    sum_inv_nat_central_annulus_le s hscale hlower hupper
  calc
    (∑ n ∈ s,
      Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
        ∑ n ∈ s, C * ((n : ℝ))⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = C * ∑ n ∈ s, ((n : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ C * 64 := mul_le_mul_of_nonneg_left hreciprocal hC
    _ = 4 * delta ^ 4 / t ^ 2 := by
      dsimp only [C]
      field_simp [ht.ne']
      ring

end HardyTheorem
