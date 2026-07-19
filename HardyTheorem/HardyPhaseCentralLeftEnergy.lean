import HardyTheorem.HardyPhaseAdditiveEnvelope
import MathlibAux.MinReciprocalSquareReindex

open Complex
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

private theorem inv_sqrt_sq_nat {n : ℕ} (hn : 0 < n) :
    ((Real.sqrt n)⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- On the central range to the left of the stationary index, the additive
stationary-distance envelope gives a uniform coefficient-energy bound. -/
theorem sum_normSq_hardyPhaseLinearizedCoeff_central_left_le
    (s : Finset ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 < delta)
    (hscale : 1 ≤ hardyPhaseStationaryScale t)
    (hleft : ∀ n ∈ s,
      n < Nat.floor (hardyPhaseStationaryScale t))
    (hcentral : ∀ n ∈ s,
      hardyPhaseStationaryScale t / 8 ≤ n) :
    (∑ n ∈ s,
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
      48 * delta := by
  let r := hardyPhaseStationaryScale t
  let m := Nat.floor r
  have hr : 0 < r := by
    exact lt_of_lt_of_le zero_lt_one (by simpa only [r] using hscale)
  have hmle : (m : ℝ) ≤ r := by
    exact Nat.floor_le hr.le
  have hpoint : ∀ n ∈ s,
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
        (8 * r⁻¹) * (min delta (2 * r / (m - n : ℕ))) ^ 2 := by
    intro n hnmem
    have hnlt := hleft n hnmem
    have hnltM : n < m := by simpa only [m, r] using hnlt
    have hncentral := hcentral n hnmem
    have hnrealpos : 0 < (n : ℝ) := by
      exact (div_pos hr (by norm_num : (0 : ℝ) < 8)).trans_le
        (by simpa only [r] using hncentral)
    have hnpos : 0 < n := by exact_mod_cast hnrealpos
    have hnleM : n ≤ m := hnltM.le
    have hnleR : (n : ℝ) ≤ r := by
      have hnleMReal : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnleM
      exact hnleMReal.trans hmle
    have hnltR : (n : ℝ) < r := by
      have hnltMReal : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnltM
      exact hnltMReal.trans_le hmle
    have haway : r ≠ (n : ℝ) := ne_of_gt hnltR
    have hjposNat : 0 < m - n := Nat.sub_pos_of_lt hnltM
    have hjpos : 0 < ((m - n : ℕ) : ℝ) := by exact_mod_cast hjposNat
    have hdist : 0 < r - (n : ℝ) := sub_pos.2 hnltR
    have hjdist : ((m - n : ℕ) : ℝ) ≤ r - (n : ℝ) := by
      rw [Nat.cast_sub hnleM]
      exact sub_le_sub_right hmle _
    have hratio :
        2 * r / (r - (n : ℝ)) ≤ 2 * r / ((m - n : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hdist hjpos).2
      exact mul_le_mul_of_nonneg_left hjdist (by positivity)
    have henv : hardyPhaseAdditiveEnvelope n delta t ≤
        min delta (2 * r / (m - n : ℕ)) := by
      rw [hardyPhaseAdditiveEnvelope, if_neg (by simpa only [r] using haway),
        max_eq_left (by simpa only [r] using hnleR),
        abs_of_nonneg (sub_nonneg.2 (by simpa only [r] using hnleR))]
      simpa only [r, m] using min_le_min_left delta hratio
    have hinv : (n : ℝ)⁻¹ ≤ 8 * r⁻¹ := by
      calc
        (n : ℝ)⁻¹ ≤ (r / 8)⁻¹ :=
          inv_anti₀ (div_pos hr (by norm_num : (0 : ℝ) < 8))
            (by simpa only [r] using hncentral)
        _ = 8 * r⁻¹ := by field_simp [hr.ne']
    have hcoeff :=
      normSq_hardyPhaseLinearizedCoeff_le_additiveEnvelope hnpos ht hdelta.le
    calc
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
          ((Real.sqrt n)⁻¹ * hardyPhaseAdditiveEnvelope n delta t) ^ 2 :=
        hcoeff
      _ = (n : ℝ)⁻¹ * (hardyPhaseAdditiveEnvelope n delta t) ^ 2 := by
        rw [mul_pow, inv_sqrt_sq_nat hnpos]
      _ ≤ (8 * r⁻¹) * (hardyPhaseAdditiveEnvelope n delta t) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
      _ ≤ (8 * r⁻¹) * (min delta (2 * r / (m - n : ℕ))) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sq_le_sq₀
          (hardyPhaseAdditiveEnvelope_nonneg n hdelta.le)
          (le_min hdelta.le (by positivity))).2 henv
  calc
    (∑ n ∈ s,
        Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
        ∑ n ∈ s,
          (8 * r⁻¹) * (min delta (2 * r / (m - n : ℕ))) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (8 * r⁻¹) * ∑ n ∈ s,
        (min delta (2 * r / (m - n : ℕ))) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (8 * r⁻¹) * (3 * (2 * r) * delta) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact MathlibAux.sum_sq_min_div_nat_sub_left_le
        s m hdelta (by positivity) (by simpa only [m] using hleft)
    _ = 48 * delta := by
      field_simp [hr.ne']
      norm_num

end HardyTheorem
