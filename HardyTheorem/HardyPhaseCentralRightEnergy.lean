import HardyTheorem.HardyPhaseAdditiveEnvelope
import MathlibAux.MinReciprocalSquareReindex

open Complex
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

private theorem inv_sqrt_sq_nat {n : ℕ} (hn : 0 < n) :
    ((Real.sqrt n)⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hn.le)]

/-- On the central range to the right of the two nearest stationary indices,
the additive stationary-distance envelope has uniformly bounded energy. -/
theorem sum_normSq_hardyPhaseLinearizedCoeff_central_right_le
    (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 < delta)
    (hscale : 1 ≤ hardyPhaseStationaryScale t)
    (hright : ∀ n ∈ s,
      Nat.floor (hardyPhaseStationaryScale t) + 1 < n)
    (hupperNat : ∀ n ∈ s, n ≤ N)
    (hcentral : ∀ n ∈ s,
      (n : ℝ) ≤ 8 * hardyPhaseStationaryScale t) :
    (∑ n ∈ s,
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
      48 * delta := by
  let r := hardyPhaseStationaryScale t
  let m := Nat.floor r
  let base := m + 1
  have hr : 0 < r := hardyPhaseStationaryScale_pos ht
  have hrFloor : (m : ℝ) ≤ r := by
    exact Nat.floor_le hr.le
  have hrBase : r < (base : ℕ) := by
    simpa only [m, base, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one r
  have hpoint : ∀ n ∈ s,
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
        r⁻¹ * (min delta (16 * r / (n - base : ℕ))) ^ 2 := by
    intro n hnmem
    have hnBase := hright n hnmem
    have hnpos : 0 < n := by omega
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hrn : r < (n : ℝ) := hrBase.trans_le (by exact_mod_cast hnBase.le)
    have haway : r ≠ (n : ℝ) := ne_of_lt hrn
    have hjposNat : 0 < n - base := Nat.sub_pos_of_lt hnBase
    have hjpos : 0 < ((n - base : ℕ) : ℝ) := by exact_mod_cast hjposNat
    have hdist : 0 < (n : ℝ) - r := sub_pos.2 hrn
    have hjdist : ((n - base : ℕ) : ℝ) ≤ (n : ℝ) - r := by
      rw [Nat.cast_sub hnBase.le]
      exact sub_le_sub_left hrBase.le _
    have hnum : 2 * (n : ℝ) ≤ 16 * r := by
      nlinarith [hcentral n hnmem]
    have hratio :
        2 * (n : ℝ) / ((n : ℝ) - r) ≤
          16 * r / ((n - base : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hdist hjpos).2
      calc
        2 * (n : ℝ) * ((n - base : ℕ) : ℝ) ≤
            16 * r * ((n - base : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hnum hjpos.le
        _ ≤ 16 * r * ((n : ℝ) - r) :=
          mul_le_mul_of_nonneg_left hjdist (by positivity)
    have henv : hardyPhaseAdditiveEnvelope n delta t ≤
        min delta (16 * r / (n - base : ℕ)) := by
      rw [hardyPhaseAdditiveEnvelope, if_neg haway,
        max_eq_right hrn.le, abs_of_nonpos (sub_nonpos.2 hrn.le)]
      simpa only [neg_sub] using min_le_min_left delta hratio
    have hcoeff :=
      normSq_hardyPhaseLinearizedCoeff_le_additiveEnvelope hnpos ht hdelta.le
    calc
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
          ((Real.sqrt n)⁻¹ * hardyPhaseAdditiveEnvelope n delta t) ^ 2 :=
        hcoeff
      _ = (n : ℝ)⁻¹ * (hardyPhaseAdditiveEnvelope n delta t) ^ 2 := by
        rw [mul_pow, inv_sqrt_sq_nat hnpos]
      _ ≤ r⁻¹ * (hardyPhaseAdditiveEnvelope n delta t) ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (inv_anti₀ hr hrn.le) (sq_nonneg _)
      _ ≤ r⁻¹ * (min delta (16 * r / (n - base : ℕ))) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sq_le_sq₀
          (hardyPhaseAdditiveEnvelope_nonneg n hdelta.le)
          (le_min hdelta.le (by positivity))).2 henv
  calc
    (∑ n ∈ s,
        Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
        ∑ n ∈ s,
          r⁻¹ * (min delta (16 * r / (n - base : ℕ))) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = r⁻¹ * ∑ n ∈ s,
        (min delta (16 * r / (n - base : ℕ))) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ r⁻¹ * (3 * (16 * r) * delta) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact MathlibAux.sum_sq_min_div_nat_sub_right_le
        s base N hdelta (by positivity) hright hupperNat
    _ = 48 * delta := by
      field_simp
      norm_num

end HardyTheorem
