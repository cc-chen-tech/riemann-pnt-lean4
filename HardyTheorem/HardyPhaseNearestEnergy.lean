import HardyTheorem.HardyPhaseAdditiveEnvelope

open Complex
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

private theorem inv_sqrt_sq_nat {n : ℕ} (hn : 0 < n) :
    ((Real.sqrt n)⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hn.le)]

/-- The two integer indices nearest the stationary real scale contribute only
`O(delta^2 / r)` to the linearized Hardy phase energy. -/
theorem sum_normSq_hardyPhaseLinearizedCoeff_nearest_le
    {delta t : ℝ} (ht : 0 < t) (hdelta : 0 ≤ delta)
    (hscale : 1 ≤ hardyPhaseStationaryScale t) :
    (∑ n ∈ ({
        Nat.floor (hardyPhaseStationaryScale t),
        Nat.floor (hardyPhaseStationaryScale t) + 1
      } : Finset ℕ),
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
      16 * delta ^ 2 / hardyPhaseStationaryScale t := by
  let r := hardyPhaseStationaryScale t
  let m := Nat.floor r
  have hr : 0 < r := hardyPhaseStationaryScale_pos ht
  have hmNat : 1 ≤ m := by
    apply Nat.le_floor
    exact_mod_cast (by simpa only [r] using hscale)
  have hmpos : 0 < m := by omega
  have hm1pos : 0 < m + 1 := by omega
  have hrlt : r < (m : ℝ) + 1 := by
    simpa only [m] using Nat.lt_floor_add_one r
  have hhalf : r / 2 ≤ (m : ℝ) := by
    have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hmNat
    nlinarith
  have hinvM : (m : ℝ)⁻¹ ≤ 2 * r⁻¹ := by
    calc
      (m : ℝ)⁻¹ ≤ (r / 2)⁻¹ :=
        inv_anti₀ (div_pos hr (by norm_num)) hhalf
      _ = 2 * r⁻¹ := by field_simp [hr.ne']
  have hinvM1 : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ r⁻¹ := by
    apply inv_anti₀ hr
    simpa only [Nat.cast_add, Nat.cast_one] using hrlt.le
  have hcoeff (n : ℕ) (hn : 0 < n) :
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
        (n : ℝ)⁻¹ * delta ^ 2 := by
    calc
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
          ((Real.sqrt n)⁻¹ * delta) ^ 2 :=
        normSq_hardyPhaseLinearizedCoeff_le_length hn hdelta
      _ = (n : ℝ)⁻¹ * delta ^ 2 := by
        rw [mul_pow, inv_sqrt_sq_nat hn]
  have hmBound :
      Complex.normSq (hardyPhaseLinearizedCoeff m delta t) ≤
        2 * (delta ^ 2 / r) := by
    calc
      Complex.normSq (hardyPhaseLinearizedCoeff m delta t) ≤
          (m : ℝ)⁻¹ * delta ^ 2 := hcoeff m hmpos
      _ ≤ (2 * r⁻¹) * delta ^ 2 :=
        mul_le_mul_of_nonneg_right hinvM (sq_nonneg delta)
      _ = 2 * (delta ^ 2 / r) := by ring
  have hm1Bound :
      Complex.normSq (hardyPhaseLinearizedCoeff (m + 1) delta t) ≤
        delta ^ 2 / r := by
    calc
      Complex.normSq (hardyPhaseLinearizedCoeff (m + 1) delta t) ≤
          ((m + 1 : ℕ) : ℝ)⁻¹ * delta ^ 2 := hcoeff (m + 1) hm1pos
      _ ≤ r⁻¹ * delta ^ 2 :=
        mul_le_mul_of_nonneg_right hinvM1 (sq_nonneg delta)
      _ = delta ^ 2 / r := by ring
  have hq : 0 ≤ delta ^ 2 / r := div_nonneg (sq_nonneg delta) hr.le
  rw [Finset.sum_insert (by simp : m ∉ ({m + 1} : Finset ℕ)),
    Finset.sum_singleton]
  calc
    Complex.normSq (hardyPhaseLinearizedCoeff m delta t) +
        Complex.normSq (hardyPhaseLinearizedCoeff (m + 1) delta t) ≤
        2 * (delta ^ 2 / r) + delta ^ 2 / r :=
      add_le_add hmBound hm1Bound
    _ ≤ 16 * (delta ^ 2 / r) := by nlinarith
    _ = 16 * delta ^ 2 / r := by ring

end HardyTheorem
