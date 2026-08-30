import PrimeNumberTheorem.MWKFCubicAFEDyadicCompletion
import PrimeNumberTheorem.MWKFCubicAFEPhysicalDecay

open MeasureTheory Set

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The exact fixed-depth spatial power majorant

At completion depth J, both positive indices are cut off below
epsilon_J=1/(2*2^J). This yields an integrable majorant in the first
index. Its epsilon factor is retained: no bound uniform in J, physical
time or the complete shift series is claimed.
-/

noncomputable def cubicAFECompletionLowerEndpoint (J : ℕ) : ℝ := 1 / (2 * (2 : ℝ)^J)

theorem cubicAFECompletionLowerEndpoint_pos (J : ℕ) :
    0 < cubicAFECompletionLowerEndpoint J := by
  unfold cubicAFECompletionLowerEndpoint
  positivity

private theorem scaled_endpoint (J : ℕ) :
    (2 : ℝ)^J * cubicAFECompletionLowerEndpoint J = 1 / 2 := by
  unfold cubicAFECompletionLowerEndpoint
  field_simp

theorem cubicAFECompletionWeight_zero_of_first_le (J : ℕ) {x : ℝ}
    (hx : x ≤ cubicAFECompletionLowerEndpoint J) (y : ℝ) :
    cubicAFEDyadicCompletionWeight J x y = 0 := by
  have hh : (2 : ℝ)^J * x ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hx (by positivity)).trans_eq (scaled_endpoint J)
  rw [cubicAFEDyadicCompletionWeight, cubicAFEDyadicLowerWeight_zero hh, zero_mul]

theorem cubicAFECompletionWeight_zero_of_second_le (J : ℕ) (x : ℝ) {y : ℝ}
    (hy : y ≤ cubicAFECompletionLowerEndpoint J) :
    cubicAFEDyadicCompletionWeight J x y = 0 := by
  have hh : (2 : ℝ)^J * y ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hy (by positivity)).trans_eq (scaled_endpoint J)
  rw [cubicAFEDyadicCompletionWeight, cubicAFEDyadicLowerWeight_zero hh, mul_zero]

theorem cubicAFECompletionWeight_nonneg (J : ℕ) (x y : ℝ) :
    0 ≤ cubicAFEDyadicCompletionWeight J x y :=
  mul_nonneg (cubicAFEDyadicLowerWeight_nonneg _) (cubicAFEDyadicLowerWeight_nonneg _)

theorem cubicAFECompletionWeight_le_one (J : ℕ) (x y : ℝ) :
    cubicAFEDyadicCompletionWeight J x y ≤ 1 := by
  unfold cubicAFEDyadicCompletionWeight
  simpa only [mul_one] using mul_le_mul (cubicAFEDyadicLowerWeight_le_one _)
    (cubicAFEDyadicLowerWeight_le_one _) (cubicAFEDyadicLowerWeight_nonneg _) zero_le_one

noncomputable def cubicAFECompletedHalfLinePower (X : ℝ) (J : ℕ) (x : ℝ) : ℝ :=
  (Ioi (cubicAFECompletionLowerEndpoint J)).indicator (fun x : ℝ ↦ x ^ (-X - 1 / 2)) x

theorem cubicAFECompletedHalfLinePower_nonneg (X : ℝ) (J : ℕ) (x : ℝ) :
    0 ≤ cubicAFECompletedHalfLinePower X J x := by
  unfold cubicAFECompletedHalfLinePower
  by_cases hx : x ∈ Ioi (cubicAFECompletionLowerEndpoint J)
  · rw [indicator_of_mem hx]
    exact Real.rpow_nonneg ((cubicAFECompletionLowerEndpoint_pos J).trans hx).le _
  · rw [indicator_of_notMem hx]

theorem integrable_cubicAFECompletedHalfLinePower {X : ℝ} (hX : 1 / 2 < X) (J : ℕ) :
    Integrable (cubicAFECompletedHalfLinePower X J) :=
  (integrableOn_Ioi_rpow_of_lt (by linarith : -X - 1 / 2 < -1)
    (cubicAFECompletionLowerEndpoint_pos J)).integrable_indicator measurableSet_Ioi

theorem cubicAFECompletionWeight_mul_product_rpow_le {X : ℝ} (hX : 1 / 2 < X)
    (J : ℕ) (x y : ℝ) :
    cubicAFEDyadicCompletionWeight J x y * (x * y) ^ (-X - 1 / 2) ≤
      (cubicAFECompletionLowerEndpoint J) ^ (-X - 1 / 2) * cubicAFECompletedHalfLinePower X J x := by
  have he := cubicAFECompletionLowerEndpoint_pos J
  by_cases hx : x ≤ cubicAFECompletionLowerEndpoint J
  · rw [cubicAFECompletionWeight_zero_of_first_le J hx y, zero_mul]
    exact mul_nonneg (Real.rpow_nonneg he.le _) (cubicAFECompletedHalfLinePower_nonneg X J x)
  by_cases hy : y ≤ cubicAFECompletionLowerEndpoint J
  · rw [cubicAFECompletionWeight_zero_of_second_le J x hy, zero_mul]
    exact mul_nonneg (Real.rpow_nonneg he.le _) (cubicAFECompletedHalfLinePower_nonneg X J x)
  have hx' : cubicAFECompletionLowerEndpoint J < x := lt_of_not_ge hx
  have hy' : cubicAFECompletionLowerEndpoint J < y := lt_of_not_ge hy
  have hx0 : 0 < x := he.trans hx'
  have hy0 : 0 < y := he.trans hy'
  calc
    _ ≤ (x * y) ^ (-X - 1 / 2) := mul_le_of_le_one_left
      (Real.rpow_nonneg (mul_pos hx0 hy0).le _) (cubicAFECompletionWeight_le_one J x y)
    _ = x ^ (-X - 1 / 2) * y ^ (-X - 1 / 2) := Real.mul_rpow hx0.le hy0.le
    _ ≤ x ^ (-X - 1 / 2) * (cubicAFECompletionLowerEndpoint J) ^ (-X - 1 / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos he hy'.le (by linarith))
        (Real.rpow_nonneg hx0.le _)
    _ = _ := by
      rw [cubicAFECompletedHalfLinePower, indicator_of_mem (show x ∈ Ioi _ from hx')]
      ring

end PrimeNumberTheorem.MWKFCubic
