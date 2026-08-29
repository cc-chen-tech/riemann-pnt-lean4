import HardyTheorem.AFEWeightedPoissonVelocity

/-!
# Endpoint lower bounds for the Poisson phase velocity

The negative Fourier modes are split on the two sides of their stationary
frequency interval.  The bounds below retain the exact endpoint gaps which
are later summed by the shifted harmonic estimates.
-/

noncomputable section

open Set

namespace HardyTheorem
namespace AFE

theorem weightedPoissonVelocity_neg_nat
    (t : ℝ) (m : ℕ) (u : ℝ) :
    weightedPoissonVelocity t (-(m : ℤ)) u =
      2 * Real.pi * (m : ℝ) - t / u := by
  rw [weightedPoissonVelocity]
  push_cast
  ring

theorem abs_weightedPoissonVelocity_of_nonneg_frequency
    {t u : ℝ} {k : ℤ} (ht : 0 ≤ t) (hu : 0 < u) (hk : 0 ≤ k) :
    |weightedPoissonVelocity t k u| =
      t / u + 2 * Real.pi * (k : ℝ) := by
  have htdiv : 0 ≤ t / u := div_nonneg ht hu.le
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hfreq : 0 ≤ 2 * Real.pi * (k : ℝ) := by positivity
  have hnonpos : -t / u - 2 * Real.pi * (k : ℝ) ≤ 0 := by
    rw [neg_div]
    linarith
  rw [weightedPoissonVelocity, abs_of_nonpos hnonpos]
  ring

theorem time_div_le_abs_weightedPoissonVelocity_of_nonneg_frequency
    {t u : ℝ} {k : ℤ} (ht : 0 ≤ t) (hu : 0 < u) (hk : 0 ≤ k) :
    t / u ≤ |weightedPoissonVelocity t k u| := by
  rw [abs_weightedPoissonVelocity_of_nonneg_frequency ht hu hk]
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hfreq : 0 ≤ 2 * Real.pi * (k : ℝ) := by positivity
  linarith

theorem frequency_le_abs_weightedPoissonVelocity_of_nonneg_frequency
    {t u : ℝ} {k : ℤ} (ht : 0 ≤ t) (hu : 0 < u) (hk : 0 ≤ k) :
    2 * Real.pi * (k : ℝ) ≤ |weightedPoissonVelocity t k u| := by
  rw [abs_weightedPoissonVelocity_of_nonneg_frequency ht hu hk]
  have htdiv : 0 ≤ t / u := div_nonneg ht hu.le
  linarith

theorem left_endpoint_gap_le_abs_weightedPoissonVelocity_neg_nat
    {a b t u : ℝ} {m : ℕ}
    (ha : 0 < a) (ht : 0 ≤ t) (hu : u ∈ Icc a b)
    (hmleft : 2 * Real.pi * (m : ℝ) ≤ t / b) :
    t / b - 2 * Real.pi * (m : ℝ) ≤
      |weightedPoissonVelocity t (-(m : ℤ)) u| := by
  have hu_pos : 0 < u := ha.trans_le hu.1
  have hb_pos : 0 < b := hu_pos.trans_le hu.2
  have htu : t / b ≤ t / u :=
    div_le_div_of_nonneg_left ht hu_pos hu.2
  rw [weightedPoissonVelocity_neg_nat]
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem right_endpoint_gap_le_abs_weightedPoissonVelocity_neg_nat
    {a b t u : ℝ} {m : ℕ}
    (ha : 0 < a) (ht : 0 ≤ t) (hu : u ∈ Icc a b)
    (hmright : t / a ≤ 2 * Real.pi * (m : ℝ)) :
    2 * Real.pi * (m : ℝ) - t / a ≤
      |weightedPoissonVelocity t (-(m : ℤ)) u| := by
  have hu_pos : 0 < u := ha.trans_le hu.1
  have htu : t / u ≤ t / a :=
    div_le_div_of_nonneg_left ht ha hu.1
  rw [weightedPoissonVelocity_neg_nat]
  rw [abs_of_nonneg (by linarith)]
  linarith

end AFE
end HardyTheorem
