import HardyTheorem.AFEExplicitPoissonInnerMode
import HardyTheorem.AFEExplicitPoissonZeroMode
import HardyTheorem.AFECriticalGammaFrequency

/-! Critical-line zero mode and the two retained endpoint Gamma terms. -/

open Complex

namespace HardyTheorem.AFE

theorem poissonGammaTerm_critical_eq (t : ℝ) (m : ℕ) :
    poissonGammaTerm (1 / 2) t m = criticalGammaFrequencyTerm t m := by
  norm_num [poissonGammaTerm, criticalGammaFrequencyTerm]

/-- The two Gamma frequencies not covered by the inner-band replacement
have a uniform square-root bound. -/
theorem sum_norm_poissonGammaTerm_two_endpoints_le (t : ℝ) {K : ℕ} (hK : 6 ≤ K) :
    (∑ m ∈ Finset.Icc (K - 1) K, ‖poissonGammaTerm (1 / 2) t m‖) ≤
      4 * (K : ℝ) ^ (-(1 / 2) : ℝ) := by
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have hcard : (Finset.Icc (K - 1) K).card = 2 := by rw [Nat.card_Icc]; omega
  have hpoint (m : ℕ) (hm : m ∈ Finset.Icc (K - 1) K) :
      ‖poissonGammaTerm (1 / 2) t m‖ ≤ 2 * (K : ℝ) ^ (-(1 / 2) : ℝ) := by
    have hmK : (K : ℝ) - 1 ≤ (m : ℝ) := by
      have h : ((K - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      simpa only [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one] using h
    have hm0 : 0 < (m : ℝ) := by linarith
    have hfour : (4 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 := by
      norm_num [Real.rpow_neg, ← Real.sqrt_eq_rpow]
    calc
      _ ≤ (m : ℝ) ^ (-(1 / 2) : ℝ) := by
        rw [poissonGammaTerm_critical_eq]
        exact norm_criticalGammaFrequencyTerm_le t hm0
      _ ≤ ((K : ℝ) / 4) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
      _ = (K : ℝ) ^ (-(1 / 2) : ℝ) / (4 : ℝ) ^ (-(1 / 2) : ℝ) :=
        Real.div_rpow (by positivity) (by norm_num) _
      _ = _ := by rw [hfour]; ring
  calc
    _ ≤ ∑ _m ∈ Finset.Icc (K - 1) K, 2 * (K : ℝ) ^ (-(1 / 2) : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring

/-- At square-root height the lower Mellin boundary costs at most one
additional `K^(-1/2)`; the upper-cutoff error still tends to zero. -/
theorem norm_explicitPoissonZeroMode_critical_sqrt_sub_main_le
    {N t : ℝ} {K : ℕ} (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    ‖explicitPoissonMode (1 / 2) ((K : ℝ) + 1) N t 0 -
        (N : ℂ) ^ (1 - s) / (1 - s)‖ ≤
      2 * (K : ℝ) ^ (-(1 / 2) : ℝ) + N ^ (-(1 / 2) : ℝ) := by
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : 0 < (K : ℝ) := by linarith
  have ht0 : 0 < t := (show 0 < 2 * Real.pi * (K : ℝ) ^ 2 by positivity).trans_le htL
  have htK : (K : ℝ) ^ 2 ≤ t := by
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hscaled : (K : ℝ) ^ 2 ≤ 2 * Real.pi * (K : ℝ) ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (sq_nonneg (K : ℝ))
    exact hscaled.trans htL
  have hroot : Real.sqrt K ≤ (K : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hrootPlus : Real.sqrt ((K : ℝ) + 1) ≤ (K : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨hK0.le, by nlinarith⟩
  have hprod : Real.sqrt ((K : ℝ) + 1) * Real.sqrt K ≤ t := by
    calc
      _ ≤ (K : ℝ) * K := mul_le_mul hrootPlus hroot (Real.sqrt_nonneg _) hK0.le
      _ ≤ t := by nlinarith [htK]
  have hboundary : ((K : ℝ) + 1) ^ (1 - (1 / 2 : ℝ)) / t ≤
      (K : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, Real.rpow_neg hK0.le, ← Real.sqrt_eq_rpow]
    apply (div_le_iff₀ ht0).2
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ (Real.sqrt_pos.mpr hK0)).2 hprod
  have h := norm_explicitPoissonZeroMode_sub_main_le (sigma := (1 / 2 : ℝ))
    (by norm_num) (show 1 < (K : ℝ) + 1 by linarith)
    (show (K : ℝ) + 1 ≤ N by linarith) ht0
  simp only [show (K : ℝ) + 1 - 1 = (K : ℝ) by ring] at h
  have h' := h.trans (add_le_add le_rfl hboundary)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h'
  exact h'.trans_eq (by ring)

end HardyTheorem.AFE
