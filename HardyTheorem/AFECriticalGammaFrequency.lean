import HardyTheorem.AFECriticalGammaPrefactor
import HardyTheorem.FirstZetaApproximation

/-! A single unit phase for every positive Gamma frequency and every finite dual sum. -/

open Complex

namespace HardyTheorem.AFE

/-- The actual positive-frequency Gamma boundary value at critical height. -/
noncomputable def criticalGammaFrequencyTerm (t m : ℝ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + I * t
  ((2 * Real.pi * m : ℝ) : ℂ) ^ (s - 1) *
    (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))

private theorem criticalGammaFrequencyTerm_eq (t : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    criticalGammaFrequencyTerm t m =
      criticalGammaPrefactor t * (m : ℂ) ^ ((1 / 2 : ℂ) + I * t - 1) := by
  dsimp only [criticalGammaFrequencyTerm, criticalGammaPrefactor]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hm]
  ring

private theorem norm_criticalGammaPower (t : ℝ) {m : ℝ} (hm : 0 < m) :
    ‖(m : ℂ) ^ ((1 / 2 : ℂ) + I * t - 1)‖ = m ^ (-(1 / 2) : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hm]
  congr 1
  norm_num

/-- The endpoint-band Gamma term has exactly the required square-root scale. -/
theorem norm_criticalGammaFrequencyTerm_le (t : ℝ) {m : ℝ} (hm : 0 < m) :
    ‖criticalGammaFrequencyTerm t m‖ ≤ m ^ (-(1 / 2) : ℝ) := by
  rw [criticalGammaFrequencyTerm_eq t hm.le, norm_mul, norm_criticalGammaPower t hm]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hm.le _)
    (norm_criticalGammaPrefactor_pos_and_le_one t).2

/-- One phase works for every finite dual sum.  Its choice depends only on
height, never on the frequency or on the truncation length. -/
theorem exists_unitPhase_criticalGammaFrequency_sums (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    ∃ U : ℂ, ‖U‖ = 1 ∧ ∀ K : ℕ,
      ‖(∑ m ∈ Finset.Icc 1 K, criticalGammaFrequencyTerm t m) -
        U * (∑ m ∈ Finset.Icc 1 K, (m : ℂ) ^ (s - 1))‖ ≤
          2 * Real.sqrt K * Real.exp (-2 * Real.pi * t) := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  obtain ⟨U, hU, hclose⟩ := exists_unitPhase_close_criticalGammaPrefactor t
  refine ⟨U, hU, ?_⟩
  intro K
  let D : ℂ := ∑ m ∈ Finset.Icc 1 K, (m : ℂ) ^ (s - 1)
  have hD : ‖D‖ ≤ 2 * Real.sqrt K := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 K, ‖(m : ℂ) ^ (s - 1)‖ := norm_sum_le _ _
      _ = ∑ m ∈ Finset.Icc 1 K, (Real.sqrt m)⁻¹ := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm1 := (Finset.mem_Icc.mp hm).1
        have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
        calc
          _ = (m : ℝ) ^ (-(1 / 2) : ℝ) := by
            simpa only [Complex.ofReal_natCast, s] using norm_criticalGammaPower t hm0
          _ = _ := by rw [Real.rpow_neg hm0.le, ← Real.sqrt_eq_rpow]
      _ ≤ _ := sum_inv_sqrt_Icc_one_le_two_sqrt K
  have hsum : (∑ m ∈ Finset.Icc 1 K, criticalGammaFrequencyTerm t m) =
      criticalGammaPrefactor t * D := by
    calc
      _ = ∑ m ∈ Finset.Icc 1 K, criticalGammaPrefactor t * (m : ℂ) ^ (s - 1) := by
        apply Finset.sum_congr rfl
        intro m _
        simpa only [Complex.ofReal_natCast, s] using
          criticalGammaFrequencyTerm_eq t (Nat.cast_nonneg m)
      _ = _ := (Finset.mul_sum _ _ _).symm
  change ‖(∑ m ∈ Finset.Icc 1 K, criticalGammaFrequencyTerm t m) - U * D‖ ≤ _
  rw [hsum, ← sub_mul, norm_mul]
  calc
    _ ≤ Real.exp (-2 * Real.pi * t) * (2 * Real.sqrt K) :=
      mul_le_mul hclose hD (norm_nonneg D) (Real.exp_pos _).le
    _ = _ := by ring

end HardyTheorem.AFE
