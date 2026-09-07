import HardyTheorem.AFECriticalTwoCutoffBridge

/-!
# Insert the canonical AFE remainder bound on a two-cutoff window

This file remains conditional on `zeta_critical_afe_target`.  It replaces
the canonical remainder term in the local two-cutoff majorant by the explicit
uniform quantity obtained from `O(t^{-1/4})` and the elementary
`2 * sqrt X` mollifier bound.  Thus the only variable terms left on the
right are the two fixed finite-polynomial energies.
-/

open Complex Set

namespace HardyTheorem
namespace AFE

/-- Uniform squared remainder bound on a window with lower endpoint `L`. -/
noncomputable def criticalAfeRemainderWindowBound
    (R L : ℝ) (X : ℕ) : ℝ :=
  (R * L ^ (-1 / 4 : ℝ) * (2 * Real.sqrt X)) ^ 2

/-- Assuming the corrected square-root AFE target, there is one positive
constant controlling every local two-cutoff window.  No analytic hypothesis
other than the still-explicit AFE target is hidden in this theorem. -/
theorem normSq_criticalAfeProduct_le_twoCutoffEnergies_of_target
    (hAFE : zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ {L U t : ℝ}, 1 < L → t ∈ Icc L U →
      Real.sqrt (U / (2 * Real.pi)) <
          Real.sqrt (L / (2 * Real.pi)) + 1 →
      ∀ X : ℕ, 2 ≤ X →
      Complex.normSq
          (riemannZeta ((1 / 2 : ℂ) + I * t) *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
        3 *
          (criticalAfeFixedPolynomialEnergy (criticalAfeCutoff L) X t +
            criticalAfeFixedPolynomialEnergy (criticalAfeCutoff L + 1) X t +
            criticalAfeRemainderWindowBound R L X) := by
  obtain ⟨R, hR, hcanonical⟩ :=
    zeta_critical_afe_target_iff_canonical_remainder.mp hAFE
  refine ⟨R, hR, ?_⟩
  intro L U t hL ht hwidth X hX
  have hLpos : 0 < L := zero_lt_one.trans hL
  have htpos : 0 < t := hLpos.trans_le ht.1
  have hpow : t ^ (-1 / 4 : ℝ) ≤ L ^ (-1 / 4 : ℝ) := by
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
      hLpos htpos ht.1
  have hremt := hcanonical t (hL.trans_le ht.1)
  have hremL :
      ‖criticalAfeCanonicalRemainder t‖ ≤
        R * L ^ (-1 / 4 : ℝ) := by
    exact hremt.trans
      (mul_le_mul_of_nonneg_left hpow hR.le)
  have hRL : 0 ≤ R * L ^ (-1 / 4 : ℝ) := by positivity
  have hprod :
      ‖criticalAfeCanonicalRemainder t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
        (R * L ^ (-1 / 4 : ℝ)) * (2 * Real.sqrt X) := by
    rw [norm_mul]
    exact mul_le_mul hremL
      (norm_selbergMoebiusMollifier_criticalLine_le_two_sqrt hX t)
      (norm_nonneg _) hRL
  have hK :
      0 ≤ R * L ^ (-1 / 4 : ℝ) * (2 * Real.sqrt X) := by
    positivity
  have hremSq :
      Complex.normSq
          (criticalAfeCanonicalRemainder t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
        criticalAfeRemainderWindowBound R L X := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) hK).2 hprod
  have hbase := normSq_criticalAfeProduct_le_three_twoCutoffEnergies
    hLpos.le ht hwidth X
  unfold criticalAfeRemainderWindowBound at hremSq ⊢
  calc
    _ ≤ 3 *
        (criticalAfeFixedPolynomialEnergy (criticalAfeCutoff L) X t +
          criticalAfeFixedPolynomialEnergy (criticalAfeCutoff L + 1) X t +
          Complex.normSq
            (criticalAfeCanonicalRemainder t *
              selbergMoebiusMollifier X
                ((1 / 2 : ℂ) + I * t))) := hbase
    _ ≤ _ := by gcongr

end AFE
end HardyTheorem
