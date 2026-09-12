import PrimeNumberTheorem.MWKFCubicEulerLocalUniform
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Analyticity of each prime-local cubic Euler correction

The constant prime base lies in the complex slit plane, so its complex power
is analytic in the three exponent variables.  The strip condition keeps the
two rational denominators nonzero.
-/

/-- Every prime-local correction factor is Fréchet analytic on the open strip
whenever `eta < 1/2`. -/
theorem analyticOnNhd_mwkfPrimeCorrectionFactor_openStrip
    (p : Nat.Primes) {eta : ℝ} (hetaHalf : eta < 1 / 2) :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ ↦
        mwkfPrimeCorrectionFactor p z.1 z.2.1 z.2.2)
      (mwkfEulerOpenStrip eta) := by
  let A : ℂ × ℂ × ℂ → ℂ := fun z ↦
    (p : ℂ) ^ (-(1 + z.1 + z.2.2))
  let B : ℂ × ℂ × ℂ → ℂ := fun z ↦
    (p : ℂ) ^ (-(1 + z.2.1 + z.2.2))
  let C : ℂ × ℂ × ℂ → ℂ := fun z ↦
    (p : ℂ) ^ (-(1 + z.1 + z.2.1))
  have hpSlit : (p : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    exact_mod_cast p.prop.pos
  have hs : AnalyticOnNhd ℂ (fun z : ℂ × ℂ × ℂ ↦ z.1)
      (mwkfEulerOpenStrip eta) := analyticOnNhd_fst
  have ht : AnalyticOnNhd ℂ (fun z : ℂ × ℂ × ℂ ↦ z.2.1)
      (mwkfEulerOpenStrip eta) := by
    intro z hz
    exact analyticAt_fst.comp analyticAt_snd
  have hw : AnalyticOnNhd ℂ (fun z : ℂ × ℂ × ℂ ↦ z.2.2)
      (mwkfEulerOpenStrip eta) := by
    intro z hz
    exact analyticAt_snd.comp analyticAt_snd
  have hpConst : AnalyticOnNhd ℂ (fun _ : ℂ × ℂ × ℂ ↦ (p : ℂ))
      (mwkfEulerOpenStrip eta) := analyticOnNhd_const
  have hA : AnalyticOnNhd ℂ A (mwkfEulerOpenStrip eta) := by
    dsimp [A]
    exact hpConst.cpow ((analyticOnNhd_const.add hs).add hw).neg
      (fun _ _ ↦ hpSlit)
  have hB : AnalyticOnNhd ℂ B (mwkfEulerOpenStrip eta) := by
    dsimp [B]
    exact hpConst.cpow ((analyticOnNhd_const.add ht).add hw).neg
      (fun _ _ ↦ hpSlit)
  have hC : AnalyticOnNhd ℂ C (mwkfEulerOpenStrip eta) := by
    dsimp [C]
    exact hpConst.cpow ((analyticOnNhd_const.add hs).add ht).neg
      (fun _ _ ↦ hpSlit)
  have hden : ∀ z ∈ mwkfEulerOpenStrip eta,
      (1 - A z) * (1 - B z) ≠ 0 := by
    intro z hz
    have hza : -eta ≤ z.1.re := hz.1.le
    have hzb : -eta ≤ z.2.1.re := hz.2.1.le
    have hzc : -eta ≤ z.2.2.re := hz.2.2.le
    have hANe : 1 - A z ≠ 0 := by
      intro hzero
      have hAOne : A z = 1 := (sub_eq_zero.mp hzero).symm
      have hnorm : ‖A z‖ ≤ (p : ℝ) ^ (-1 + 2 * eta) := by
        simpa [A] using norm_prime_cpow_neg_one_add_le p.prop hza hzc
      rw [hAOne, norm_one] at hnorm
      have hpOne : (p : ℝ) ^ (-1 + 2 * eta) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast p.prop.one_lt) (by linarith [hetaHalf])
      exact (not_le_of_gt hpOne) hnorm
    have hBNe : 1 - B z ≠ 0 := by
      intro hzero
      have hBOne : B z = 1 := (sub_eq_zero.mp hzero).symm
      have hnorm : ‖B z‖ ≤ (p : ℝ) ^ (-1 + 2 * eta) := by
        simpa [B] using norm_prime_cpow_neg_one_add_le p.prop hzb hzc
      rw [hBOne, norm_one] at hnorm
      have hpOne : (p : ℝ) ^ (-1 + 2 * eta) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast p.prop.one_lt) (by linarith [hetaHalf])
      exact (not_le_of_gt hpOne) hnorm
    exact mul_ne_zero hANe hBNe
  change AnalyticOnNhd ℂ
    (fun z : ℂ × ℂ × ℂ ↦
      (1 - A z - B z + C z) * (1 - C z) /
        ((1 - A z) * (1 - B z)))
    (mwkfEulerOpenStrip eta)
  exact (((analyticOnNhd_const.sub hA).sub hB).add hC).mul
      (analyticOnNhd_const.sub hC) |>.div
    ((analyticOnNhd_const.sub hA).mul (analyticOnNhd_const.sub hB))
    hden

end PrimeNumberTheorem.MWKFCubic
