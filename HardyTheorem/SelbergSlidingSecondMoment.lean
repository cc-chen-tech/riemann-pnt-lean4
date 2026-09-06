import HardyTheorem.SelbergFourierEnergyTransport
import MathlibAux.SlidingIntegralFourierEnergy

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace HardyTheorem

set_option maxHeartbeats 800000

/-! # Selberg S2: the genuine sliding signed-mass second moment -/

theorem exists_integral_normSq_sliding_selbergCompletedMollifiedF_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta u v : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) → u ≤ v →
        (∫ t in u..v,
          Complex.normSq
            (∫ z in t..t +
                (2 * Real.pi / Real.log ((X : ℝ) ^ a)),
              selbergCompletedMollifiedFComplex delta X z)) ≤
          C * ((2 * Real.pi / Real.log ((X : ℝ) ^ a)) *
            delta ^ (-(1 / 2 : ℝ)) / Real.log (X : ℝ)) := by
  rcases exists_integral_normSq_selbergExplicitInverseFourierKernel_low_le
    ha hc hcEight hac with ⟨CL, hCL, hLow⟩
  rcases exists_integral_normSq_selbergExplicitInverseFourierKernel_high_le
    ha hc hcEight hac with ⟨CH, hCH, hHigh⟩
  refine ⟨4 * Real.pi * CL + 16 * Real.pi * CH, by positivity, ?_⟩
  intro X delta u v hdelta hdelta1 hX hdeltaPi hXexp hXpow hLtwo huv
  let L : ℝ := Real.log ((X : ℝ) ^ a)
  let D : ℝ := delta ^ (-(1 / 2 : ℝ))
  let H : ℝ := 2 * Real.pi / L
  let A : ℝ := 1 / H
  let F : ℝ → ℂ := selbergCompletedMollifiedFComplex delta X
  let hF2 : MemLp F 2 :=
    memLp_two_selbergCompletedMollifiedF_complex hdelta hdeltaPi X
  have hL : 0 < L := by dsimp [L]; linarith
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hH : 0 < H := by dsimp [H]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsplit : (2 * Real.pi) * A = L := by
    dsimp [A, H]
    field_simp [hL.ne', Real.pi_ne_zero]
  have hslide := MathlibAux.integral_normSq_slidingIntegral_le_fourier_low_high
    (integrable_selbergCompletedMollifiedF_complex hdelta hdeltaPi X)
    hF2 hH huv
  have hLowEq := integral_normSq_selbergFourierLp_abs_le_eq
    hdelta hdeltaPi X hA
  have hHighEq := integral_normSq_selbergFourierLp_abs_gt_eq
    hdelta hdeltaPi X hA
  rw [hsplit] at hLowEq hHighEq
  have hLowBound :
      (∫ y in Ioc 0 L,
        Complex.normSq
          (selbergExplicitInverseFourierKernel delta X y)) ≤
        CL * (D * L / Real.log (X : ℝ)) := by
    simpa only [L, D] using hLow X delta hdelta hdelta1 hX hdeltaPi
      hXexp hXpow hLtwo
  have hHighBound :
      (∫ y in Ioi L,
        Complex.normSq
            (selbergExplicitInverseFourierKernel delta X y) / y ^ 2) ≤
        CH * (D / (L * Real.log (X : ℝ))) := by
    simpa only [L, D] using hHigh X delta hdelta hdelta1 hX hdeltaPi
      hXexp hXpow hLtwo
  calc
    (∫ t in u..v,
        Complex.normSq
          (∫ z in t..t +
              (2 * Real.pi / Real.log ((X : ℝ) ^ a)),
            selbergCompletedMollifiedFComplex delta X z)) ≤
      H ^ 2 * (∫ w : ℝ in {w | |w| ≤ 1 / H},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w‖ ^ 2) +
      4 * (∫ w : ℝ in {w | 1 / H < |w|},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w‖ ^ 2 / w ^ 2) := by
        simpa only [H, F, hF2] using hslide
    _ = H ^ 2 *
          (2 * ∫ y in Ioc 0 L,
            Complex.normSq
              (selbergExplicitInverseFourierKernel delta X y)) +
        4 * ((8 * Real.pi ^ 2) *
          ∫ y in Ioi L,
            Complex.normSq
              (selbergExplicitInverseFourierKernel delta X y) / y ^ 2) := by
      rw [hLowEq, hHighEq]
    _ ≤ H ^ 2 * (2 * (CL * (D * L / Real.log (X : ℝ)))) +
        4 * ((8 * Real.pi ^ 2) *
          (CH * (D / (L * Real.log (X : ℝ))))) := by
      gcongr
    _ = (4 * Real.pi * CL + 16 * Real.pi * CH) *
        ((2 * Real.pi / Real.log ((X : ℝ) ^ a)) *
          delta ^ (-(1 / 2 : ℝ)) / Real.log (X : ℝ)) := by
      dsimp [H, L, D]
      field_simp [hL.ne', hlogX.ne']
      ring

end HardyTheorem
