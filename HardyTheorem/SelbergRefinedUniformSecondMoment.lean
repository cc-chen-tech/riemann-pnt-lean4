import HardyTheorem.SelbergRefinedUniformFourierMass
import HardyTheorem.SelbergFourierEnergyTransport
import MathlibAux.SlidingIntegralFourierEnergy

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace HardyTheorem

set_option maxHeartbeats 800000

/-!
# Refined Selberg S2, uniform in the short-window exponent

After the exact Fourier normalization, the residue contributes the explicit
lower-order term `20 * H^2 * X^4`.  All dependence on the nonconstant kernel
is contained in one coefficient independent of `a ∈ (0,1]`.
-/

/-- The refined sliding signed second moment.  Its nonconstant coefficient is
uniform for every `0 < a ≤ 1`, while the residue is retained explicitly. -/
theorem exists_integral_normSq_sliding_selbergCompletedMollifiedF_le_refined_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (X : ℕ) (delta u v : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-(1 / 32 : ℝ)) →
        2 ≤ Real.log ((X : ℝ) ^ a) → u ≤ v →
        let H := 2 * Real.pi / Real.log ((X : ℝ) ^ a)
        (∫ t in u..v,
          Complex.normSq
            (∫ z in t..t + H,
              selbergCompletedMollifiedFComplex delta X z)) ≤
          20 * (H ^ 2 * (X : ℝ) ^ 4) +
            C * (H * delta ^ (-(1 / 2 : ℝ)) /
              Real.log (X : ℝ)) := by
  obtain ⟨CL, hCL, hLow⟩ :=
    exists_integral_normSq_selbergExplicitInverseFourierKernel_low_le_refined_uniform
  obtain ⟨CH, hCH, hHigh⟩ :=
    exists_integral_normSq_selbergExplicitInverseFourierKernel_high_le_refined_uniform
  refine ⟨8 * Real.pi * CL + 32 * Real.pi * CH, by positivity, ?_⟩
  intro a ha haOne X delta u v hdelta hdeltaOne hX hdeltaPi hXexp hXpow
    hLtwo huv
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
        2 * (X : ℝ) ^ 4 +
          2 * CL * (D * L / Real.log (X : ℝ)) := by
    simpa only [L, D] using hLow a ha haOne X delta hdelta hdeltaOne hX
      hdeltaPi hXexp hXpow hLtwo
  have hHighBound :
      (∫ y in Ioi L,
        Complex.normSq
            (selbergExplicitInverseFourierKernel delta X y) / y ^ 2) ≤
        2 * (X : ℝ) ^ 4 / L ^ 2 +
          2 * CH * (D / (L * Real.log (X : ℝ))) := by
    simpa only [L, D] using hHigh a ha haOne X delta hdelta hdeltaOne hX
      hdeltaPi hXexp hXpow hLtwo
  dsimp only
  calc
    (∫ t in u..v,
        Complex.normSq
          (∫ z in t..t + H,
            selbergCompletedMollifiedFComplex delta X z)) ≤
      H ^ 2 * (∫ w : ℝ in {w | |w| ≤ 1 / H},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w‖ ^ 2) +
      4 * (∫ w : ℝ in {w | 1 / H < |w|},
        ‖(𝓕 (hF2.toLp F) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) w‖ ^ 2 / w ^ 2) := by
        simpa only [F, hF2] using hslide
    _ = H ^ 2 *
          (2 * ∫ y in Ioc 0 L,
            Complex.normSq
              (selbergExplicitInverseFourierKernel delta X y)) +
        4 * ((8 * Real.pi ^ 2) *
          ∫ y in Ioi L,
            Complex.normSq
              (selbergExplicitInverseFourierKernel delta X y) / y ^ 2) := by
      rw [hLowEq, hHighEq]
    _ ≤ H ^ 2 *
          (2 * (2 * (X : ℝ) ^ 4 +
            2 * CL * (D * L / Real.log (X : ℝ)))) +
        4 * ((8 * Real.pi ^ 2) *
          (2 * (X : ℝ) ^ 4 / L ^ 2 +
            2 * CH * (D / (L * Real.log (X : ℝ))))) := by
      gcongr
    _ = 20 * (H ^ 2 * (X : ℝ) ^ 4) +
        (8 * Real.pi * CL + 32 * Real.pi * CH) *
          (H * D / Real.log (X : ℝ)) := by
      dsimp [H]
      field_simp [hL.ne', hlogX.ne']
      ring

end HardyTheorem
