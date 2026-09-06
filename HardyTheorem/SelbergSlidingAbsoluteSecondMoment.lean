import HardyTheorem.SelbergGlobalFourierMass
import MathlibAux.AbsoluteSlidingWindowL2

open Complex MeasureTheory Set
open scoped Interval

namespace HardyTheorem

/-! # Selberg S3 absolute sliding second moment -/

/-- Selberg S3b: the global second moment of the absolute mass in a window
of length `H` has the exact `H²` loss over the S3a global square mass. -/
theorem exists_integral_sq_abs_selbergCompletedMollifiedF_sliding_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta H : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log (delta ^ (-2 : ℝ)) → 0 ≤ H →
        (∫ t : ℝ,
          (∫ u in t..t + H,
            ‖selbergCompletedMollifiedFComplex delta X u‖) ^ 2) ≤
          C * (H ^ 2 *
            (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
              Real.log (X : ℝ))) := by
  rcases exists_integral_normSq_selbergCompletedMollifiedF_global_le
    ha hc hcEight hac with ⟨C, hC, hglobal⟩
  refine ⟨C, hC, ?_⟩
  intro X delta H hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo hH
  have hwindow := MathlibAux.integral_sq_abs_slidingWindow_le
    (memLp_two_selbergCompletedMollifiedF_complex hdelta hdeltaPi X) hH
  calc
    (∫ t : ℝ,
        (∫ u in t..t + H,
          ‖selbergCompletedMollifiedFComplex delta X u‖) ^ 2) ≤
        H ^ 2 *
          ∫ u : ℝ, ‖selbergCompletedMollifiedFComplex delta X u‖ ^ 2 :=
      hwindow
    _ ≤ H ^ 2 *
        (C * (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
          Real.log (X : ℝ))) := by
      gcongr
      exact hglobal X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
    _ = C * (H ^ 2 *
        (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
          Real.log (X : ℝ))) := by ring

end HardyTheorem
