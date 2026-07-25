import MathlibAux.SlidingRegionSwap
import MathlibAux.SlidingWindowBadSet

open Complex MeasureTheory Set ComplexConjugate
open scoped BigOperators

namespace MathlibAux

/-!
# Lag identity for signed sliding masses

For a continuous real-valued function `F`, the second moment of its signed
sliding mass over `[A, B]` is a triangular lag integral of translated
autocorrelations.  This isolates the measure-theoretic Fubini and
change-of-variables argument from any particular analytic-number-theory
function.
-/

/-- The second moment of a continuous signed sliding mass equals its
translated-autocorrelation integral over the square displacement window. -/
theorem integral_sq_slidingWindowMass_eq_correlation
    {F : ℝ → ℝ} (hF : Continuous F) {A B H : ℝ}
    (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (slidingWindowMass F H t) ^ 2) =
      ∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
        F x * F (x + (w - v)) := by
  have hFc : Continuous (fun t : ℝ => (F t : ℂ)) :=
    Complex.continuous_ofReal.comp hF
  have hk := slidingIntervalCorrelation_kernel hFc hFc hAB hH
  have hI : ∀ t : ℝ,
      (∫ v in 0..H, (F (t + v) : ℂ)) =
        (slidingWindowMass F H t : ℂ) := by
    intro t
    rw [intervalIntegral.integral_ofReal]
    congr 1
    have hcomp :
        (∫ v in 0..H, F (t + v)) =
          ∫ v in 0..H, F (v + t) := by
      apply intervalIntegral.integral_congr
      intro v _hv
      dsimp only
      rw [add_comm]
    rw [hcomp, intervalIntegral.integral_comp_add_right, zero_add,
      add_comm H t]
    rfl
  have hpoint : ∀ t : ℝ,
      conj (∫ v in 0..H, (F (t + v) : ℂ)) *
          (∫ w in 0..H, (F (t + w) : ℂ)) =
        (((slidingWindowMass F H t) ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [hI t]
    simp [pow_two]
  have hmain :
      (∫ t in A..B,
          conj (∫ v in 0..H, (F (t + v) : ℂ)) *
            (∫ w in 0..H, (F (t + w) : ℂ))) =
        ((∫ t in A..B, (slidingWindowMass F H t) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hpoint t
  have htri :
      (∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
          conj (F x : ℂ) * (F (x + (w - v)) : ℂ)) =
        ((∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
          F x * F (x + (w - v)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro v _hv
    dsimp only
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro w _hw
    dsimp only
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only
    simp
  exact Complex.ofReal_injective (hmain.symm.trans (hk.trans htri))

/-- For continuous `F`, the squared signed sliding mass on `[A, B]` equals a
triangular lag integral of translated autocorrelations.  At lag
`τ ∈ [-H, H]`, the displacement variable ranges from `max 0 (-τ)` to
`min H (H - τ)`. -/
theorem integral_sq_slidingWindowMass_eq_lagIntegral
    {F : ℝ → ℝ} (hF : Continuous F) {A B H : ℝ}
    (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (slidingWindowMass F H t) ^ 2) =
      ∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ),
        ∫ x in A + v..B + v, F x * F (x + τ) := by
  let Φ : ℝ → ℝ → ℝ := fun v τ =>
    ∫ x in A + v..B + v, F x * F (x + τ)
  have hΦrw : ∀ v τ : ℝ,
      Φ v τ = ∫ y in A..B, F (y + v) * F (y + v + τ) := by
    intro v τ
    exact (intervalIntegral.integral_comp_add_right
      (fun x => F x * F (x + τ)) v).symm
  have hΦcont : Continuous (Function.uncurry Φ) := by
    have hcont : Continuous (Function.uncurry (fun v τ : ℝ =>
        ∫ y in A..B, F (y + v) * F (y + v + τ))) := by
      have hIntegrand : Continuous
          (Function.uncurry (fun (p : ℝ × ℝ) (y : ℝ) =>
            F (y + p.1) * F (y + p.1 + p.2))) :=
        (hF.comp (continuous_snd.add
          (continuous_fst.comp continuous_fst))).mul
          (hF.comp ((continuous_snd.add
            (continuous_fst.comp continuous_fst)).add
            (continuous_snd.comp continuous_fst)))
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) hIntegrand A B
    rw [show Function.uncurry Φ =
        Function.uncurry (fun v τ : ℝ =>
          ∫ y in A..B, F (y + v) * F (y + v + τ)) from
      funext fun p => hΦrw p.1 p.2]
    exact hcont
  rw [integral_sq_slidingWindowMass_eq_correlation hF hAB hH]
  exact intervalIntegral_pair_sub_eq_lagIntegral hΦcont hH

end MathlibAux
