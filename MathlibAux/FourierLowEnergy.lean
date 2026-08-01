import MathlibAux.SlidingWindowParseval

/-!
# Restricting Fourier energy

The square energy of the Fourier transform on a measurable frequency set is
at most its total energy.  Plancherel then identifies the latter with the
square energy of the original `L2` function.
-/

open FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace MathlibAux

/-- Fourier square energy restricted to a set is bounded by the total square
energy of the original `L2` function. -/
theorem integral_norm_sq_fourier_restrict_le
    (F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))
    (s : Set ℝ) :
    (∫ y : ℝ in s,
      ‖(𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) ≤
      ∫ t : ℝ, ‖F t‖ ^ 2 := by
  let Fhat : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) := 𝓕 F
  have hFhatMem : MemLp (fun y : ℝ => Fhat y) 2 :=
    MeasureTheory.Lp.memLp Fhat
  have hFhatInt : Integrable (fun y : ℝ => ‖Fhat y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFhatMem.1).mp hFhatMem
  calc
    (∫ y : ℝ in s, ‖Fhat y‖ ^ 2) ≤
        ∫ y : ℝ, ‖Fhat y‖ ^ 2 :=
      setIntegral_le_integral hFhatInt
        (Filter.Eventually.of_forall fun y => sq_nonneg ‖Fhat y‖)
    _ = ‖Fhat‖ ^ 2 := integral_norm_sq_coeFn_eq_norm_sq Fhat
    _ = ‖F‖ ^ 2 := by
      rw [show Fhat = 𝓕 F by rfl, MeasureTheory.Lp.norm_fourier_eq]
    _ = ∫ t : ℝ, ‖F t‖ ^ 2 :=
      (integral_norm_sq_coeFn_eq_norm_sq F).symm

/-- The low-frequency square energy used by the rectangular-window bound is
therefore controlled by the original total energy. -/
theorem integral_norm_sq_fourier_low_le
    (F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) (H : ℝ) :
    (∫ y : ℝ in {y | |y| ≤ 1 / H},
      ‖(𝓕 F : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) ≤
      ∫ t : ℝ, ‖F t‖ ^ 2 := by
  exact integral_norm_sq_fourier_restrict_le F
    {y | |y| ≤ 1 / H}

end MathlibAux
