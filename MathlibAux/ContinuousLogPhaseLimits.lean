import MathlibAux.ArgumentCrossing

/-!
# Phase limits of arbitrary continuous logarithms

A model logarithm and a chosen component logarithm differ by one constant
deck transformation on their connected overlap. Thus a finite phase limit
of the model transfers to the chosen logarithm, even when the curve vanishes
at the boundary and the real part of the logarithm diverges.
-/

open Complex Set Filter Topology

namespace MathlibAux

/-- A finite phase limit transfers by a constant integer deck shift. The
eventual overlap, not a logarithm value at the boundary, is what is needed. -/
theorem exists_int_tendsto_im_continuousLog
    {ell model : ℝ → ℂ} {a b alpha : ℝ} {F : Filter ℝ}
    (hab : a < b) (hell : ContinuousOn ell (Ioo a b))
    (hmodel : ContinuousOn model (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) = Complex.exp (model t))
    (hmem : Ioo a b ∈ F)
    (hlim : Tendsto (fun t => (model t).im) F (nhds alpha)) :
    ∃ k : ℤ, Tendsto (fun t => (ell t).im) F
      (nhds (alpha + ((k : ℂ) * (2 * Real.pi * I)).im)) := by
  have hmid : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  obtain ⟨k, hk⟩ := exists_int_continuousLogs_eq_add_two_pi_I hell hmodel hexp hmid
  refine ⟨k, (hlim.add_const _).congr' ?_⟩
  filter_upwards [hmem] with t ht
  simpa only [Complex.add_im] using (congrArg Complex.im (hk t ht)).symm

end MathlibAux
