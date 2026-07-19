import PrimeNumberTheorem.WeightedHilbertKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- A normalized positive Fourier kernel for the weighted Hilbert inequality.
The high-frequency formula begins at frequency one; positive dilation moves
that threshold to the local separation scale. -/
structure PositiveHilbertKernelProfile (C : ℝ) (kappa : ℂ) where
  kernel : ℝ → ℝ
  integrable_kernel : Integrable kernel
  kernel_nonneg : ∀ t, 0 ≤ kernel t
  dilation_antitone : ∀ {deltaSmall deltaLarge : ℝ},
    0 < deltaSmall → deltaSmall ≤ deltaLarge → ∀ t,
      kernel (deltaLarge * t) ≤ kernel (deltaSmall * t)
  fourierKernel_zero :
    fourierKernel kernel 0 = ((2 * C : ℝ) : ℂ)
  fourierKernel_of_one_le_abs : ∀ {xi : ℝ}, 1 ≤ |xi| →
    fourierKernel kernel xi = kappa / xi

/-- The kernel profile dilated by the local scale at index `n`. -/
def scaledKernelSequence {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    (delta : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  profile.kernel (delta n * t)

/-- Positive dilation preserves integrability of a kernel profile. -/
theorem integrable_scaledKernelSequence {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    {delta : ℕ → ℝ} {n : ℕ} (hdelta : 0 < delta n) :
    Integrable (scaledKernelSequence profile delta n) := by
  simpa only [scaledKernelSequence] using
    profile.integrable_kernel.comp_mul_left' hdelta.ne'

/-- Every member of a scaled positive-kernel sequence is nonnegative. -/
theorem scaledKernelSequence_nonneg {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    {delta : ℕ → ℝ} {n : ℕ} {t : ℝ} :
    0 ≤ scaledKernelSequence profile delta n t := by
  exact profile.kernel_nonneg (delta n * t)

/-- Decreasing local scales produce a pointwise increasing kernel sequence. -/
theorem scaledKernelSequence_mono {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    {delta : ℕ → ℝ} (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n) (n : ℕ) (t : ℝ) :
    scaledKernelSequence profile delta n t ≤
      scaledKernelSequence profile delta (n + 1) t := by
  exact profile.dilation_antitone (hdelta (n + 1)) (hanti n) t

/-- The zero-frequency mass of a scaled profile has reciprocal-scale weight. -/
theorem fourierKernel_scaledKernelSequence_zero {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    {delta : ℕ → ℝ} {n : ℕ} (hdelta : 0 < delta n) :
    fourierKernel (scaledKernelSequence profile delta n) 0 =
      ((2 * C * (delta n)⁻¹ : ℝ) : ℂ) := by
  unfold scaledKernelSequence
  rw [fourierKernel_scale_pos hdelta]
  simp only [zero_div, profile.fourierKernel_zero]
  push_cast
  ring

/-- Once a frequency exceeds the local scale, dilation preserves the
reciprocal-frequency Fourier formula. -/
theorem fourierKernel_scaledKernelSequence_of_large_frequency
    {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    {delta : ℕ → ℝ} {n : ℕ} {xi : ℝ}
    (hdelta : 0 < delta n) (hlarge : delta n ≤ |xi|) :
    fourierKernel (scaledKernelSequence profile delta n) xi = kappa / xi := by
  have hscaled : 1 ≤ |xi / delta n| := by
    rw [abs_div, abs_of_pos hdelta]
    exact (le_div_iff₀ hdelta).2 (by simpa using hlarge)
  have hxi_abs : 0 < |xi| := hdelta.trans_le hlarge
  have hxi : xi ≠ 0 := abs_pos.mp hxi_abs
  unfold scaledKernelSequence
  rw [fourierKernel_scale_pos hdelta,
    profile.fourierKernel_of_one_le_abs hscaled]
  push_cast
  field_simp [hdelta.ne', hxi]

/-- Two normalized positive profiles and local frequency separation yield the
finite weighted Montgomery--Vaughan mean-square estimate.  The construction
of concrete extremal profiles is deliberately kept outside this theorem. -/
theorem finiteExponentialSum_meanSquare_le_of_scaled_positive_kernels
    {N : ℕ} {c : ℕ → ℂ} {omega delta : ℕ → ℝ} {a b C : ℝ}
    (hab : a ≤ b)
    (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n)
    (hlocal : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|)
    (profileMinus : PositiveHilbertKernelProfile C (-2 * Complex.I))
    (profilePlus : PositiveHilbertKernelProfile C (2 * Complex.I)) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ Finset.range N, (delta n)⁻¹ * ‖c n‖ ^ 2 := by
  have homega : Set.InjOn omega (Finset.range N : Set ℕ) := by
    intro m hm n hn heq
    by_contra hmn
    have hsep := hlocal m hm n hn hmn
    rw [heq, sub_self, abs_zero] at hsep
    exact (not_le_of_gt (hdelta (min m n))) hsep
  apply finiteExponentialSum_meanSquare_le_of_positive_kernelSequences
    (gMinus := scaledKernelSequence profileMinus delta)
    (gPlus := scaledKernelSequence profilePlus delta)
    (weight := fun n => (delta n)⁻¹) hab homega
  · intro n hn
    exact (inv_nonneg.mpr (hdelta n).le)
  · intro j
    exact integrable_scaledKernelSequence profileMinus (hdelta j)
  · intro t
    exact scaledKernelSequence_nonneg profileMinus
  · exact scaledKernelSequence_mono profileMinus hdelta hanti
  · intro n hn
    exact fourierKernel_scaledKernelSequence_zero profileMinus (hdelta n)
  · intro m hm n hn hmn
    simpa only [ofReal_sub] using
      (fourierKernel_scaledKernelSequence_of_large_frequency
        profileMinus (hdelta (min m n)) (hlocal m hm n hn hmn))
  · intro j
    exact integrable_scaledKernelSequence profilePlus (hdelta j)
  · intro t
    exact scaledKernelSequence_nonneg profilePlus
  · exact scaledKernelSequence_mono profilePlus hdelta hanti
  · intro n hn
    exact fourierKernel_scaledKernelSequence_zero profilePlus (hdelta n)
  · intro m hm n hn hmn
    simpa only [ofReal_sub] using
      (fourierKernel_scaledKernelSequence_of_large_frequency
        profilePlus (hdelta (min m n)) (hlocal m hm n hn hmn))

end DirichletPolynomial
end PrimeNumberTheorem
