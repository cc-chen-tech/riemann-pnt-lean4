import PrimeNumberTheorem.WeightedHilbertKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- Reflecting a real weight reflects its Fourier kernel frequency. -/
theorem fourierKernel_reflect (g : ℝ → ℝ) (xi : ℝ) :
    fourierKernel (fun t => g (-t)) xi = fourierKernel g (-xi) := by
  let F : ℝ → ℂ := fun y =>
    (g y : ℂ) * Complex.exp
      (Complex.I * (-(xi : ℂ) * (y : ℂ)))
  unfold fourierKernel
  calc
    (∫ t, (g (-t) : ℂ) * Complex.exp (Complex.I * (xi * t))) =
        ∫ t, F ((-1 : ℝ) * t) := by
      congr 1
      funext t
      simp only [F, neg_one_mul]
      congr 2
      push_cast
      ring
    _ = |((-1 : ℝ)⁻¹)| • ∫ y, F y :=
      Measure.integral_comp_mul_left F (-1)
    _ = ∫ y, F y := by norm_num
    _ = ∫ t, (g t : ℂ) * Complex.exp
        (Complex.I * (((-xi : ℝ) : ℂ) * (t : ℂ))) := by
      simp only [F, Complex.ofReal_neg]

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

/-- Reflection preserves positivity and scale monotonicity while reversing the
sign of the reciprocal-frequency Fourier coefficient. -/
def PositiveHilbertKernelProfile.reflect {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa) :
    PositiveHilbertKernelProfile C (-kappa) where
  kernel := fun t => profile.kernel (-t)
  integrable_kernel := by
    simpa only [neg_one_mul] using
      profile.integrable_kernel.comp_mul_left'
        (by norm_num : (-1 : ℝ) ≠ 0)
  kernel_nonneg := fun t => profile.kernel_nonneg (-t)
  dilation_antitone := by
    intro deltaSmall deltaLarge hsmall hle t
    simpa only [mul_neg] using
      profile.dilation_antitone hsmall hle (-t)
  fourierKernel_zero := by
    rw [fourierKernel_reflect, neg_zero]
    exact profile.fourierKernel_zero
  fourierKernel_of_one_le_abs := by
    intro xi hxi
    have hxi_neg : 1 ≤ |-xi| := by simpa only [abs_neg] using hxi
    have hxi_pos : 0 < |xi| := zero_lt_one.trans_le hxi
    have hxi_ne : xi ≠ 0 := abs_pos.mp hxi_pos
    rw [fourierKernel_reflect,
      profile.fourierKernel_of_one_le_abs hxi_neg]
    push_cast
    field_simp [hxi_ne]

/-- The exact real-line properties of the Carneiro--Littmann majorant error in
the paper's Fourier normalization, translated to this file's `+i xi x`
convention.  Constructing an inhabitant from the explicit extremal function is
the remaining analytic step. -/
structure CarneiroLittmannKernel where
  kernel : ℝ → ℝ
  integrable_kernel : Integrable kernel
  kernel_nonneg : ∀ t, 0 ≤ kernel t
  dilation_antitone : ∀ {deltaSmall deltaLarge : ℝ},
    0 < deltaSmall → deltaSmall ≤ deltaLarge → ∀ t,
      kernel (deltaLarge * t) ≤ kernel (deltaSmall * t)
  fourierKernel_zero : fourierKernel kernel 0 = (2 : ℂ)
  fourierKernel_of_two_pi_le_abs : ∀ {xi : ℝ},
    2 * Real.pi ≤ |xi| →
      fourierKernel kernel xi = (-2 * Complex.I) / xi

/-- Rescaling the paper's kernel by `(2 pi)⁻¹` moves its Fourier threshold from
`2 pi` to one.  Its mass becomes `4 pi`, so the weighted Hilbert constant is
`C = 2 pi`. -/
noncomputable def CarneiroLittmannKernel.normalizedProfile
    (kernel : CarneiroLittmannKernel) :
    PositiveHilbertKernelProfile (2 * Real.pi) (-2 * Complex.I) where
  kernel := fun t => kernel.kernel ((2 * Real.pi)⁻¹ * t)
  integrable_kernel := by
    exact kernel.integrable_kernel.comp_mul_left'
      (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  kernel_nonneg := fun t => kernel.kernel_nonneg ((2 * Real.pi)⁻¹ * t)
  dilation_antitone := by
    intro deltaSmall deltaLarge hsmall hle t
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      kernel.dilation_antitone hsmall hle ((2 * Real.pi)⁻¹ * t)
  fourierKernel_zero := by
    have hscale : 0 < (2 * Real.pi)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
    rw [fourierKernel_scale_pos hscale]
    simp only [zero_div, kernel.fourierKernel_zero, inv_inv]
    push_cast
    ring
  fourierKernel_of_one_le_abs := by
    intro xi hxi
    have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hscale : 0 < (2 * Real.pi)⁻¹ := inv_pos.mpr htwoPi
    have hraw : 2 * Real.pi ≤ |xi / (2 * Real.pi)⁻¹| := by
      rw [abs_div, abs_of_pos hscale]
      apply (le_div_iff₀ hscale).2
      rw [mul_inv_cancel₀ htwoPi.ne']
      exact hxi
    have hxi_pos : 0 < |xi| := zero_lt_one.trans_le hxi
    have hxi_ne : xi ≠ 0 := abs_pos.mp hxi_pos
    rw [fourierKernel_scale_pos hscale,
      kernel.fourierKernel_of_two_pi_le_abs hraw]
    push_cast
    field_simp [htwoPi.ne', hxi_ne]

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

/-- Reflection supplies the opposite high-frequency sign, so one concrete
positive profile is enough for the finite weighted mean-square estimate. -/
theorem finiteExponentialSum_meanSquare_le_of_scaled_positive_kernel
    {N : ℕ} {c : ℕ → ℂ} {omega delta : ℕ → ℝ} {a b C : ℝ}
    (hab : a ≤ b)
    (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n)
    (hlocal : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|)
    (profile : PositiveHilbertKernelProfile C (-2 * Complex.I)) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ Finset.range N, (delta n)⁻¹ * ‖c n‖ ^ 2 := by
  have profilePlus : PositiveHilbertKernelProfile C (2 * Complex.I) := by
    simpa only [neg_mul, neg_neg] using profile.reflect
  exact finiteExponentialSum_meanSquare_le_of_scaled_positive_kernels
    hab hdelta hanti hlocal profile profilePlus

/-- The paper-normalized Carneiro--Littmann kernel gives the concrete
`2 pi` weighted Hilbert constant, hence a `4 pi` finite mean-square error. -/
theorem finiteExponentialSum_meanSquare_le_of_carneiroLittmannKernel
    {N : ℕ} {c : ℕ → ℂ} {omega delta : ℕ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n)
    (hlocal : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|)
    (kernel : CarneiroLittmannKernel) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        4 * Real.pi *
          ∑ n ∈ Finset.range N, (delta n)⁻¹ * ‖c n‖ ^ 2 := by
  have h := finiteExponentialSum_meanSquare_le_of_scaled_positive_kernel
    (c := c) (omega := omega) (delta := delta)
    hab hdelta hanti hlocal kernel.normalizedProfile
  convert h using 1
  ring

end DirichletPolynomial
end PrimeNumberTheorem
