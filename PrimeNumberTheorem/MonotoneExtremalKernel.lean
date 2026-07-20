import PrimeNumberTheorem.LocalSeparationKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- Reflection of a real weight negates the frequency in the Fourier kernel. -/
theorem fourierKernel_reflect (g : ℝ → ℝ) (xi : ℝ) :
    fourierKernel (fun t => g (-t)) xi = fourierKernel g (-xi) := by
  let F : ℝ → ℂ := fun y =>
    (g y : ℂ) * Complex.exp
      (Complex.I * (((-xi) * y : ℝ) : ℂ))
  unfold fourierKernel
  calc
    (∫ t, (g (-t) : ℂ) * Complex.exp (Complex.I * (xi * t))) =
        ∫ t, F ((-1 : ℝ) * t) := by
      congr 1
      funext t
      simp only [F, neg_mul, one_mul]
      congr 2
      push_cast
      ring
    _ = ∫ y, F y := by
      simpa using (Measure.integral_comp_mul_left F (-1))
    _ = ∫ y, (g y : ℂ) * Complex.exp
          (Complex.I * (((-xi : ℝ) : ℂ) * (y : ℂ))) := by
      congr 1
      funext y
      simp only [F]
      congr 2
      push_cast
      ring

/-- The analytic properties of the monotone Beurling--Selberg error profile
needed by the Fourier proof of the weighted Hilbert--Montgomery--Vaughan
inequality.  With the convention used by `fourierKernel`, the profile
`M - sgn` from Carneiro--Littmann has this normalization. -/
structure MonotoneExtremalKernelCertificate (psi : ℝ → ℝ) : Prop where
  integrable : Integrable psi
  nonnegative : ∀ t, 0 ≤ psi t
  fourier_zero : fourierKernel psi 0 = 2
  fourier_tail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
    fourierKernel psi xi = (-2 * Complex.I) / xi
  dilation_antitone : ∀ {deltaNew deltaOld : ℝ},
    0 < deltaNew → deltaNew ≤ deltaOld → ∀ t,
      psi (deltaOld * t) ≤ psi (deltaNew * t)

namespace MonotoneExtremalKernelCertificate

theorem integrable_reflection {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi) :
    Integrable (fun t => psi (-t)) := by
  simpa only [neg_one_mul] using
    hpsi.integrable.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)

theorem fourier_reflection_zero {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi) :
    fourierKernel (fun t => psi (-t)) 0 = 2 := by
  rw [fourierKernel_reflect, neg_zero, hpsi.fourier_zero]

theorem fourier_reflection_tail {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel (fun t => psi (-t)) xi =
      (2 * Complex.I) / xi := by
  have hneg : 2 * Real.pi ≤ |-xi| := by simpa using hxi
  rw [fourierKernel_reflect, hpsi.fourier_tail (-xi) hneg]
  push_cast
  ring

theorem integrable_dilation {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (fun t => psi (delta * t)) :=
  hpsi.integrable.comp_mul_left' hdelta.ne'

theorem fourier_zero_dilation {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℝ} (hdelta : 0 < delta) :
    fourierKernel (fun t => psi (delta * t)) 0 =
      (((2 / delta : ℝ)) : ℂ) := by
  rw [fourierKernel_scale_pos hdelta, zero_div, hpsi.fourier_zero]
  push_cast
  field_simp [hdelta.ne']

theorem fourier_localDilation_offDiagonal
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {m n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (localFourierDilationScale S omega n * t))
        (omega n - omega m) =
      (-2 * Complex.I) / (omega n - omega m) :=
  fourierKernel_localDilation_eq_neg_two_I_div
    hS hm hn hmn homega hpsi.fourier_tail

theorem fourier_reflection_localDilation_offDiagonal
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {m n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (-(localFourierDilationScale S omega n * t)))
        (omega n - omega m) =
      (2 * Complex.I) / (omega n - omega m) := by
  exact fourierKernel_localDilation_eq_const_div
    (g := fun u => psi (-u)) (kappa := 2 * Complex.I)
    hS hm hn hmn homega (fun xi hxi =>
      hpsi.fourier_reflection_tail hxi)

theorem fourier_localDilation_zero
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hn : n ∈ S)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (localFourierDilationScale S omega n * t)) 0 =
      (((4 * Real.pi / localFrequencySeparation S omega n : ℝ)) : ℂ) := by
  have hsep := localFrequencySeparation_pos hS hn homega
  have hscale := localFourierDilationScale_pos hS hn homega
  rw [hpsi.fourier_zero_dilation hscale]
  unfold localFourierDilationScale normalizedFourierDilationScale
  push_cast
  field_simp [hsep.ne', Real.pi_ne_zero]
  ring

theorem kernelForm_dilation_increment_re_nonneg
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {deltaNew deltaOld : ℝ}
    (hNew : 0 < deltaNew) (hOld : 0 < deltaOld)
    (horder : deltaNew ≤ deltaOld) :
    0 ≤ (finiteFourierKernelForm S c omega
          (fun t => psi (deltaNew * t)) -
        finiteFourierKernelForm S c omega
          (fun t => psi (deltaOld * t))).re := by
  exact finiteFourierKernelForm_scaled_sub_re_nonneg
    hpsi.integrable hOld hNew
    (hpsi.dilation_antitone hNew horder)

end MonotoneExtremalKernelCertificate
end DirichletPolynomial
end PrimeNumberTheorem
