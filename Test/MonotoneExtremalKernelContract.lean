import PrimeNumberTheorem.MonotoneExtremalKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example (psi : ℝ → ℝ) : Prop :=
  MonotoneExtremalKernelCertificate psi

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi) :
    Integrable psi :=
  hpsi.integrable

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi) :
    fourierKernel psi 0 = 2 :=
  hpsi.fourier_zero

example (g : ℝ → ℝ) (xi : ℝ) :
    fourierKernel (fun t => g (-t)) xi = fourierKernel g (-xi) :=
  fourierKernel_reflect g xi

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi) :
    Integrable (fun t => psi (-t)) :=
  hpsi.integrable_reflection

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi) :
    fourierKernel (fun t => psi (-t)) 0 = 2 :=
  hpsi.fourier_reflection_zero

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel (fun t => psi (-t)) xi =
      (2 * Complex.I) / xi :=
  hpsi.fourier_reflection_tail hxi

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (fun t => psi (delta * t)) :=
  hpsi.integrable_dilation hdelta

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℝ} (hdelta : 0 < delta) :
    fourierKernel (fun t => psi (delta * t)) 0 =
      (((2 / delta : ℝ)) : ℂ) :=
  hpsi.fourier_zero_dilation hdelta

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {m n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (localFourierDilationScale S omega n * t))
        (omega n - omega m) =
      (-2 * Complex.I) / (omega n - omega m) :=
  hpsi.fourier_localDilation_offDiagonal hS hm hn hmn homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {m n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (-(localFourierDilationScale S omega n * t)))
        (omega n - omega m) =
      (2 * Complex.I) / (omega n - omega m) :=
  hpsi.fourier_reflection_localDilation_offDiagonal
    hS hm hn hmn homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hn : n ∈ S)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (localFourierDilationScale S omega n * t)) 0 =
      (((4 * Real.pi / localFrequencySeparation S omega n : ℝ)) : ℂ) :=
  hpsi.fourier_localDilation_zero hS hn homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {deltaNew deltaOld : ℝ}
    (hNew : 0 < deltaNew) (hOld : 0 < deltaOld)
    (horder : deltaNew ≤ deltaOld) :
    0 ≤ (finiteFourierKernelForm S c omega
          (fun t => psi (deltaNew * t)) -
        finiteFourierKernelForm S c omega
          (fun t => psi (deltaOld * t))).re :=
  hpsi.kernelForm_dilation_increment_re_nonneg hNew hOld horder

#print axioms MonotoneExtremalKernelCertificate.integrable_dilation
#print axioms fourierKernel_reflect
#print axioms MonotoneExtremalKernelCertificate.integrable_reflection
#print axioms MonotoneExtremalKernelCertificate.fourier_reflection_zero
#print axioms MonotoneExtremalKernelCertificate.fourier_reflection_tail
#print axioms MonotoneExtremalKernelCertificate.fourier_zero_dilation
#print axioms MonotoneExtremalKernelCertificate.fourier_localDilation_offDiagonal
#print axioms MonotoneExtremalKernelCertificate.fourier_reflection_localDilation_offDiagonal
#print axioms MonotoneExtremalKernelCertificate.fourier_localDilation_zero
#print axioms MonotoneExtremalKernelCertificate.kernelForm_dilation_increment_re_nonneg

end DirichletPolynomial
end PrimeNumberTheorem
