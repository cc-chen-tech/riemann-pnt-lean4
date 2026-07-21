import PrimeNumberTheorem.CarneiroLittmannProfile

open Complex FourierTransform MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

noncomputable example (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  signedRadialTailProfile q x

example {q : ℝ → ℝ}
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0) (x : ℝ) :
    0 ≤ signedRadialTailProfile q x :=
  signedRadialTailProfile_nonnegative hpos hneg x

example {q : ℝ → ℝ} (hq : Integrable q)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x) :
    AntitoneOn (signedRadialTailProfile q) (Ioi 0) :=
  signedRadialTailProfile_antitoneOn_nonnegative hq hpos

example {q : ℝ → ℝ} (hq : Integrable q)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0) :
    MonotoneOn (signedRadialTailProfile q) (Iio 0) :=
  signedRadialTailProfile_monotoneOn_nonpositive hq hneg

example {q : ℝ → ℝ} (hq : Integrable q)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0)
    {deltaNew deltaOld : ℝ}
    (hNew : 0 < deltaNew) (horder : deltaNew ≤ deltaOld) (t : ℝ) :
    signedRadialTailProfile q (deltaOld * t) ≤
      signedRadialTailProfile q (deltaNew * t) :=
  signedRadialTailProfile_dilation_antitone hq hpos hneg hNew horder t

noncomputable example (x : ℝ) : ℝ := carneiroLittmannDensity x

example {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ carneiroLittmannDensity x :=
  carneiroLittmannDensity_nonnegative hx

example {x : ℝ} (hx : x ≤ 0) :
    carneiroLittmannDensity x ≤ 0 :=
  carneiroLittmannDensity_nonpositive hx

example : Integrable carneiroLittmannDensity :=
  integrable_carneiroLittmannDensity

example {xi : ℝ} (hxi : 1 ≤ |xi|) :
    𝓕 (fun x : ℝ => (carneiroLittmannDensity x : ℂ)) xi = 0 :=
  fourier_carneiroLittmannDensity_eq_zero_of_one_le_abs hxi

example {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel carneiroLittmannDensity xi = 0 :=
  fourierKernel_carneiroLittmannDensity_eq_zero hxi

example : ∫ x, carneiroLittmannDensity x = -1 :=
  integral_carneiroLittmannDensity_eq_neg_one

example : Integrable (fun x : ℝ => x * carneiroLittmannDensity x) :=
  integrable_id_mul_carneiroLittmannDensity

example {x : ℝ} (hx : x ≠ -1) :
    x * carneiroLittmannDensity x =
      Real.sinc (Real.pi * (x + 1)) ^ 2 :=
  id_mul_carneiroLittmannDensity_eq_sinc_shift hx

example : Integrable (fun x : ℝ =>
    Real.sinc (Real.pi * (x + 1)) ^ 2) :=
  integrable_carneiroLittmannSincShiftSq

noncomputable example (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  positiveTailIntegral q x

example {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    Integrable (positiveTailIntegral q) :=
  integrable_positiveTailIntegral hq hmoment

example {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    ∫ x, positiveTailIntegral q x =
      ∫ x in Ici 0, x * q x :=
  integral_positiveTailIntegral hq hmoment

example {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    ∫ x, signedRadialTailProfile q x =
      2 * ∫ x, x * q x :=
  integral_signedRadialTailProfile hq hmoment

noncomputable example (x : ℝ) : ℝ := carneiroLittmannTailProfile x

example : Integrable carneiroLittmannTailProfile :=
  integrable_carneiroLittmannTailProfile

example :
    ∫ x, carneiroLittmannTailProfile x =
      2 * (∫ x, Real.sinc (Real.pi * (x + 1)) ^ 2) :=
  integral_carneiroLittmannTailProfile_eq_sinc_shift

example :
    ∫ x, Real.sinc (Real.pi * (x + 1)) ^ 2 =
      Real.pi⁻¹ * ∫ u, Real.sinc u ^ 2 :=
  integral_carneiroLittmannSincShiftSq_eq

example :
    ∫ x, carneiroLittmannTailProfile x =
      2 * (Real.pi⁻¹ * ∫ u, Real.sinc u ^ 2) :=
  integral_carneiroLittmannTailProfile_eq_sinc_sq

example : ∫ x, carneiroLittmannTailProfile x = 2 :=
  integral_carneiroLittmannTailProfile_eq_two

example {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x))
    {xi : ℝ} (hxi : xi ≠ 0) :
    (Complex.I * (xi : ℂ)) * fourierKernel (signedRadialTailProfile q) xi =
      2 * (fourierKernel q xi - ((∫ x, q x : ℝ) : ℂ)) :=
  fourierKernel_signedRadialTailProfile_mul hq hmoment hxi

example {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel carneiroLittmannTailProfile xi =
      (-2 * Complex.I) / xi :=
  fourierKernel_carneiroLittmannTailProfile_eq hxi

example :
    MonotoneExtremalKernelCertificate carneiroLittmannTailProfile :=
  carneiroLittmannTailProfile_certificate

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ)
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    ‖hilbertForm S c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n :=
  hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
    S c omega hS homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hS : S.Nontrivial)
    (homega : Set.InjOn omega (S : Set ι)) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2 +
        4 * Real.pi *
          ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n :=
  finiteExponentialSum_meanSquare_le_localSeparation hab hS homega

example
    (hmass : ∫ x, Real.sinc (Real.pi * (x + 1)) ^ 2 = 1) :
    MonotoneExtremalKernelCertificate carneiroLittmannTailProfile :=
  carneiroLittmannTailProfile_certificate_of_sinc_shift_integral hmass

example
    (hmass : ∫ x, Real.sinc x ^ 2 = Real.pi) :
    MonotoneExtremalKernelCertificate carneiroLittmannTailProfile :=
  carneiroLittmannTailProfile_certificate_of_integral_sinc_sq hmass

#print axioms signedRadialTailProfile_nonnegative
#print axioms signedRadialTailProfile_antitoneOn_nonnegative
#print axioms signedRadialTailProfile_monotoneOn_nonpositive
#print axioms signedRadialTailProfile_dilation_antitone
#print axioms carneiroLittmannDensity_nonnegative
#print axioms carneiroLittmannDensity_nonpositive
#print axioms integrable_carneiroLittmannDensity
#print axioms fourier_carneiroLittmannDensity_eq_zero_of_one_le_abs
#print axioms fourierKernel_carneiroLittmannDensity_eq_zero
#print axioms integral_carneiroLittmannDensity_eq_neg_one
#print axioms integrable_id_mul_carneiroLittmannDensity
#print axioms id_mul_carneiroLittmannDensity_eq_sinc_shift
#print axioms id_mul_carneiroLittmannDensity_ae_eq_sinc_shift
#print axioms integrable_carneiroLittmannSincShiftSq
#print axioms integrable_positiveTailIntegral
#print axioms integral_positiveTailIntegral
#print axioms integrable_signedRadialTailProfile
#print axioms integral_signedRadialTailProfile
#print axioms integrable_carneiroLittmannTailProfile
#print axioms integral_carneiroLittmannTailProfile_eq_sinc_shift
#print axioms integral_carneiroLittmannSincShiftSq_eq
#print axioms integral_carneiroLittmannTailProfile_eq_sinc_sq
#print axioms integral_carneiroLittmannTailProfile_eq_two
#print axioms fourierKernel_signedRadialTailProfile_mul
#print axioms fourierKernel_carneiroLittmannTailProfile_eq
#print axioms carneiroLittmannTailProfile_certificate
#print axioms hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
#print axioms finiteExponentialSum_meanSquare_le_localSeparation
#print axioms carneiroLittmannTailProfile_certificate_of_sinc_shift_integral
#print axioms carneiroLittmannTailProfile_certificate_of_integral_sinc_sq

end DirichletPolynomial
end PrimeNumberTheorem
