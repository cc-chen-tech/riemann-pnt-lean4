import PrimeNumberTheorem.CarneiroLittmannProfile

open Complex MeasureTheory Set

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

noncomputable example (x : ℝ) : ℝ := carneiroLittmannTailProfile x

example
    (hprofile : Integrable carneiroLittmannTailProfile)
    (hmass : ∫ x, carneiroLittmannTailProfile x = 2)
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel carneiroLittmannTailProfile xi =
        (-2 * Complex.I) / xi) :
    MonotoneExtremalKernelCertificate carneiroLittmannTailProfile :=
  carneiroLittmannTailProfile_certificate hprofile hmass htail

#print axioms signedRadialTailProfile_nonnegative
#print axioms signedRadialTailProfile_antitoneOn_nonnegative
#print axioms signedRadialTailProfile_monotoneOn_nonpositive
#print axioms signedRadialTailProfile_dilation_antitone
#print axioms carneiroLittmannDensity_nonnegative
#print axioms carneiroLittmannDensity_nonpositive
#print axioms integrable_carneiroLittmannDensity
#print axioms carneiroLittmannTailProfile_certificate

end DirichletPolynomial
end PrimeNumberTheorem
