import PrimeNumberTheorem.LittlewoodRectangle

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {G : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hbottom : IntervalIntegrable
      (fun x : ℝ => G ((x : ℂ) + (y0 : ℂ) * I))
      MeasureTheory.volume x0 x1)
    (htop : IntervalIntegrable
      (fun x : ℝ => G ((x : ℂ) + (y1 : ℂ) * I))
      MeasureTheory.volume x0 x1)
    (hright : IntervalIntegrable
      (fun y : ℝ => G ((x1 : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume y0 y1)
    (hleft : IntervalIntegrable
      (fun y : ℝ => G ((x0 : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume y0 y1) :
    (MathlibAux.boundaryRectIntegral G x0 x1 y0 y1).im =
      (∫ x in x0..x1,
          (G ((x : ℂ) + (y0 : ℂ) * I)).im) -
        (∫ x in x0..x1,
          (G ((x : ℂ) + (y1 : ℂ) * I)).im) +
        (∫ y in y0..y1,
          (G ((x1 : ℂ) + (y : ℂ) * I)).re) -
        (∫ y in y0..y1,
          (G ((x0 : ℂ) + (y : ℂ) * I)).re) :=
  im_boundaryRectIntegral_eq_four_edges hbottom htop hright hleft

example {f : ℂ → ℂ} {sigma t : ℝ}
    (hf : AnalyticAt ℂ f ((sigma : ℂ) + I * (t : ℂ)))
    (hne : f ((sigma : ℂ) + I * (t : ℂ)) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖)
      (-(logDeriv f ((sigma : ℂ) + I * (t : ℂ))).im) t :=
  hasDerivAt_log_norm_vertical hf hne

example {f : ℂ → ℂ} {sigma a b : ℝ}
    (hf : ∀ u ∈ [[a, b]],
      AnalyticAt ℂ f ((sigma : ℂ) + I * (u : ℂ)))
    (hne : ∀ u ∈ [[a, b]],
      f ((sigma : ℂ) + I * (u : ℂ)) ≠ 0)
    (hint : IntervalIntegrable
      (fun u : ℝ => -(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)
      MeasureTheory.volume a b) :
    (∫ u in a..b,
        u * (-(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)) =
      b * Real.log ‖f ((sigma : ℂ) + I * (b : ℂ))‖ -
        a * Real.log ‖f ((sigma : ℂ) + I * (a : ℂ))‖ -
          ∫ u in a..b,
            Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖ :=
  intervalIntegral_mul_neg_im_logDeriv_vertical_eq hf hne hint

example {f : ℂ → ℂ} {sigma a b : ℝ}
    (hf : ∀ u ∈ [[a, b]],
      AnalyticAt ℂ f ((sigma : ℂ) + I * (u : ℂ)))
    (hne : ∀ u ∈ [[a, b]],
      f ((sigma : ℂ) + I * (u : ℂ)) ≠ 0) :
    ContinuousOn
      (fun u : ℝ => -(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)
      [[a, b]] :=
  continuousOn_neg_im_logDeriv_vertical hf hne

example {f : ℂ → ℂ} {sigma a b : ℝ}
    (hf : ∀ u ∈ [[a, b]],
      AnalyticAt ℂ f ((sigma : ℂ) + I * (u : ℂ)))
    (hne : ∀ u ∈ [[a, b]],
      f ((sigma : ℂ) + I * (u : ℂ)) ≠ 0) :
    (∫ u in a..b,
        u * (-(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)) =
      b * Real.log ‖f ((sigma : ℂ) + I * (b : ℂ))‖ -
        a * Real.log ‖f ((sigma : ℂ) + I * (a : ℂ))‖ -
          ∫ u in a..b,
            Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖ :=
  intervalIntegral_mul_neg_im_logDeriv_vertical_eq_of_analytic hf hne

example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ) (anchor : ℂ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1) :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ => (z - anchor) * logDeriv f z)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ poles, (rho - anchor) * (multiplicity rho : ℂ) :=
  boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum
    poles multiplicity anchor hf hzero horder hpoles

example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1)
    (hbottom : IntervalIntegrable
      (fun x : ℝ =>
        (((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x : ℂ) + (y0 : ℂ) * I)))
      MeasureTheory.volume x0 x1)
    (htop : IntervalIntegrable
      (fun x : ℝ =>
        (((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x : ℂ) + (y1 : ℂ) * I)))
      MeasureTheory.volume x0 x1)
    (hright : IntervalIntegrable
      (fun y : ℝ =>
        (((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x1 : ℂ) + (y : ℂ) * I)))
      MeasureTheory.volume y0 y1)
    (hleft : IntervalIntegrable
      (fun y : ℝ =>
        (((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x0 : ℂ) + (y : ℂ) * I)))
      MeasureTheory.volume y0 y1) :
    (2 * Real.pi) *
        ∑ rho ∈ poles,
          (rho.re - x0) * (multiplicity rho : ℝ) =
      (∫ x in x0..x1,
          ((((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x : ℂ) + (y0 : ℂ) * I))).im) -
        (∫ x in x0..x1,
          ((((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x : ℂ) + (y1 : ℂ) * I))).im) +
        (∫ y in y0..y1,
          ((((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x1 : ℂ) + (y : ℂ) * I))).re) -
        (∫ y in y0..y1,
          ((((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x0 : ℂ) + (y : ℂ) * I))).re) :=
  two_pi_mul_zeroMultiplicityWeightedRealSum_eq_four_edges
    poles multiplicity hf hzero horder hpoles hbottom htop hright hleft

#print axioms boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum
#print axioms im_boundaryRectIntegral_eq_four_edges
#print axioms hasDerivAt_log_norm_vertical
#print axioms intervalIntegral_mul_neg_im_logDeriv_vertical_eq
#print axioms continuousOn_neg_im_logDeriv_vertical
#print axioms intervalIntegral_mul_neg_im_logDeriv_vertical_eq_of_analytic
#print axioms two_pi_mul_zeroMultiplicityWeightedRealSum_eq_four_edges

end CarlsonZeroDensity
end PrimeNumberTheorem
