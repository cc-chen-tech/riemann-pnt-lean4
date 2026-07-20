import PrimeNumberTheorem.PintzEnvelope

open Complex Filter Set Topology

namespace PrimeNumberTheorem
namespace Pintz

noncomputable example (x : ℝ) : Set ℝ :=
  pintzZeroEnvelopeValues x

noncomputable example (x : ℝ) : ℝ :=
  pintzZeroEnvelope x

noncomputable example (c x t : ℝ) : ℝ :=
  pintzClassicalMinorant c x t

example : Set ℂ := pintzLowZeros

noncomputable example (x : ℝ) : Set ℝ := pintzLowZeroValues x

noncomputable example (x : ℝ) : ℝ := pintzLowZeroFloor x

example (x : ℝ) : (pintzZeroEnvelopeValues x).Nonempty :=
  pintzZeroEnvelopeValues_nonempty x

example : pintzLowZeros.Finite := finite_pintzLowZeros

example (x : ℝ) : (pintzLowZeroValues x).Finite :=
  finite_pintzLowZeroValues x

example {x : ℝ} (hx : 1 ≤ x) :
    BddBelow (pintzZeroEnvelopeValues x) :=
  bddBelow_pintzZeroEnvelopeValues hx

example {x : ℝ} (hx : 1 ≤ x) {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im) :
    pintzZeroEnvelope x ≤
      (1 - rho.re) * Real.log x + Real.log rho.im :=
  pintzZeroEnvelope_le_zeroTerm hx hrho him

example :
    ∃ c > 0, ∀ {x : ℝ}, 1 ≤ x → ∀ {rho : ℂ},
      RiemannHypothesis.IsNontrivialZero rho → 2 ≤ rho.im →
        pintzClassicalMinorant c x rho.im ≤ pintzZeroTerm x rho :=
  exists_classicalMinorant_le_zeroTerm

example {c x t : ℝ} (hc : 0 < c) (hx : 1 ≤ x) (ht : 2 ≤ t) :
    2 * Real.sqrt (c * Real.log x) ≤ pintzClassicalMinorant c x t :=
  two_mul_sqrt_le_classicalMinorant hc hx ht

example :
    ∃ c > 0, ∀ {x : ℝ}, 1 ≤ x → ∀ {rho : ℂ},
      RiemannHypothesis.IsNontrivialZero rho → 2 ≤ rho.im →
        2 * Real.sqrt (c * Real.log x) ≤ pintzZeroTerm x rho :=
  exists_two_mul_sqrt_le_highZeroTerm

example :
    ∃ c > 0, ∀ {x : ℝ}, 1 ≤ x →
      min (pintzLowZeroFloor x) (2 * Real.sqrt (c * Real.log x)) ≤
        pintzZeroEnvelope x :=
  exists_min_lowFloor_two_mul_sqrt_le_zeroEnvelope

example {c : ℝ} (hc : 0 < c) {rho : ℂ} (hrho : rho ∈ pintzLowZeros) :
    ∀ᶠ x : ℝ in atTop,
      2 * Real.sqrt (c * Real.log x) ≤ pintzZeroTerm x rho :=
  eventually_two_mul_sqrt_le_lowZeroTerm hc hrho

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ rho ∈ pintzLowZeros,
      2 * Real.sqrt (c * Real.log x) ≤ pintzZeroTerm x rho :=
  eventually_all_lowZeroTerms_above_sqrt hc

example :
    ∃ c > 0, ∀ᶠ x : ℝ in atTop,
      2 * Real.sqrt (c * Real.log x) ≤ pintzZeroEnvelope x :=
  exists_eventually_two_mul_sqrt_le_zeroEnvelope

example : MonotoneOn pintzZeroEnvelope (Set.Ici 1) :=
  monotoneOn_pintzZeroEnvelope

#print axioms pintzZeroEnvelopeValues_nonempty
#print axioms finite_pintzLowZeros
#print axioms finite_pintzLowZeroValues
#print axioms bddBelow_pintzZeroEnvelopeValues
#print axioms exists_classicalMinorant_le_zeroTerm
#print axioms two_mul_sqrt_le_classicalMinorant
#print axioms exists_two_mul_sqrt_le_highZeroTerm
#print axioms exists_min_lowFloor_two_mul_sqrt_le_zeroEnvelope
#print axioms eventually_two_mul_sqrt_le_lowZeroTerm
#print axioms eventually_all_lowZeroTerms_above_sqrt
#print axioms exists_eventually_two_mul_sqrt_le_zeroEnvelope
#print axioms pintzZeroEnvelope_le_zeroTerm
#print axioms monotoneOn_pintzZeroEnvelope

end Pintz
end PrimeNumberTheorem
