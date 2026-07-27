import PrimeNumberTheorem.VKEdgeArithmeticL2Converse
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition

open Complex Filter
open Asymptotics
open scoped ComplexConjugate

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/--
For a fixed positive logarithmic-window width `ε`, the ordinary local
Chebyshev-error second moment has exponent at most `theta` if it is little-o
of every strictly larger exponential scale.

This is an upper-bound hypothesis. No unconditional estimate of this strength
is asserted here.
-/
def LocalPsiL2ExponentAtMost (ε theta : ℝ) : Prop :=
  ∀ beta : ℝ, theta < beta →
    (fun Y : ℝ => logarithmicPsiErrorSecondMoment ε Y) =o[atTop]
      (fun Y : ℝ =>
        Real.exp (2 * beta * Real.log Y) * Real.log Y)

/--
A local second-moment exponent bound excludes every positive-ordinate zeta
zero whose real part lies strictly above both the critical line and the
claimed exponent.
-/
theorem riemannZeta_ne_zero_of_localPsiL2ExponentAtMost
    {ε theta : ℝ}
    (hε : 0 < ε)
    (hupper : LocalPsiL2ExponentAtMost ε theta)
    {rho : ℂ}
    (hgamma : 0 < rho.im)
    (hrhoReHalf : 1 / 2 < rho.re)
    (hthetaRho : theta < rho.re)
    (hrhoRe1 : rho.re < 1) :
    riemannZeta rho ≠ 0 :=
  riemannZeta_ne_zero_of_logarithmicPsiErrorSecondMoment_isLittleO
    hε hgamma hrhoReHalf hrhoRe1 (hupper rho.re hthetaRho)

private theorem nontrivialZero_re_eq_half_of_positive_im
    {ε : ℝ}
    (hε : 0 < ε)
    (hupper : LocalPsiL2ExponentAtMost ε (1 / 2))
    {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hgamma : 0 < rho.im) :
    rho.re = 1 / 2 := by
  apply le_antisymm
  · by_contra hle
    have hhalf : (1 / 2 : ℝ) < rho.re := lt_of_not_ge hle
    exact
      (riemannZeta_ne_zero_of_localPsiL2ExponentAtMost
        hε hupper hgamma hhalf hhalf hrho.2.2) hrho.1
  · by_contra hle
    have hrhoHalf : rho.re < (1 / 2 : ℝ) := lt_of_not_ge hle
    let reflected : ℂ :=
      RiemannVonMangoldt.criticalLineReflection rho
    have hreflectedZero :
        RiemannHypothesis.IsNontrivialZero reflected :=
      RiemannVonMangoldt.isNontrivialZero_criticalLineReflection hrho
    have hreflectedIm : 0 < reflected.im := by
      simpa [reflected] using hgamma
    have hreflectedHalf : (1 / 2 : ℝ) < reflected.re := by
      dsimp [reflected]
      simp only [RiemannVonMangoldt.criticalLineReflection_re]
      linarith
    exact
      (riemannZeta_ne_zero_of_localPsiL2ExponentAtMost
        hε hupper hreflectedIm hreflectedHalf hreflectedHalf
          hreflectedZero.2.2) hreflectedZero.1

/--
At the critical exponent, the local second-moment upper bound forces every
nontrivial zeta zero with nonzero ordinate onto the critical line.

The `rho.im ≠ 0` premise records the exact coverage of the oscillation theorem
used upstream; real points in the critical strip are not hidden in this
statement.
-/
theorem nontrivialZero_re_eq_half_of_localPsiL2ExponentAtMost_of_im_ne_zero
    {ε : ℝ}
    (hε : 0 < ε)
    (hupper : LocalPsiL2ExponentAtMost ε (1 / 2))
    {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (him : rho.im ≠ 0) :
    rho.re = 1 / 2 := by
  by_cases hgamma : 0 < rho.im
  · exact
      nontrivialZero_re_eq_half_of_positive_im hε hupper hrho hgamma
  · have hneg : rho.im < 0 := lt_of_le_of_ne (le_of_not_gt hgamma) him
    have hconj :
        RiemannHypothesis.IsNontrivialZero (conj rho) :=
      RiemannVonMangoldt.isNontrivialZero_conj hrho
    have hconjGamma : 0 < (conj rho).im := by
      simp
      exact hneg
    have hconjRe :
        (conj rho).re = 1 / 2 :=
      nontrivialZero_re_eq_half_of_positive_im
        hε hupper hconj hconjGamma
    simpa using hconjRe

/--
Conditional RH closure from the critical local-second-moment exponent bound,
provided the remaining real-axis case is supplied separately.

The third premise is explicit because the positive-ordinate oscillation
theorem does not itself exclude real zeta zeros in the critical strip.
-/
theorem riemannHypothesis_of_localPsiL2ExponentAtMost_of_realAxis
    {ε : ℝ}
    (hε : 0 < ε)
    (hupper : LocalPsiL2ExponentAtMost ε (1 / 2))
    (hreal :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        rho.im = 0 →
        rho.re = 1 / 2) :
    RiemannHypothesis.Statement := by
  intro rho hrho
  by_cases him : rho.im = 0
  · exact hreal rho hrho him
  · exact
      nontrivialZero_re_eq_half_of_localPsiL2ExponentAtMost_of_im_ne_zero
        hε hupper hrho him

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
