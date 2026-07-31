import PrimeNumberTheorem.VKEdgePiOverTwoFinitePoleFilter

open Polynomial

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check poleFactor
#check targetPreservingPoleFilter
#check emptyCenterPoleFilter
#check conjugatePolynomial

example (z : ℂ) :
    (poleFactor z).eval 0 = 1 :=
  poleFactor_eval_zero z

example {z : ℂ} (hz : z ≠ 0) :
    (poleFactor z).eval z = 0 :=
  poleFactor_eval_self hz

example (offsets : Finset ℂ) :
    (targetPreservingPoleFilter offsets).eval 0 = 1 :=
  targetPreservingPoleFilter_eval_zero offsets

example {offsets : Finset ℂ} {z : ℂ}
    (hz : z ∈ offsets) (hz0 : z ≠ 0) :
    (targetPreservingPoleFilter offsets).eval z = 0 :=
  targetPreservingPoleFilter_eval_eq_zero hz hz0

example {offsets : Finset ℂ} {z : ℂ}
    (hz : z ∈ offsets) (hz0 : z ≠ 0) :
    (emptyCenterPoleFilter offsets).eval z = 0 :=
  emptyCenterPoleFilter_eval_eq_zero hz hz0

example (p : ℂ[X]) (z : ℂ) :
    (conjugatePolynomial p).eval (star z) = star (p.eval z) :=
  conjugatePolynomial_eval_star p z

example (offsets : Finset ℂ) :
    conjugatePolynomial (targetPreservingPoleFilter offsets) =
      targetPreservingPoleFilter (offsets.image fun z => star z) :=
  conjugatePolynomial_targetPreservingPoleFilter offsets

end VKEdgePiOverTwo
end PrimeNumberTheorem
