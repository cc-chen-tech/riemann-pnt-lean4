import PrimeNumberTheorem.ZeroDensityExponentCertificate

namespace PrimeNumberTheorem

open Filter
open Asymptotics

example {σ q : ℝ} {B : ℕ}
    (h : ZeroDensityEventualMajorant σ q B) :
    (fun T => (ZeroDensity.zeroDensityCount σ T : ℝ)) =O[atTop]
      (fun T => T ^ q * (Real.log T) ^ B) :=
  h.isBigO

example {σ q q' : ℝ} {B : ℕ}
    (h : ZeroDensityEventualMajorant σ q B) (hqq' : q ≤ q') :
    ZeroDensityEventualMajorant σ q' B :=
  h.mono_exponent hqq'

example (h : CarlsonDIImprovedDensityCertificate) :
    (fun T => (ZeroDensity.zeroDensityCount (2 / 3) T : ℝ)) =O[atTop]
      (fun T => T ^ (467 / 576 : ℝ) * (Real.log T) ^ 6) :=
  h.isBigO

example : CarlsonDIImprovedDensityCertificate =
    ZeroDensityEventualMajorant (2 / 3) diTargetExponent 6 := by
  rfl

#print axioms ZeroDensityEventualMajorant.isBigO
#print axioms ZeroDensityEventualMajorant.mono_exponent
#print axioms CarlsonDIImprovedDensityCertificate.isBigO

end PrimeNumberTheorem
