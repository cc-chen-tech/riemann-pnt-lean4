import PrimeNumberTheorem.CarlsonHalfRangeDensity

set_option autoImplicit false
open Filter Asymptotics
open PrimeNumberTheorem PrimeNumberTheorem.ZeroDensity

example : ∃ K > (0 : ℝ), ∀ᶠ T : ℝ in atTop,
    (zeroDensityClosedCount (2 / 3) T : ℝ) ≤
      K * T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6 :=
  exists_eventually_carlson_halfRange_closedCount_le

example : (fun T => (zeroDensityClosedCount (2 / 3) T : ℝ)) =O[atTop]
    (fun T => T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6) :=
  carlson_halfRange_closed_zeroDensity_isBigO

example : Nonempty (ZeroDensityEventualMajorant (2 / 3) (8 / 9 - 1 / 400) 6) :=
  exists_carlson_halfRange_densityCertificate

example : (fun T => (zeroDensityCount (2 / 3) T : ℝ)) =O[atTop]
    (fun T => T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6) :=
  carlson_halfRange_zeroDensity_isBigO

#print axioms exists_eventually_carlson_halfRange_closedCount_le
#print axioms carlson_halfRange_closed_zeroDensity_isBigO
#print axioms exists_carlson_halfRange_densityCertificate
#print axioms carlson_halfRange_zeroDensity_isBigO
