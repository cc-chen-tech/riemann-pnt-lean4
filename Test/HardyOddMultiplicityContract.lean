import HardyTheorem.HardyOddMultiplicity

open Complex Set

namespace HardyTheorem

#check criticalLineCompletedRiemannZeta
#check analyticAt_criticalLineCompletedRiemannZeta
#check hardyZ_eq_criticalLineCompletedRiemannZeta_div_norm
#check odd_analyticOrderNatAt_riemannZeta_of_hardyZ_local_sign_change
#check odd_analyticOrderNatAt_riemannZeta_of_hardyZ_reverse_local_sign_change

#print axioms analyticAt_criticalLineCompletedRiemannZeta
#print axioms hardyZ_eq_criticalLineCompletedRiemannZeta_div_norm
#print axioms analyticOrderNatAt_criticalLineCompletedRiemannZeta_eq_riemannZeta
#print axioms odd_analyticOrderNatAt_riemannZeta_of_hardyZ_local_sign_change
#print axioms odd_analyticOrderNatAt_riemannZeta_of_hardyZ_reverse_local_sign_change

example {t : ℝ}
    (hleft : ∀ ε > 0, ∃ x ∈ Set.Ioo (t - ε) t, hardyZ x < 0)
    (hright : ∀ ε > 0, ∃ x ∈ Set.Ioo t (t + ε), 0 < hardyZ x) :
    Odd (analyticOrderNatAt riemannZeta ((1 / 2 : ℂ) + I * t)) :=
  odd_analyticOrderNatAt_riemannZeta_of_hardyZ_local_sign_change hleft hright

end HardyTheorem
