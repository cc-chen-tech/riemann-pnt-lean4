import HardyTheorem.SelbergMollifiedCoefficientEnergy

open scoped BigOperators

namespace HardyTheorem

#check selbergMollifiedCriticalLineCoeff
#check normSq_selbergMollifiedCriticalLineCoeff_le_inv
#check sum_normSq_selbergMollifiedCriticalLineCoeff_le_harmonic
#check sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log_min
#check sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log

example {N X k : ℕ} (hX : 2 ≤ X) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (hkX : k ≤ X) :
    Complex.normSq (selbergMollifiedCriticalLineCoeff N X k) ≤ (k : ℝ)⁻¹ :=
  normSq_selbergMollifiedCriticalLineCoeff_le_inv hX hk1 hkN hkX

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Icc 1 (min N X),
      Complex.normSq (selbergMollifiedCriticalLineCoeff N X k)) ≤
      (harmonic (min N X) : ℝ) :=
  sum_normSq_selbergMollifiedCriticalLineCoeff_le_harmonic hN hX

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Icc 1 (min N X),
      Complex.normSq (selbergMollifiedCriticalLineCoeff N X k)) ≤
      1 + Real.log X :=
  sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log hN hX

#print axioms normSq_selbergMollifiedCriticalLineCoeff_le_inv
#print axioms sum_normSq_selbergMollifiedCriticalLineCoeff_le_harmonic
#print axioms sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log_min
#print axioms sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log

end HardyTheorem
