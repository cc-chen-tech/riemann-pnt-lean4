import HardyTheorem.SelbergCompletedMollified

open Complex

namespace HardyTheorem

/-!
# Contract for Selberg's completed-zeta mollified sign function

The contract catches a wrong `-1/2` conversion from Xi to completed zeta,
loss of the positive exponential tilt, or an incorrect sign orientation in
the transfer back to Hardy's `Z` function.
-/

example (delta : ℝ) (X : ℕ) (t : ℝ) :
    selbergCompletedMollifiedF delta X t =
      -(selbergCompletedMollifiedPositiveFactor delta X t) * hardyZ t :=
  selbergCompletedMollifiedF_eq_neg_factor_mul_hardyZ delta X t

example (X : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) + I * t)) =
      selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
        ((1 / 2 : ℂ) - I * t) :=
  conj_selbergCompletedSqrtZetaMollifier_criticalLine_eq_neg X t

example (X : ℕ) (t : ℝ) :
    selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) + I * t) *
        selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) - I * t) =
      (Complex.normSq
        (selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) + I * t)) : ℂ) :=
  selbergCompletedSqrtZetaMollifier_mul_reflection_eq_normSq X t

example {delta : ℝ} {X : ℕ} {t : ℝ}
    (h : selbergCompletedMollifiedF delta X t < 0) :
    0 < hardyZ t :=
  hardyZ_pos_of_selbergCompletedMollifiedF_neg h

example {delta : ℝ} {X : ℕ} {t : ℝ}
    (h : 0 < selbergCompletedMollifiedF delta X t) :
    hardyZ t < 0 :=
  hardyZ_neg_of_selbergCompletedMollifiedF_pos h

example {delta : ℝ} {X : ℕ} {t : ℝ}
    (h : HasLocalSignChangeAt (selbergCompletedMollifiedF delta X) t) :
    HasLocalSignChangeAt hardyZ t :=
  hasLocalSignChangeAt_hardyZ_of_selbergCompletedMollifiedF h

example (delta : ℝ) (X : ℕ) :
    Continuous (selbergCompletedMollifiedF delta X) :=
  continuous_selbergCompletedMollifiedF delta X

#print axioms selbergCompletedMollifiedF_eq_neg_factor_mul_hardyZ
#print axioms conj_selbergCompletedSqrtZetaMollifier_criticalLine_eq_neg
#print axioms selbergCompletedSqrtZetaMollifier_mul_reflection_eq_normSq
#print axioms hasLocalSignChangeAt_hardyZ_of_selbergCompletedMollifiedF
#print axioms continuous_selbergCompletedMollifiedF

end HardyTheorem
