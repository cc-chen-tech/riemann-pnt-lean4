import HardyTheorem.SelbergShortLowRangeArithmetic

open Complex

namespace Test.SelbergShortLowRangeArithmeticContract

#check HardyTheorem.selbergShortLowRangeVonMangoldtConvolution
#check HardyTheorem.selbergShortCollectedDirichletConvolution_eq_lowRange
#check HardyTheorem.selbergShortDirichletCollectedCoeff_eq_lowRange
#check HardyTheorem.norm_selbergShortDirichletCollectedCoeff_le_two_div_sqrt

example {N X k : ℕ} (hk : 1 < k) (hkN : k ≤ N) (hkX : k ≤ X) :
    HardyTheorem.selbergShortCollectedDirichletConvolution N X k =
      HardyTheorem.selbergMoebiusCoeff X k +
        HardyTheorem.selbergShortLowRangeVonMangoldtConvolution X k /
          Real.log X :=
  HardyTheorem.selbergShortCollectedDirichletConvolution_eq_lowRange
    hk hkN hkX

example {N X k : ℕ} (hk : 1 < k) (hkN : k ≤ N) (hkX : k ≤ X) :
    HardyTheorem.selbergShortDirichletCollectedCoeff N X k =
      ((HardyTheorem.selbergMoebiusCoeff X k +
          HardyTheorem.selbergShortLowRangeVonMangoldtConvolution X k /
            Real.log X : ℝ) : ℂ) *
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ :=
  HardyTheorem.selbergShortDirichletCollectedCoeff_eq_lowRange hk hkN hkX

example {N X k : ℕ} (hX : 2 ≤ X) (hk : 1 < k)
    (hkN : k ≤ N) (hkX : k ≤ X) :
    ‖HardyTheorem.selbergShortDirichletCollectedCoeff N X k‖ ≤
      2 / Real.sqrt (k : ℝ) :=
  HardyTheorem.norm_selbergShortDirichletCollectedCoeff_le_two_div_sqrt
    hX hk hkN hkX

#print axioms HardyTheorem.selbergShortCollectedDirichletConvolution_eq_lowRange
#print axioms HardyTheorem.selbergShortDirichletCollectedCoeff_eq_lowRange
#print axioms HardyTheorem.norm_selbergShortDirichletCollectedCoeff_le_two_div_sqrt

end Test.SelbergShortLowRangeArithmeticContract
