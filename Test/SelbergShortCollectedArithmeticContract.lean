import HardyTheorem.SelbergShortCollectedArithmetic

open Complex

namespace Test.SelbergShortCollectedArithmeticContract

#check HardyTheorem.selbergShortCollectedDirichletConvolution
#check HardyTheorem.selbergShortDirichletCollectedCoeff_eq_convolution
#check HardyTheorem.selbergShortDirichletCollectedCoeff_eq_zero_of_not_mem
#check HardyTheorem.norm_selbergShortDirichletCollectedCoeff_le_convolutionMajorant

example (N X k : ℕ) :
    HardyTheorem.selbergShortDirichletCollectedCoeff N X k =
      (HardyTheorem.selbergShortCollectedDirichletConvolution N X k : ℂ) *
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ :=
  HardyTheorem.selbergShortDirichletCollectedCoeff_eq_convolution N X k

example {N X k : ℕ}
    (hk : k ∉ Finset.Icc 1 (N * X * X)) :
    HardyTheorem.selbergShortDirichletCollectedCoeff N X k = 0 :=
  HardyTheorem.selbergShortDirichletCollectedCoeff_eq_zero_of_not_mem hk

example {N X k : ℕ} (hX : 2 ≤ X) :
    ‖HardyTheorem.selbergShortDirichletCollectedCoeff N X k‖ ≤
      (∑ p ∈ HardyTheorem.selbergMollifiedDirichletPairs (N * X) X k,
        (p.1.divisorsAntidiagonal.card : ℝ)) /
        Real.sqrt (k : ℝ) :=
  HardyTheorem.norm_selbergShortDirichletCollectedCoeff_le_convolutionMajorant hX

#print axioms HardyTheorem.selbergShortDirichletCollectedCoeff_eq_convolution
#print axioms HardyTheorem.selbergShortDirichletCollectedCoeff_eq_zero_of_not_mem
#print axioms HardyTheorem.norm_selbergShortDirichletCollectedCoeff_le_convolutionMajorant

end Test.SelbergShortCollectedArithmeticContract
