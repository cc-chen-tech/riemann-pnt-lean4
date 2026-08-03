import HardyTheorem.SelbergSqrtZetaCoeffBound

open Complex

namespace HardyTheorem

example (k : ℕ) :
    |selbergSqrtZetaLocalCoeff k| ≤ 1 :=
  abs_selbergSqrtZetaLocalCoeff_le_one k

example (n : ℕ) :
    |selbergSqrtZetaCoeff n| ≤ 1 :=
  abs_selbergSqrtZetaCoeff_le_one n

example
    {X n : ℕ} (hX : 2 ≤ X) (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    |selbergSqrtZetaTaperedCoeff X n| ≤ 1 :=
  abs_selbergSqrtZetaTaperedCoeff_le_one hX hn1 hnX

example
    {X : ℕ} (hX : 2 ≤ X) :
    selbergSqrtZetaMollifierMajorant X ≤ 2 * Real.sqrt X :=
  selbergSqrtZetaMollifierMajorant_le_two_sqrt hX

example
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    ‖selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
      2 * Real.sqrt X :=
  norm_selbergSqrtZetaMollifier_criticalLine_le_two_sqrt hX t

end HardyTheorem
