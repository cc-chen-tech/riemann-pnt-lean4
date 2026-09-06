import HardyTheorem.SelbergOffDiagonalOuterSum

namespace HardyTheorem

#check selbergOffDiagonalOuterMajorant
#check selbergOffDiagonalOuterMajorant_le

example {X : ℕ} (hX : 1 ≤ X) {L W : ℝ} (hL : 0 ≤ L) (hW : 0 ≤ W) :
    selbergOffDiagonalOuterMajorant X L W ≤
      (X : ℝ) ^ 4 * (1 + Real.log (X : ℝ)) * L +
        (X : ℝ) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 * W :=
  selbergOffDiagonalOuterMajorant_le hX hL hW

end HardyTheorem
