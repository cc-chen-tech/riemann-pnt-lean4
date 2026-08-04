import HardyTheorem.SelbergSqrtZetaSignedModelSupBound

namespace HardyTheorem

noncomputable example (T : ℝ) (X : ℕ) : ℝ :=
  selbergSqrtZetaSignedModelSupBoundL1 T X

example (kappa T : ℝ) (X : ℕ) (t : ℝ) :
    |selbergSqrtZetaSignedThetaModel kappa T X t| ≤
      selbergSqrtZetaSignedModelSupBoundL1 T X :=
  abs_selbergSqrtZetaSignedThetaModel_le_modelSupBoundL1 kappa T X t

end HardyTheorem
