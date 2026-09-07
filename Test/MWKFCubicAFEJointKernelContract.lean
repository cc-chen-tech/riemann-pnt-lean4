import PrimeNumberTheorem.MWKFCubicAFEJointKernel

open PrimeNumberTheorem.MWKFCubic

#check continuous_cubicAFELogProductWeightFinite_joint
#check continuousOn_cubicAFERealProductWeightFinite_joint
#check continuousOn_cubicAFEProgressionPhysicalSummand_joint
#check continuous_cubicAFEProgressionCutoffSummand_joint
#check hasCompactSupport_cubicAFEProgressionCutoffSummand_joint

open Set

-- Arbitrary real height and signed shifts: joint regularity is not inferred
-- from separate continuity or assumed for an abstract replacement kernel.
#check (@continuous_cubicAFELogProductWeightFinite_joint :
  ∀ {X : ℝ}, 1 / 2 < X → ∀ V : ℝ,
    Continuous (fun p : ℝ × ℂ ↦ cubicAFELogProductWeightFinite p.1 X V p.2))

#check (@continuousOn_cubicAFERealProductWeightFinite_joint :
  ∀ {X : ℝ}, 1 / 2 < X → ∀ V : ℝ,
    ContinuousOn (fun p : ℝ × ℝ ↦ cubicAFERealProductWeightFinite p.1 X V p.2)
      {p | 0 < p.2})

#check (@continuous_cubicAFEProgressionCutoffSummand_joint :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < d → 0 < e →
    ∀ {δ : ℤ} (χ : CubicProgressionCutoff d e δ), 1 / 2 < X →
      Continuous (Function.uncurry (cubicAFEProgressionCutoffSummand W T X V χ)))

-- Joint compact support needs a nonzero time dilation, but does not require
-- the Mellin line hypothesis or positivity of either arithmetic index.
#check (@hasCompactSupport_cubicAFEProgressionCutoffSummand_joint :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ (X V : ℝ) {d e : ℕ} {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ),
    HasCompactSupport (Function.uncurry (cubicAFEProgressionCutoffSummand W T X V χ)))
