import HardyTheorem.SelbergSqrtZetaSignedRationalWindowEnvelope

open Complex
open HardyTheorem

#check selbergSqrtZetaSignedRationalWindowEnvelopeSum
#check norm_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalWindowEnvelopeSum

example (kappa T : ℝ) (X : ℕ) {H t : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hH : 0 ≤ H) :
    ‖∫ v in 0..H,
      selbergSqrtZetaSignedComplexModel kappa T X (t + v)‖ ≤
      selbergSqrtZetaSignedRationalWindowEnvelopeSum T X H t :=
  norm_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalWindowEnvelopeSum
    kappa X hT hTt hH

#print axioms
  norm_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalWindowEnvelopeSum
