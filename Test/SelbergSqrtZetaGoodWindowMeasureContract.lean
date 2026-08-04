import HardyTheorem.SelbergSqrtZetaGoodWindowMeasure

open Complex MeasureTheory Set

namespace HardyTheorem

noncomputable example (X : ℕ) (H t : ℝ) : ℝ :=
  selbergSqrtZetaSignedShortIntegral X H t

example (X : ℕ) (H eta : ℝ) : Set ℝ :=
  selbergSqrtZetaExcessiveSignedMassStarts X H eta

example (X : ℕ) (H eta : ℝ) : Set ℝ :=
  selbergSqrtZetaGoodWindowStarts X H eta

example {X : ℕ} (hX : 1 ≤ X) {H eta t : ℝ} (hH : 0 ≤ H)
    (ht : t ∈ selbergSqrtZetaGoodWindowStarts X H eta) :
    ∃ u ∈ Set.Ioo t (t + H), HasLocalSignChangeAt hardyZ u :=
  exists_hardyZ_localSignChange_of_selbergSqrtZetaGoodStart hX hH ht

example (A T0 : ℝ) (X : ℝ → ℕ) (eta : ℝ → ℝ) (hA : 0 < A)
    (hX : ∀ T ≥ T0, 1 ≤ X T)
    (hsmall : ∀ T ≥ T0,
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) ∩
            selbergSqrtZetaSmallAbsoluteMassStarts
              (X T) (A / Real.log T) (eta T)) ≤ T / 24)
    (hexcessive : ∀ T ≥ T0,
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) ∩
            selbergSqrtZetaExcessiveSignedMassStarts
              (X T) (A / Real.log T) (eta T)) ≤ T / 24) :
    selberg_odd_zero_proportion_target :=
  selberg_odd_zero_proportion_target_of_sqrtZeta_good_window_bounds
    A T0 X eta hA hX hsmall hexcessive

end HardyTheorem
