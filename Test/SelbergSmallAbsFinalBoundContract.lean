import HardyTheorem.SelbergSmallAbsFinalBound

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Contract for the conditional `T / 24` small-absolute-mass bound

The example below applies the conditional final step at a schematic choice of
parameters, exposing the exact hypothesis shape that any explicit gap-sum upper
bound must supply.
-/

/-- Schematic application: the conditional theorem is usable at concrete
parameter shape. -/
example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ (X : ℕ) (A T eta M : ℝ), 2 ≤ X → T0 ≤ T → 0 < A → A ≤ Real.log T →
        0 < A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T →
        selbergShortDirichletGapSum (firstZetaApproximationCutoff T) X T
          (2 * T - A / Real.log T) (A / Real.log T) ≤ M →
        M ≤ T * (A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T) ^ 2 / 24 →
        volume.real (Set.Icc T (2 * T - A / Real.log T) ∩
          selbergSmallAbsoluteMassStarts X (A / Real.log T) eta) ≤ T / 24 :=
  exists_volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_T_div_24_of_gapSum_le

#print axioms
  exists_volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_T_div_24_of_gapSum_le

end HardyTheorem
