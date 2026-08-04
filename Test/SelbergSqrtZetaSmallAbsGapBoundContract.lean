import HardyTheorem.SelbergSqrtZetaSmallAbsGapBound

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

noncomputable example (N X : ℕ) (A B H : ℝ) : ℝ :=
  selbergSqrtZetaShortDirichletGapSum N X A B H

example (X : ℕ) (H eta : ℝ) : Set ℝ :=
  selbergSqrtZetaSmallAbsoluteMassStarts X H eta

example {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) {A B H : ℝ} :
    (∫ t in A..B,
        Complex.normSq
          (selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t)) ≤
      selbergSqrtZetaShortDirichletGapSum N X A B H :=
  integral_normSq_selbergSqrtZetaMollifiedShortDirichletPolynomial_le_gapSum'
    hN hX

example {absMass : ℝ → ℝ} {X N : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    {A B H eta R : ℝ} (hAB : A ≤ B)
    (hthreshold : 0 < H - eta - R)
    (hlower : ∀ t ∈ Icc A B,
      H - ‖selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t‖ - R ≤
        absMass t) :
    volume.real ({t | absMass t ≤ eta} ∩ Icc A B) ≤
      selbergSqrtZetaShortDirichletGapSum N X A B H /
        (H - eta - R) ^ 2 :=
  volume_smallMassStarts_inter_Icc_le_sqrtZetaGapSum
    hN hX hAB hthreshold hlower

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H eta : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T →
        0 < H - eta - 4 * C * H * X / Real.sqrt T →
        volume.real
            (selbergSqrtZetaSmallAbsoluteMassStarts X H eta ∩
              Icc T (2 * T - H)) ≤
          selbergSqrtZetaShortDirichletGapSum
              (firstZetaApproximationCutoff T) X T (2 * T - H) H /
            (H - eta - 4 * C * H * X / Real.sqrt T) ^ 2 :=
  exists_volume_selbergSqrtZetaSmallAbsoluteMassStarts_inter_Icc_le_gapSum

end HardyTheorem
