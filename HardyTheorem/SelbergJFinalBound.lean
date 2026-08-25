import HardyTheorem.SelbergJDiagonalBridge
import HardyTheorem.SelbergDiagonalFinalBound
import HardyTheorem.SelbergOffDiagonalAbsorption

namespace HardyTheorem

/-! # Final object-level bound for Selberg's physical `J(x, theta)` -/

theorem selbergJ_eq_diagonalPhysical_add_offDiagonalPhysical
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    {X : ℕ} (hX : 2 ≤ X) :
    (selbergJ delta x theta X : ℂ) =
      selbergDiagonalPhysicalOriginalSum delta x theta X +
        selbergPhysicalOffDiagonalSum delta x theta X := by
  rw [selbergJ_eq_diagonal_add_forward_add_reverse
    hdelta hdelta1 htheta.le hx hX,
    selbergJDiagonalPart_eq_physicalOriginalSum
      hdelta hdelta1 hx htheta hthetaHalf hX,
    selbergJForwardPart_eq_physicalPositiveOffDiagonalSum
      hdelta hdelta1 htheta.le hx hX,
    selbergJReversePart_eq_physicalReverseOffDiagonalSum
      hdelta hdelta1 htheta.le hx hX]
  unfold selbergPhysicalOffDiagonalSum
  ring

theorem exists_abs_selbergJ_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta x theta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-c) →
        1 ≤ x → x ≤ (X : ℝ) ^ a →
        0 < theta → theta ≤ 1 / 2 →
        |selbergJ delta x theta X| ≤
          C * (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
            (theta * Real.log (X : ℝ))) := by
  rcases exists_norm_selbergDiagonalPhysicalOriginalSum_le
    ha hc hcEight hac with ⟨D, hD, hdiag⟩
  rcases exists_selbergOffDiagonalOscillatoryMajorant_le
    hc hcEight with ⟨K, hK, hoffMajor⟩
  refine ⟨D + K, add_nonneg hD hK, ?_⟩
  intro X delta x theta hdelta hdelta1 hX hXexp hXpow
    hx hxX htheta hthetaHalf
  let M : ℝ := delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
    (theta * Real.log (X : ℝ))
  have hdiag' := hdiag X delta x theta hdelta hdelta1 hX hXexp
    hXpow hx hxX htheta hthetaHalf
  have hoffNorm := norm_selbergPhysicalOffDiagonalSum_le_oscillatoryMajorant
    hdelta hdelta1 hx htheta.le hX
  have hoffM := hoffMajor X delta x theta hdelta hdelta1 hXexp
    hXpow hx htheta hthetaHalf
  have hoff : ‖selbergPhysicalOffDiagonalSum delta x theta X‖ ≤ K * M :=
    hoffNorm.trans (by simpa only [M] using hoffM)
  have hj := selbergJ_eq_diagonalPhysical_add_offDiagonalPhysical
    hdelta hdelta1 hx htheta hthetaHalf hX
  calc
    |selbergJ delta x theta X| = ‖(selbergJ delta x theta X : ℂ)‖ := by simp
    _ = ‖selbergDiagonalPhysicalOriginalSum delta x theta X +
        selbergPhysicalOffDiagonalSum delta x theta X‖ := by rw [hj]
    _ ≤ ‖selbergDiagonalPhysicalOriginalSum delta x theta X‖ +
        ‖selbergPhysicalOffDiagonalSum delta x theta X‖ := norm_add_le _ _
    _ ≤ D * M + K * M := add_le_add (by simpa only [M] using hdiag') hoff
    _ = (D + K) * M := by ring
    _ = _ := rfl

end HardyTheorem
