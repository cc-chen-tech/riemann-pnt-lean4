import HardyTheorem.SelbergDiagonalRemainderAbsorption

namespace HardyTheorem

/-! # Assembly of the exact diagonal estimate, isolated from scalar absorption. -/

theorem exists_norm_selbergDiagonalPhysicalOriginalSum_le_of_scales :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta x theta K : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → Real.exp 1 ≤ (X : ℝ) →
        1 ≤ x → 0 < theta → theta ≤ 1 / 2 → 0 ≤ K →
        delta ^ (1 / 2 : ℝ) * (X : ℝ) ^ 2 * x ≤ 1 →
        selbergDiagonalRemainderAbsorptionScale
          delta x theta (X : ℝ) ≤ K →
        ‖selbergDiagonalPhysicalOriginalSum delta x theta X‖ ≤
          (C + K) *
            (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
              (theta * Real.log (X : ℝ))) := by
  rcases exists_norm_selbergDiagonalPhysicalFloorKernelSum_le with
    ⟨A, hA, hfloor⟩
  let C : ℝ :=
    (Real.sqrt Real.pi / 2 + 1 / 2 * Real.Gamma (1 / 4)) * A
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro X delta x theta K hdelta0 hdelta1 hX hXexp hx htheta0
    hthetaHalf hK hmainGate hremGate
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hXone : (1 : ℝ) < (X : ℝ) :=
    lt_of_lt_of_le (by linarith [Real.exp_one_gt_two]) hXexp
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hpre := hfloor X delta x theta hdelta0 hdelta1 hX hXexp
    hx htheta0 hthetaHalf
  have hzero := selbergDiagonalSZeroContribution_le hA hdelta0 hdelta1
    hx0 htheta0 hlogX
  have htheta := selbergDiagonalSThetaContribution_le hA hdelta0 hdelta1
    hx0 (by exact_mod_cast (hX.trans' (by norm_num)) : 0 < (X : ℝ))
      hlogX htheta0 hthetaHalf hmainGate
  have hrem := selbergDiagonalRemainderTerm_le_target hK hdelta0 hx0
    htheta0 hlogX hremGate
  rw [selbergDiagonalPhysicalOriginalSum_eq_floorKernelSum
    hdelta0 hdelta1 hx0 htheta0 hthetaHalf]
  calc
    ‖selbergDiagonalPhysicalFloorKernelSum delta x theta X‖ ≤
      |selbergDiagonalSZeroCoefficient delta x theta| *
            (A / Real.log (X : ℝ)) +
          |selbergDiagonalSThetaCoefficient delta theta| *
            (A * ((X : ℝ) ^ (2 * theta)) / Real.log (X : ℝ)) +
          (X : ℝ) ^ 4 *
            (3 * (x ^ (1 - theta) / theta) +
              x ^ (1 - theta) *
                Real.log (2 + (X : ℝ) ^ 4 / delta)) := hpre
    _ ≤ (Real.sqrt Real.pi / 2 * A) *
          (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
            (theta * Real.log (X : ℝ))) +
        ((1 / 2 * Real.Gamma (1 / 4)) * A) *
          (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
            (theta * Real.log (X : ℝ))) +
        K * (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log (X : ℝ))) := by
      exact add_le_add (add_le_add hzero htheta) hrem
    _ = (C + K) *
        (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log (X : ℝ))) := by
      dsimp [C]
      ring

end HardyTheorem
