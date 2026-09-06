import HardyTheorem.SelbergDiagonalLogAbsorption

namespace HardyTheorem

/-! # Final parameter-uniform bound for Selberg's original diagonal sum. -/

theorem exists_norm_selbergDiagonalPhysicalOriginalSum_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (X : ℕ) (delta x theta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-c) →
        1 ≤ x → x ≤ (X : ℝ) ^ a →
        0 < theta → theta ≤ 1 / 2 →
        ‖selbergDiagonalPhysicalOriginalSum delta x theta X‖ ≤
          D * (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
            (theta * Real.log (X : ℝ))) := by
  rcases exists_uniform_selbergDiagonalRemainderAbsorptionScale_le
    ha hc hcEight hac with ⟨K, hK, hrem⟩
  rcases exists_norm_selbergDiagonalPhysicalOriginalSum_le_of_scales with
    ⟨C, hC, hassembled⟩
  refine ⟨C + K, add_nonneg hC hK, ?_⟩
  intro X delta x theta hdelta hdelta1 hX hXexp hXpow
    hx hxX htheta0 hthetaHalf
  have hXone : 1 ≤ (X : ℝ) := by exact_mod_cast (hX.trans' (by norm_num))
  have hx0 : 0 ≤ x := (zero_le_one.trans hx)
  have hmainGate := selbergDiagonalMainGate_of_parameters
    hdelta hdelta1 (hX.trans' (by norm_num)) ha hc hXpow hxX hac
  have hremGate := hrem hdelta hdelta1 hXone hx0 hxX htheta0.le
    hthetaHalf hXpow
  exact hassembled X delta x theta K hdelta hdelta1 hX hXexp hx
    htheta0 hthetaHalf hK hmainGate hremGate

end HardyTheorem
