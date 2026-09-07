import PrimeNumberTheorem.MWKFCubicAFECompletedPower
import PrimeNumberTheorem.MWKFCubicAFELatticeDecay

open Set

namespace PrimeNumberTheorem.MWKFCubic

/-!
# A translation-uniform lattice bound at the actual completion endpoint

For epsilon=1/(2*2^J), reindex at floor(epsilon*s-b). The lower
spacing epsilon/(1+epsilon*s) is positive for every positive real s.
The explicit constant retains its depth and modulus dependence. It is
not a uniform-in-depth estimate and gives no Mobius cancellation.
-/

theorem measurable_cubicAFECompletedHalfLinePower (X : ℝ) (J : ℕ) :
    Measurable (cubicAFECompletedHalfLinePower X J) :=
  (measurable_id.pow measurable_const).indicator measurableSet_Ioi

theorem cubicAFECompletedHalfLinePower_le_endpoint {X : ℝ} (hX : 1 / 2 < X)
    (J : ℕ) (x : ℝ) :
    cubicAFECompletedHalfLinePower X J x ≤ cubicAFECompletionLowerEndpoint J ^ (-X - 1 / 2) := by
  by_cases hx : cubicAFECompletionLowerEndpoint J < x
  · rw [cubicAFECompletedHalfLinePower, indicator_of_mem (show x ∈ Ioi _ from hx)]
    exact Real.rpow_le_rpow_of_nonpos (cubicAFECompletionLowerEndpoint_pos J) hx.le (by linarith)
  · rw [cubicAFECompletedHalfLinePower, indicator_of_notMem (show x ∉ Ioi _ from hx)]
    exact Real.rpow_nonneg (cubicAFECompletionLowerEndpoint_pos J).le _

noncomputable def cubicAFECompletedLatticeConstant (X : ℝ) (J : ℕ) (s : ℝ) : ℝ :=
  (cubicAFECompletionLowerEndpoint J / (1 + cubicAFECompletionLowerEndpoint J * s)) ^ (-X - 1 / 2) *
    ∑' n : ℤ, |(n : ℝ)| ^ (-X - 1 / 2)

theorem cubicAFECompletedLatticeConstant_nonneg (X : ℝ) (J : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ cubicAFECompletedLatticeConstant X J s := by
  have hε := cubicAFECompletionLowerEndpoint_pos J
  unfold cubicAFECompletedLatticeConstant
  apply mul_nonneg
  · apply Real.rpow_nonneg
    exact (div_pos (cubicAFECompletionLowerEndpoint_pos J) (by positivity)).le
  · exact tsum_nonneg (fun n ↦ Real.rpow_nonneg (abs_nonneg (n : ℝ)) _)

private theorem completed_lattice_le_shifted
    {X s : ℝ} (hX : 1 / 2 < X) (hs : 0 < s) (J : ℕ) (b : ℝ) (δ : ℤ) :
    cubicAFECompletedHalfLinePower X J (((δ : ℝ) + b) / s) ≤
      (cubicAFECompletionLowerEndpoint J / (1 + cubicAFECompletionLowerEndpoint J * s)) ^ (-X - 1 / 2) *
        |((δ - ⌊cubicAFECompletionLowerEndpoint J * s - b⌋ : ℤ) : ℝ)| ^ (-X - 1 / 2) := by
  let ε := cubicAFECompletionLowerEndpoint J
  have hε : 0 < ε := cubicAFECompletionLowerEndpoint_pos J
  have hc : 0 < ε / (1 + ε * s) := div_pos hε (by positivity)
  by_cases hz : δ ≤ ⌊ε * s - b⌋
  · have hy : ((δ : ℝ) + b) / s ≤ ε := by
      apply (div_le_iff₀ hs).mpr
      have hh : (δ : ℝ) ≤ (⌊ε * s - b⌋ : ℤ) := by exact_mod_cast hz
      linarith [Int.floor_le (ε * s - b)]
    rw [cubicAFECompletedHalfLinePower,
      indicator_of_notMem (show ((δ : ℝ) + b) / s ∉ Ioi ε from not_lt.mpr hy)]
    exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (abs_nonneg _) _)
  · let n : ℝ := ((δ - ⌊ε * s - b⌋ : ℤ) : ℝ)
    have hn : 1 ≤ n := by
      dsimp [n]
      exact_mod_cast (show (1 : ℤ) ≤ δ - ⌊ε * s - b⌋ by omega)
    have hy : ε < ((δ : ℝ) + b) / s := by
      apply (lt_div_iff₀ hs).mpr
      have hh : (⌊ε * s - b⌋ : ℝ) + 1 ≤ δ := by exact_mod_cast (show ⌊ε * s - b⌋ + 1 ≤ δ by omega)
      linarith [Int.lt_floor_add_one (ε * s - b)]
    have ht : ε * s + n - 1 ≤ (δ : ℝ) + b := by
      dsimp [n]
      push_cast
      linarith [Int.floor_le (ε * s - b), Int.lt_floor_add_one (ε * s - b)]
    have hlower : (ε / (1 + ε * s)) * n ≤ ((δ : ℝ) + b) / s := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity : 0 < 1 + ε * s) hs]
      have hh := mul_le_mul_of_nonneg_right ht (show 0 ≤ 1 + ε * s by positivity)
      nlinarith [sq_nonneg (ε * s)]
    rw [cubicAFECompletedHalfLinePower, indicator_of_mem (show ((δ : ℝ) + b) / s ∈ Ioi ε from hy)]
    calc
      _ ≤ ((ε / (1 + ε * s)) * n) ^ (-X - 1 / 2) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hc (by linarith)) hlower (by linarith)
      _ = _ := by rw [Real.mul_rpow hc.le (by linarith), abs_of_nonneg (by linarith : 0 ≤ n)]

private theorem completed_shifted_summable {X : ℝ} (hX : 1 / 2 < X) (s : ℝ) (J : ℕ) (b : ℝ) :
    Summable (fun δ : ℤ ↦
      (cubicAFECompletionLowerEndpoint J / (1 + cubicAFECompletionLowerEndpoint J * s)) ^ (-X - 1 / 2) *
        |((δ - ⌊cubicAFECompletionLowerEndpoint J * s - b⌋ : ℤ) : ℝ)| ^ (-X - 1 / 2)) := by
  have hp : Summable (fun n : ℤ ↦ |(n : ℝ)| ^ (-X - 1 / 2)) := by
    simpa only [neg_add, sub_eq_add_neg] using Real.summable_abs_int_rpow (by linarith : 1 < X + 1 / 2)
  exact (hp.mul_left _).comp_injective (fun a b h ↦ by omega)

theorem summable_cubicAFECompletedLatticePower {X s : ℝ} (hX : 1 / 2 < X) (hs : 0 < s)
    (J : ℕ) (b : ℝ) :
    Summable (fun δ : ℤ ↦ cubicAFECompletedHalfLinePower X J (((δ : ℝ) + b) / s)) :=
  Summable.of_nonneg_of_le (fun _δ ↦ cubicAFECompletedHalfLinePower_nonneg X J _)
    (completed_lattice_le_shifted hX hs J b) (completed_shifted_summable hX s J b)

theorem tsum_cubicAFECompletedLatticePower_le {X s : ℝ} (hX : 1 / 2 < X) (hs : 0 < s)
    (J : ℕ) (b : ℝ) :
    (∑' δ : ℤ, cubicAFECompletedHalfLinePower X J (((δ : ℝ) + b) / s)) ≤
      cubicAFECompletedLatticeConstant X J s := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun δ ↦ δ - ⌊cubicAFECompletionLowerEndpoint J * s - b⌋
      invFun := fun n ↦ n + ⌊cubicAFECompletionLowerEndpoint J * s - b⌋
      left_inv := fun δ ↦ sub_add_cancel _ _
      right_inv := fun n ↦ add_sub_cancel_right _ _ }
  calc
    _ ≤ ∑' δ : ℤ,
        (cubicAFECompletionLowerEndpoint J / (1 + cubicAFECompletionLowerEndpoint J * s)) ^ (-X - 1 / 2) *
          |((δ - ⌊cubicAFECompletionLowerEndpoint J * s - b⌋ : ℤ) : ℝ)| ^ (-X - 1 / 2) :=
      Summable.tsum_le_tsum (completed_lattice_le_shifted hX hs J b)
        (summable_cubicAFECompletedLatticePower hX hs J b) (completed_shifted_summable hX s J b)
    _ = ∑' n : ℤ,
        (cubicAFECompletionLowerEndpoint J / (1 + cubicAFECompletionLowerEndpoint J * s)) ^ (-X - 1 / 2) *
          |(n : ℝ)| ^ (-X - 1 / 2) :=
      e.tsum_eq (fun n : ℤ ↦
        (cubicAFECompletionLowerEndpoint J / (1 + cubicAFECompletionLowerEndpoint J * s)) ^ (-X - 1 / 2) *
          |(n : ℝ)| ^ (-X - 1 / 2))
    _ = _ := tsum_mul_left

end PrimeNumberTheorem.MWKFCubic
