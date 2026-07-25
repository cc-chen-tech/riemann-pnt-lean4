import PrimeNumberTheorem.VKEdgePiOverTwoRightTailBound

open Complex Filter Polynomial Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- A fixed linear coefficient dominating every height expression in the
localized rectangle when `T ∈ [12m + |v|, 12m + |v| + 1]`. -/
def localizedLinearHeightCoefficient (u v : ℝ) : ℝ :=
  20 + u + 2 * |v|

/-- Fixed constant in the coarse polynomial-exponential bound for the three
non-right edges. -/
def localizedOtherEdgeDecayConstant
    (A : ℂ[X]) (u v C : ℝ) : ℝ :=
  let S := ∑ k ∈ A.support, ‖A.coeff k‖
  let K := localizedLinearHeightCoefficient u v
  let R :=
    4 * C +
      ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2
  let B :=
    ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
      ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
      Real.pi + 1 + 2
  2 * S * K ^ (A.natDegree + 2) * (R * (u + 3) + B)

theorem localizedLinearHeightCoefficient_pos
    {u v : ℝ} (hu : 0 < u) :
    0 < localizedLinearHeightCoefficient u v := by
  unfold localizedLinearHeightCoefficient
  nlinarith [abs_nonneg v]

theorem localizedOtherEdgeDecayConstant_nonneg
    (A : ℂ[X]) {u v C : ℝ}
    (hu : 0 < u) (hC : 0 ≤ C) :
    0 ≤ localizedOtherEdgeDecayConstant A u v C := by
  have hseries :
      0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
    tsum_nonneg fun n => norm_nonneg _
  unfold localizedOtherEdgeDecayConstant
  dsimp
  positivity [localizedLinearHeightCoefficient_pos (v := v) hu]

private theorem log_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ x := by
  calc
    Real.log x ≤ x - 1 :=
      Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx)
    _ ≤ x := by linarith

set_option maxHeartbeats 1000000 in
/--
On every linearly selected good-height interval, the complete explicit
upper bound for the bottom, top, and left edges is dominated by a fixed
polynomial times `exp (-15m)`.
-/
theorem localizedOtherEdgeUpperBound_le_decayEnvelope
    (A : ℂ[X]) {u v C m T : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hC : 0 ≤ C)
    (hm : 1 ≤ m)
    (hT : T ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1)) :
    localizedOtherEdgeUpperBound A u v m C
        (12 * m + |v|) T ≤
      localizedOtherEdgeDecayConstant A u v C *
        m ^ (A.natDegree + 2) * Real.exp (-15 * m) := by
  let S : ℝ := ∑ k ∈ A.support, ‖A.coeff k‖
  let K : ℝ := localizedLinearHeightCoefficient u v
  let V : ℝ := ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1
  let R : ℝ := 4 * C + V + 2
  let B : ℝ :=
    V + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
      Real.pi + 1 + 2
  have hseries : 0 ≤ V := by
    dsimp [V]
    exact tsum_nonneg fun n => norm_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hK : 0 < K := by
    exact localizedLinearHeightCoefficient_pos (v := v) hu
  have hKm : 1 ≤ K * m := by
    dsimp [K, localizedLinearHeightCoefficient]
    nlinarith [abs_nonneg v]
  have hvScale : |v| ≤ |v| * m := by
    nlinarith [mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hm)]
  have huScale : u ≤ u * m := by
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hm)]
  have hTnonneg : 0 ≤ T := by
    have : 0 < 12 * m + |v| := by positivity
    exact this.le.trans hT.1
  have hTle : T ≤ K * m := by
    dsimp [K, localizedLinearHeightCoefficient]
    nlinarith [hT.2, abs_nonneg v]
  have hhorizontalArg :
      T + |v| + 3 ≤ K * m := by
    dsimp [K, localizedLinearHeightCoefficient]
    nlinarith [hT.2, abs_nonneg v]
  have hleftArg :
      u + T + |v| + 2 ≤ K * m := by
    dsimp [K, localizedLinearHeightCoefficient]
    nlinarith [hT.2, abs_nonneg v]
  have hlogArg :
      12 * m + |v| + 6 ≤ K * m := by
    dsimp [K, localizedLinearHeightCoefficient]
    nlinarith [hT.2, abs_nonneg v]
  have hTfour : T + 4 ≤ K * m := by
    dsimp [K, localizedLinearHeightCoefficient]
    nlinarith [hT.2, abs_nonneg v]
  have hlogH :
      Real.log (12 * m + |v| + 6) ≤ K * m :=
    (log_le_self_of_one_le (by nlinarith [abs_nonneg v])).trans hlogArg
  have hlogT :
      Real.log (T + 4) ≤ K * m :=
    (log_le_self_of_one_le (by linarith)).trans hTfour
  have hmaxHorizontal :
      max 1 (T + |v| + 3) ≤ K * m := by
    rw [max_le_iff]
    exact ⟨hKm, hhorizontalArg⟩
  have hmaxLeft :
      max 1 (u + T + |v| + 2) ≤ K * m := by
    rw [max_le_iff]
    exact ⟨hKm, hleftArg⟩
  have hgap : 12 * m ≤ T - |v| := by linarith [hT.1]
  have hexp :
      Real.exp (-(m * (T - |v|) ^ 2) / 2) ≤
        Real.exp (-15 * m) := by
    apply Real.exp_le_exp.mpr
    have hm0 : 0 ≤ m := zero_le_one.trans hm
    nlinarith [sq_nonneg (T - |v| - 12 * m)]
  have hkernel :
      max
          (C * (1 + Real.log (12 * m + |v| + 6)) ^ 2)
          V + 2 ≤
        R * (K * m) ^ 2 := by
    have hlogLower :
        0 ≤ Real.log (12 * m + |v| + 6) :=
      Real.log_nonneg (by nlinarith [abs_nonneg v])
    have honeLog :
        1 + Real.log (12 * m + |v| + 6) ≤
          2 * (K * m) := by
      nlinarith
    have hfirst :
        C * (1 + Real.log (12 * m + |v| + 6)) ^ 2 ≤
          4 * C * (K * m) ^ 2 := by
      have hsquare :=
        sq_le_sq₀
          (by positivity : 0 ≤
            1 + Real.log (12 * m + |v| + 6))
          (by positivity : 0 ≤ 2 * (K * m))
      have := hsquare.mpr honeLog
      nlinarith
    have hsecond :
        V + 2 ≤ (V + 2) * (K * m) ^ 2 := by
      have hVm : 0 ≤ V + 2 := by positivity
      have hsqOne : 1 ≤ (K * m) ^ 2 := by nlinarith
      nlinarith
    have hmax :
        max
            (C * (1 + Real.log (12 * m + |v| + 6)) ^ 2)
            V ≤
          (4 * C + V) * (K * m) ^ 2 := by
      rw [max_le_iff]
      constructor
      · have hsq : 0 ≤ (K * m) ^ 2 := sq_nonneg _
        nlinarith
      · have hsqOne : 1 ≤ (K * m) ^ 2 := by nlinarith
        nlinarith
    dsimp [R]
    have hsqOne : 1 ≤ (K * m) ^ 2 := by nlinarith
    nlinarith
  have hleftLog :
      leftLogDerivBound T + 1 ≤ B * (K * m) := by
    have hB0 :
        0 ≤ V + ‖Complex.log Real.pi‖ +
            2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
            Real.pi + 1 := by
      positivity
    dsimp [B, leftLogDerivBound]
    nlinarith
  have hhorizontal :
      localizedHorizontalEdgeUpperBound A u v m C
          (12 * m + |v|) T ≤
        S * R * (u + 3) * K ^ (A.natDegree + 2) *
          m ^ (A.natDegree + 2) * Real.exp (-15 * m) := by
    unfold localizedHorizontalEdgeUpperBound
    change
      ((S * max 1 (T + |v| + 3) ^ A.natDegree *
          Real.exp (-(m * (T - |v|) ^ 2) / 2)) *
        (max
          (C * (1 + Real.log (12 * m + |v| + 6)) ^ 2)
          V + 2)) * (u + 3) ≤ _
    have hpow :
        max 1 (T + |v| + 3) ^ A.natDegree ≤
          (K * m) ^ A.natDegree := by gcongr
    calc
      _ ≤
          ((S * (K * m) ^ A.natDegree *
              Real.exp (-15 * m)) *
            (R * (K * m) ^ 2)) * (u + 3) := by
        gcongr
      _ = _ := by
        rw [mul_pow]
        ring
  have hleft :
      localizedLeftEdgeUpperBound A u v m T ≤
        2 * S * B * K ^ (A.natDegree + 2) *
          m ^ (A.natDegree + 2) * Real.exp (-15 * m) := by
    unfold localizedLeftEdgeUpperBound
    change
      (S * max 1 (u + T + |v| + 2) ^ A.natDegree *
          Real.exp (-15 * m) * (leftLogDerivBound T + 1)) *
        (2 * T) ≤ _
    have hpow :
        max 1 (u + T + |v| + 2) ^ A.natDegree ≤
          (K * m) ^ A.natDegree := by gcongr
    calc
      _ ≤
          (S * (K * m) ^ A.natDegree *
              Real.exp (-15 * m) * (B * (K * m))) *
            (2 * (K * m)) := by
        gcongr
        exact add_nonneg (leftLogDerivBound_nonneg hTnonneg) (by norm_num)
      _ = _ := by
        rw [mul_pow]
        ring
  unfold localizedOtherEdgeUpperBound
  unfold localizedOtherEdgeDecayConstant
  dsimp [S, K, V, R, B]
  calc
    2 * localizedHorizontalEdgeUpperBound A u v m C
          (12 * m + |v|) T +
        localizedLeftEdgeUpperBound A u v m T ≤
      2 *
          (S * R * (u + 3) * K ^ (A.natDegree + 2) *
            m ^ (A.natDegree + 2) * Real.exp (-15 * m)) +
        2 * S * B * K ^ (A.natDegree + 2) *
          m ^ (A.natDegree + 2) * Real.exp (-15 * m) := by
      gcongr
    _ = _ := by ring

theorem tendsto_localizedOtherEdgeDecayEnvelope
    (A : ℂ[X]) (u v C : ℝ) :
    Tendsto
      (fun m : ℝ =>
        localizedOtherEdgeDecayConstant A u v C *
          m ^ (A.natDegree + 2) * Real.exp (-15 * m))
      atTop (𝓝 0) := by
  have hbase :
      Tendsto
        (fun m : ℝ =>
          m ^ (A.natDegree + 2) * Real.exp (-15 * m))
        atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((A.natDegree + 2 : ℕ) : ℝ) 15 (by norm_num)
  simpa [mul_assoc] using
    hbase.const_mul (localizedOtherEdgeDecayConstant A u v C)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
