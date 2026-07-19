import HardyTheorem.HardyPhaseMovingSecondMoment

open Complex MeasureTheory Set

namespace HardyTheorem

open OscillatoryIntegral

/-- An explicit constant for the dyadic second moment of the linearized Hardy
short sum.  Its dependence on the fixed window length is deliberately coarse;
Hardy--Littlewood only needs a finite constant after choosing that length. -/
noncomputable def hardyPhaseLinearizedDyadicSecondMomentConstant
    (delta : ℝ) : ℝ :=
  200 * delta +
    3200 * (5 * Real.pi + 4) * delta +
    8 * (5 * Real.pi + 4) * (204 * delta ^ 4 + 200 * delta)

/-- For every fixed admissible window, the complete linearized Hardy short sum
has second moment `O(T)` on the interior of a dyadic interval.  The stationary
scale hypotheses are separated here; a later threshold lemma discharges them
uniformly for large `T`. -/
theorem integral_normSq_hardyPhaseLinearizedSum_le_dyadic_mul
    {T delta : ℝ} (hT : 1 ≤ T) (hdelta : 1 ≤ delta)
    (hroom : delta ≤ T)
    (hscale : ∀ t ∈ Set.Icc T (2 * T - delta),
      8 ≤ hardyPhaseStationaryScale t)
    (hwindow : ∀ t ∈ Set.Icc T (2 * T - delta),
      delta ≤ hardyPhaseStationaryScale t) :
    (∫ t in T..2 * T - delta,
      Complex.normSq (hardyPhaseLinearizedSum T delta t)) ≤
        hardyPhaseLinearizedDyadicSecondMomentConstant delta * T := by
  let N := firstZetaApproximationCutoff T
  let K : ℝ := 5 * Real.pi + 4
  let A : ℝ := 204 * delta ^ 4 + 200 * delta
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hab : T ≤ 2 * T - delta := by linarith
  have hq : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hcutoff : 0 < firstZetaApproximationCutoff T := by
    exact Nat.floor_pos.mpr (by
      linarith)
  have hNle : (N : ℝ) ≤ 4 * T := by
    dsimp only [N, firstZetaApproximationCutoff]
    exact Nat.floor_le (by positivity)
  have hlen0 : 0 ≤ T - delta := sub_nonneg.mpr hroom
  have hlenEq : (2 * T - delta) - T = T - delta := by ring
  have hlen : |(2 * T - delta) - T| = T - delta := by
    rw [hlenEq, abs_of_nonneg hlen0]
  have hsqrtSq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
  have hinner :
      (Real.sqrt T) ^ 2 * (204 * delta ^ 4 / T ^ 2) +
          ((Real.sqrt T) ^ 2)⁻¹ * (200 * delta) = A / T := by
    rw [hsqrtSq]
    dsimp only [A]
    field_simp [hTpos.ne']
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hdiag :
      (T - delta) * (200 * delta) ≤ T * (200 * delta) := by
    exact mul_le_mul_of_nonneg_right (sub_le_self T hdelta0) (by positivity)
  have hendpoint :
      4 * K * N * (200 * delta) ≤
        T * (3200 * K * delta) := by
    calc
      4 * K * N * (200 * delta) ≤
          4 * K * (4 * T) * (200 * delta) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNle (by positivity)) (by positivity)
      _ = T * (3200 * K * delta) := by ring
  have hNdiv : (N : ℝ) / T ≤ 4 := by
    exact (div_le_iff₀ hTpos).2 (by simpa using hNle)
  have hvariationCoeff :
      2 * K * N * (A / T) ≤ 8 * K * A := by
    calc
      2 * K * N * (A / T) = 2 * K * A * ((N : ℝ) / T) := by
        field_simp [hTpos.ne']
      _ ≤ 2 * K * A * 4 :=
        mul_le_mul_of_nonneg_left hNdiv (by positivity)
      _ = 8 * K * A := by ring
  have hvariation :
      (T - delta) * (2 * K * N * (A / T)) ≤
        T * (8 * K * A) := by
    exact mul_le_mul (sub_le_self T hdelta0) hvariationCoeff
      (by positivity) hTpos.le
  have hraw := integral_normSq_hardyPhaseLinearizedSum_le
    (T := T) (delta := delta) (a := T) (b := 2 * T - delta)
      (q := Real.sqrt T) hTpos hab hdelta hq hcutoff hscale hwindow
  calc
    (∫ t in T..2 * T - delta,
        Complex.normSq (hardyPhaseLinearizedSum T delta t)) ≤
        (T - delta) * (200 * delta) +
          4 * K * N * (200 * delta) +
          (T - delta) * (2 * K * N * (A / T)) := by
      rw [hlenEq, abs_of_nonneg hlen0, hinner] at hraw
      simpa only [N, K] using hraw
    _ ≤ T * (200 * delta) +
          T * (3200 * K * delta) + T * (8 * K * A) :=
      add_le_add (add_le_add hdiag hendpoint) hvariation
    _ = hardyPhaseLinearizedDyadicSecondMomentConstant delta * T := by
      dsimp only [hardyPhaseLinearizedDyadicSecondMomentConstant, K, A]
      ring

end HardyTheorem
