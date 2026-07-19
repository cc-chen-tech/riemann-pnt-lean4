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

/-- After fixing a positive window length, the stationary-scale hypotheses in
the dyadic estimate hold uniformly above an explicit threshold. -/
theorem exists_integral_normSq_hardyPhaseLinearizedSum_le_mul
    (delta : ℝ) (hdelta : 1 ≤ delta) :
    ∃ C > 0, ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T ≥ T0,
      (∫ t in T..2 * T - delta,
        Complex.normSq (hardyPhaseLinearizedSum T delta t)) ≤ C * T := by
  let C := hardyPhaseLinearizedDyadicSecondMomentConstant delta
  let T0 : ℝ := max 1
    (max delta (max (128 * Real.pi) (2 * Real.pi * delta ^ 2)))
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hC : 0 < C := by
    dsimp only [C, hardyPhaseLinearizedDyadicSecondMomentConstant]
    positivity
  refine ⟨C, hC, T0, ?_, ?_⟩
  · dsimp only [T0]
    exact le_max_left _ _
  intro T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hrest :
      max delta (max (128 * Real.pi) (2 * Real.pi * delta ^ 2)) ≤ T :=
    (le_max_right (1 : ℝ) _).trans hT
  have hroom : delta ≤ T := (le_max_left _ _).trans hrest
  have hrest' : max (128 * Real.pi) (2 * Real.pi * delta ^ 2) ≤ T :=
    (le_max_right delta _).trans hrest
  have hscaleT : 128 * Real.pi ≤ T := (le_max_left _ _).trans hrest'
  have hwindowT : 2 * Real.pi * delta ^ 2 ≤ T :=
    (le_max_right _ _).trans hrest'
  have hscale : ∀ t ∈ Set.Icc T (2 * T - delta),
      8 ≤ hardyPhaseStationaryScale t := by
    intro t ht
    unfold hardyPhaseStationaryScale
    have ht0 : 0 ≤ t := (zero_le_one.trans hT1).trans ht.1
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 8) (by positivity)]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    calc
      8 ^ 2 * (2 * Real.pi) = 128 * Real.pi := by ring
      _ ≤ T := hscaleT
      _ ≤ t := ht.1
  have hwindow : ∀ t ∈ Set.Icc T (2 * T - delta),
      delta ≤ hardyPhaseStationaryScale t := by
    intro t ht
    unfold hardyPhaseStationaryScale
    have ht0 : 0 ≤ t := (zero_le_one.trans hT1).trans ht.1
    rw [Real.le_sqrt hdelta0 (by positivity)]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    calc
      delta ^ 2 * (2 * Real.pi) = 2 * Real.pi * delta ^ 2 := by ring
      _ ≤ T := hwindowT
      _ ≤ t := ht.1
  exact integral_normSq_hardyPhaseLinearizedSum_le_dyadic_mul
    hT1 hdelta hroom hscale hwindow

end HardyTheorem
