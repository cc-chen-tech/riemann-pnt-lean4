import PrimeNumberTheorem.ZeroDensityLayerBudgetDirectL2NumericalCore

/-!
# Shared outer-height feasibility for short direct-L2 intervals

The intrinsic direct-L2 criterion only asks for a cutoff below `lambda / 2`.
If a consumer additionally requires the existing L1 outer cap
`alpha < 2 * beta - 1`, a stronger condition appears.  This file isolates that
extra condition and shows how shortening to `lambda = 1 + epsilon` restores a
positive parameter range exactly when `beta > 2/3` in the polylogarithmic
Occupancy case.
-/

namespace PrimeNumberTheorem

/-- Outer-height cap inherited from the existing L1 two-height geometry. -/
def directL2SharedOuterCap (beta : ℝ) : ℝ :=
  2 * beta - 1

/-- Maximum short-interval increment compatible with the shared outer cap. -/
def directL2SharedOuterEpsilonThreshold (beta theta : ℝ) : ℝ :=
  (2 - theta) * (2 * beta - 1) / (2 * (1 - beta)) - 1

/-- Polylogarithmic specialization of the shared-cap epsilon threshold. -/
def directL2PolylogSharedOuterEpsilonThreshold (beta : ℝ) : ℝ :=
  (3 * beta - 2) / (1 - beta)

/-- Exact shared-cap condition for an arbitrary outer interval exponent. -/
theorem directL2CriticalRightHeight_lt_sharedOuterCap_iff
    (beta lambda theta : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (htheta : theta < 2) :
    directL2CriticalRightHeight beta lambda theta <
        directL2SharedOuterCap beta ↔
      theta <
        2 - 2 * lambda * (1 - beta) / directL2SharedOuterCap beta := by
  have hthetaDen : 0 < 2 - theta := sub_pos.mpr htheta
  have hcap : 0 < directL2SharedOuterCap beta := by
    dsimp [directL2SharedOuterCap]
    nlinarith
  constructor
  · intro h
    have hcross := (div_lt_iff₀ hthetaDen).mp h
    have hratio :
        2 * lambda * (1 - beta) / directL2SharedOuterCap beta <
          2 - theta := by
      apply (div_lt_iff₀ hcap).mpr
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
    nlinarith
  · intro h
    have hratio :
        2 * lambda * (1 - beta) / directL2SharedOuterCap beta <
          2 - theta := by
      nlinarith
    have hcross := (div_lt_iff₀ hcap).mp hratio
    apply (div_lt_iff₀ hthetaDen).mpr
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

/-- For `lambda = 1 + epsilon`, the shared-cap condition is exactly an upper
bound on `epsilon`. -/
theorem directL2CriticalRightHeight_shortInterval_iff
    (beta theta epsilon : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (htheta : theta < 2) :
    directL2CriticalRightHeight beta (1 + epsilon) theta <
        directL2SharedOuterCap beta ↔
      epsilon < directL2SharedOuterEpsilonThreshold beta theta := by
  have hthetaDen : 0 < 2 - theta := sub_pos.mpr htheta
  have hbetaDen : 0 < 2 * (1 - beta) := by nlinarith
  constructor
  · intro h
    have hcross := (div_lt_iff₀ hthetaDen).mp h
    have hratio :
        epsilon + 1 <
          ((2 - theta) * (2 * beta - 1)) / (2 * (1 - beta)) := by
      apply (lt_div_iff₀ hbetaDen).mpr
      dsimp [directL2SharedOuterCap] at hcross
      nlinarith
    dsimp [directL2SharedOuterEpsilonThreshold]
    nlinarith
  · intro h
    have hratio :
        epsilon + 1 <
          ((2 - theta) * (2 * beta - 1)) / (2 * (1 - beta)) := by
      dsimp [directL2SharedOuterEpsilonThreshold] at h
      nlinarith
    have hcross := (lt_div_iff₀ hbetaDen).mp hratio
    apply (div_lt_iff₀ hthetaDen).mpr
    dsimp [directL2SharedOuterCap]
    nlinarith

/-- At `theta = 0`, the general short-interval threshold reduces to the
explicit ratio `(3 * beta - 2) / (1 - beta)`. -/
theorem directL2SharedOuterEpsilonThreshold_zero
    (beta : ℝ)
    (hbetaOne : beta < 1) :
    directL2SharedOuterEpsilonThreshold beta 0 =
      directL2PolylogSharedOuterEpsilonThreshold beta := by
  have hden : 1 - beta ≠ 0 := ne_of_gt (sub_pos.mpr hbetaOne)
  simp [directL2SharedOuterEpsilonThreshold,
    directL2PolylogSharedOuterEpsilonThreshold]
  field_simp [hden]
  ring

/-- Polylogarithmic shared-cap feasibility on `[Y, Y^(1+epsilon)]`. -/
theorem directL2Polylog_shortInterval_sharedOuter_iff
    (beta epsilon : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1) :
    directL2CriticalRightHeight beta (1 + epsilon) 0 <
        directL2SharedOuterCap beta ↔
      epsilon < directL2PolylogSharedOuterEpsilonThreshold beta := by
  rw [directL2CriticalRightHeight_shortInterval_iff beta 0 epsilon
    hbetaHalf hbetaOne (by norm_num)]
  rw [directL2SharedOuterEpsilonThreshold_zero beta hbetaOne]

/-- The polylogarithmic short-interval range is positive exactly beyond
`beta = 2/3`. -/
theorem directL2PolylogSharedOuterEpsilonThreshold_pos_iff
    (beta : ℝ)
    (hbetaOne : beta < 1) :
    0 < directL2PolylogSharedOuterEpsilonThreshold beta ↔
      2 / 3 < beta := by
  have hden : 0 < 1 - beta := sub_pos.mpr hbetaOne
  constructor
  · intro h
    have hnum : 0 < 3 * beta - 2 :=
      (div_pos_iff.mp h).resolve_right (by
        intro hnegative
        nlinarith)
    nlinarith
  · intro h
    exact div_pos (by nlinarith) hden

/-- Every positive epsilon below the explicit threshold gives a shared outer
height. -/
theorem directL2Polylog_shortInterval_sharedOuter
    (beta epsilon : ℝ)
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hepsilon : epsilon < directL2PolylogSharedOuterEpsilonThreshold beta) :
    directL2CriticalRightHeight beta (1 + epsilon) 0 <
      directL2SharedOuterCap beta := by
  have hbetaHalf : 1 / 2 < beta := by nlinarith
  exact (directL2Polylog_shortInterval_sharedOuter_iff
    beta epsilon hbetaHalf hbetaOne).2 hepsilon

/-- Beyond `beta = 2/3`, a positive short-interval increment compatible with
the shared outer cap always exists. -/
theorem exists_pos_directL2Polylog_sharedOuterEpsilon
    (beta : ℝ)
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      epsilon < directL2PolylogSharedOuterEpsilonThreshold beta ∧
      directL2CriticalRightHeight beta (1 + epsilon) 0 <
        directL2SharedOuterCap beta := by
  have hthreshold :
      0 < directL2PolylogSharedOuterEpsilonThreshold beta :=
    (directL2PolylogSharedOuterEpsilonThreshold_pos_iff beta hbetaOne).2 hbeta
  let epsilon := directL2PolylogSharedOuterEpsilonThreshold beta / 2
  have hepsilonPos : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilonLt :
      epsilon < directL2PolylogSharedOuterEpsilonThreshold beta := by
    dsimp [epsilon]
    nlinarith
  exact ⟨epsilon, hepsilonPos, hepsilonLt,
    directL2Polylog_shortInterval_sharedOuter
      beta epsilon hbeta hbetaOne hepsilonLt⟩

/-- Expanded numerator form of the shared-outer short-interval threshold. -/
theorem directL2SharedOuterEpsilonThreshold_eq_expanded
    (beta theta : ℝ)
    (hbetaOne : beta < 1) :
    directL2SharedOuterEpsilonThreshold beta theta =
      (2 * (3 * beta - 2) - theta * (2 * beta - 1)) /
        (2 * (1 - beta)) := by
  have hden : 1 - beta ≠ 0 := ne_of_gt (sub_pos.mpr hbetaOne)
  simp [directL2SharedOuterEpsilonThreshold]
  field_simp [hden]
  ring

/-- A positive shared-outer short interval exists precisely below this
Occupancy threshold. -/
theorem directL2SharedOuterEpsilonThreshold_pos_iff
    (beta theta : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1) :
    0 < directL2SharedOuterEpsilonThreshold beta theta ↔
      theta < 2 * (3 * beta - 2) / (2 * beta - 1) := by
  have hden : 0 < 2 * (1 - beta) := by nlinarith
  have hcap : 0 < 2 * beta - 1 := by nlinarith
  rw [directL2SharedOuterEpsilonThreshold_eq_expanded beta theta hbetaOne]
  constructor
  · intro h
    have hnum : 0 < 2 * (3 * beta - 2) - theta * (2 * beta - 1) := by
      rcases (div_pos_iff.mp h) with hpositive | hnegative
      · exact hpositive.1
      · nlinarith [hnegative.2, hden]
    apply (lt_div_iff₀ hcap).mpr
    nlinarith
  · intro h
    have hcross := (lt_div_iff₀ hcap).mp h
    exact div_pos (by nlinarith) hden

/-- Existence form of the positive-short-interval criterion. -/
theorem exists_pos_directL2_sharedOuterEpsilon_iff
    (beta theta : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1) :
    (∃ epsilon : ℝ,
      0 < epsilon ∧
        epsilon < directL2SharedOuterEpsilonThreshold beta theta) ↔
      theta < 2 * (3 * beta - 2) / (2 * beta - 1) := by
  rw [← directL2SharedOuterEpsilonThreshold_pos_iff
    beta theta hbetaHalf hbetaOne]
  constructor
  · rintro ⟨epsilon, hepsilonPos, hepsilonLt⟩
    nlinarith
  · intro hthreshold
    refine ⟨directL2SharedOuterEpsilonThreshold beta theta / 2, ?_, ?_⟩
    · positivity
    · nlinarith

/-- The intrinsic and shared-positive-interval thresholds agree at
`beta = 3/4`. -/
theorem directL2_thresholds_eq_at_threeFourths :
    4 * (3 / 4 : ℝ) - 2 =
      2 * (3 * (3 / 4 : ℝ) - 2) / (2 * (3 / 4 : ℝ) - 1) := by
  norm_num

/-- Below `beta = 3/4`, positive shared-short-interval feasibility is the
stronger restriction. -/
theorem directL2_sharedThreshold_lt_intrinsic_of_lt_threeFourths
    (beta : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaThreeFourths : beta < 3 / 4) :
    2 * (3 * beta - 2) / (2 * beta - 1) < 4 * beta - 2 := by
  have hcap : 0 < 2 * beta - 1 := by nlinarith
  apply (div_lt_iff₀ hcap).mpr
  have hfirst : 4 * beta - 3 < 0 := by nlinarith
  have hsecond : beta - 1 < 0 := by nlinarith
  have hproduct : 0 < (4 * beta - 3) * (beta - 1) :=
    mul_pos_of_neg_of_neg hfirst hsecond
  nlinarith

/-- Above `beta = 3/4`, the intrinsic direct-L2 threshold is the stronger
restriction. -/
theorem directL2_intrinsicThreshold_lt_shared_of_threeFourths_lt
    (beta : ℝ)
    (hbetaThreeFourths : 3 / 4 < beta)
    (hbetaOne : beta < 1) :
    4 * beta - 2 < 2 * (3 * beta - 2) / (2 * beta - 1) := by
  have hcap : 0 < 2 * beta - 1 := by nlinarith
  apply (lt_div_iff₀ hcap).mpr
  have hfirst : 0 < 4 * beta - 3 := by nlinarith
  have hsecond : beta - 1 < 0 := by nlinarith
  have hproduct : (4 * beta - 3) * (beta - 1) < 0 :=
    mul_neg_of_pos_of_neg hfirst hsecond
  nlinarith

end PrimeNumberTheorem
