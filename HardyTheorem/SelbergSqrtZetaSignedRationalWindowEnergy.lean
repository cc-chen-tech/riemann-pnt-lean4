import HardyTheorem.SelbergSqrtZetaSignedRationalEnergy
import HardyTheorem.SelbergSqrtZetaSignedRationalSquareEnvelope
import HardyTheorem.SelbergSqrtZetaSignedRationalWindowEnvelope

/-!
# Energy bound for rational Selberg short-window envelopes

The stationary-safe square packing estimate combines with finite
Cauchy--Schwarz.  The tangent-line error is retained explicitly through the
coefficient `L1` norm rather than hidden in a support-cardinality loss.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

private theorem stationaryMinReciprocalEnvelope_nonneg
    {H xi x : ℝ} (hH : 0 ≤ H) :
    0 ≤ MathlibAux.stationaryMinReciprocalEnvelope H xi x := by
  unfold MathlibAux.stationaryMinReciprocalEnvelope
  split_ifs
  · exact hH
  · exact le_min hH (div_nonneg (by norm_num) (abs_nonneg _))

/-- The exact theta-frequency envelope is at most the stationary-safe
reciprocal envelope plus the uniform tangent-line error. -/
theorem thetaFrequencyShortIntegralEnvelope_le_stationary_add_error
    (omega : ℝ) {T H t : ℝ} (hT : 0 < T) (hH : 0 ≤ H) :
    thetaFrequencyShortIntegralEnvelope omega T H t ≤
      MathlibAux.stationaryMinReciprocalEnvelope
        H (-deriv thetaModel t) omega +
        H ^ 3 / (2 * T) := by
  unfold thetaFrequencyShortIntegralEnvelope
  split_ifs with hfreq
  · have homega : omega = -deriv thetaModel t := by linarith
    rw [MathlibAux.stationaryMinReciprocalEnvelope, if_pos homega]
    have herr : 0 ≤ H ^ 3 / (2 * T) := by positivity
    linarith
  · have homega : omega ≠ -deriv thetaModel t := by
      intro homega
      exfalso
      apply hfreq
      rw [homega]
      ring
    rw [MathlibAux.stationaryMinReciprocalEnvelope, if_neg homega]
    have habs :
        |omega - -deriv thetaModel t| =
          |deriv thetaModel t + omega| := by
      congr 1
      ring
    rw [habs]

private theorem thetaFrequencyShortIntegralEnvelope_nonneg
    (omega : ℝ) {T H t : ℝ} (hT : 0 < T) (hH : 0 ≤ H) :
    0 ≤ thetaFrequencyShortIntegralEnvelope omega T H t := by
  unfold thetaFrequencyShortIntegralEnvelope
  split_ifs
  · exact hH
  · exact add_nonneg
      (le_min hH (div_nonneg (by norm_num) (abs_nonneg _)))
      (by positivity)

/-- The coefficient-weighted short-window envelope is controlled by the
collected coefficient square energy and the stationary packing budget.  The
linearization error remains as an explicit coefficient-`L1` term. -/
theorem sq_sum_norm_mul_thetaFrequencyShortIntegralEnvelope_le
    {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    {T H t : ℝ} (hT : 0 < T) (hH : 0 ≤ H) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        ‖selbergSqrtZetaSignedRationalCoeff N X q‖ *
          thetaFrequencyShortIntegralEnvelope
            (selbergSqrtZetaSignedRationalFrequency q) T H t) ^ 2 ≤
      2 *
          (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X q)) *
          (H ^ 2 + 12 * H * ((N * X ^ 2 : ℕ) : ℝ)) +
        2 *
          ((H ^ 3 / (2 * T)) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              ‖selbergSqrtZetaSignedRationalCoeff N X q‖) ^ 2 := by
  classical
  let Q : Finset ℚ := selbergSqrtZetaSignedRationalSupport N X
  let a : ℚ → ℝ := fun q =>
    ‖selbergSqrtZetaSignedRationalCoeff N X q‖
  let e : ℚ → ℝ := fun q =>
    MathlibAux.stationaryMinReciprocalEnvelope
      H (-deriv thetaModel t)
      (selbergSqrtZetaSignedRationalFrequency q)
  let r : ℝ := H ^ 3 / (2 * T)
  let lhs : ℝ := ∑ q ∈ Q,
    a q * thetaFrequencyShortIntegralEnvelope
      (selbergSqrtZetaSignedRationalFrequency q) T H t
  let main : ℝ := ∑ q ∈ Q, a q * e q
  let tail : ℝ := r * ∑ q ∈ Q, a q
  let energy : ℝ := ∑ q ∈ Q,
    Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)
  let packing : ℝ := H ^ 2 + 12 * H * ((N * X ^ 2 : ℕ) : ℝ)
  have hr : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hlhs : 0 ≤ lhs := by
    dsimp only [lhs]
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (norm_nonneg _)
      (thetaFrequencyShortIntegralEnvelope_nonneg
        (selbergSqrtZetaSignedRationalFrequency q) hT hH)
  have hmain : 0 ≤ main := by
    dsimp only [main]
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (norm_nonneg _)
      (stationaryMinReciprocalEnvelope_nonneg hH)
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    exact mul_nonneg hr (Finset.sum_nonneg fun q hq => norm_nonneg _)
  have hlhs_le : lhs ≤ main + tail := by
    dsimp only [lhs, main, tail]
    calc
      (∑ q ∈ Q,
          a q * thetaFrequencyShortIntegralEnvelope
            (selbergSqrtZetaSignedRationalFrequency q) T H t) ≤
          ∑ q ∈ Q, a q * (e q + r) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left
          (thetaFrequencyShortIntegralEnvelope_le_stationary_add_error
            (selbergSqrtZetaSignedRationalFrequency q) hT hH)
          (norm_nonneg _)
      _ = (∑ q ∈ Q, a q * e q) + r * ∑ q ∈ Q, a q := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        ring
  have hmainSq :
      main ^ 2 ≤ energy * packing := by
    have hcs :=
      Finset.sum_mul_sq_le_sq_mul_sq Q a e
    have hpack :=
      sum_sq_stationaryMinReciprocalEnvelope_rationalSupport_le
        hN hX (t := t) hH
    have henergy : 0 ≤ energy := by
      dsimp only [energy]
      exact Finset.sum_nonneg fun q hq => Complex.normSq_nonneg _
    calc
      main ^ 2 ≤
          (∑ q ∈ Q, (a q) ^ 2) * ∑ q ∈ Q, (e q) ^ 2 := by
        simpa only [main] using hcs
      _ = energy * ∑ q ∈ Q, (e q) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        simp only [a, Complex.normSq_eq_norm_sq]
      _ ≤ energy * packing := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [Q, e, packing] using hpack
        · exact henergy
  have hlhsSq : lhs ^ 2 ≤ (main + tail) ^ 2 :=
    (sq_le_sq₀ hlhs (add_nonneg hmain htail)).2 hlhs_le
  have hsplit :
      (main + tail) ^ 2 ≤ 2 * main ^ 2 + 2 * tail ^ 2 := by
    nlinarith [sq_nonneg (main - tail)]
  have hfinal :
      lhs ^ 2 ≤ 2 * energy * packing + 2 * tail ^ 2 := by
    calc
      lhs ^ 2 ≤ (main + tail) ^ 2 := hlhsSq
      _ ≤ 2 * main ^ 2 + 2 * tail ^ 2 := hsplit
      _ ≤ 2 * (energy * packing) + 2 * tail ^ 2 := by
        gcongr
      _ = 2 * energy * packing + 2 * tail ^ 2 := by ring
  simpa only [lhs, energy, packing, tail, r, Q, a] using hfinal

/-- The squared norm of the actual finite complex Selberg-model short
integral is controlled by the rational coefficient energy and the explicit
linearization-error `L1` term. -/
theorem
    norm_sq_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalEnergy
    (kappa : ℝ) {X : ℕ} (hX : 0 < X)
    {T H t : ℝ} (hT : 1 ≤ T) (hTt : T ≤ t) (hH : 0 ≤ H) :
    ‖∫ v in 0..H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v)‖ ^ 2 ≤
      2 *
          (∑ q ∈ selbergSqrtZetaSignedRationalSupport
              (firstZetaApproximationCutoff T) X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff
                (firstZetaApproximationCutoff T) X q)) *
          (H ^ 2 + 12 * H *
            (((firstZetaApproximationCutoff T) * X ^ 2 : ℕ) : ℝ)) +
        2 *
          ((H ^ 3 / (2 * T)) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              ‖selbergSqrtZetaSignedRationalCoeff
                (firstZetaApproximationCutoff T) X q‖) ^ 2 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hcutoff : 0 < firstZetaApproximationCutoff T := by
    exact Nat.floor_pos.mpr (by
      linarith)
  have henv :
      0 ≤ selbergSqrtZetaSignedRationalWindowEnvelopeSum T X H t := by
    unfold selbergSqrtZetaSignedRationalWindowEnvelopeSum
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (norm_nonneg _)
      (thetaFrequencyShortIntegralEnvelope_nonneg
        (selbergSqrtZetaSignedRationalFrequency q) hTpos hH)
  have hintegral :=
    norm_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalWindowEnvelopeSum
      kappa X hTpos hTt hH
  have hsquare :
      ‖∫ v in 0..H,
          selbergSqrtZetaSignedComplexModel kappa T X (t + v)‖ ^ 2 ≤
        (selbergSqrtZetaSignedRationalWindowEnvelopeSum T X H t) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) henv).2 hintegral
  exact hsquare.trans
    (sq_sum_norm_mul_thetaFrequencyShortIntegralEnvelope_le
      hcutoff hX hTpos hH)

end HardyTheorem
