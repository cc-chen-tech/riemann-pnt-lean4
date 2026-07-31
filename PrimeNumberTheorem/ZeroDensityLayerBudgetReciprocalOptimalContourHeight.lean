import PrimeNumberTheorem.ZeroDensityLayerBudgetReciprocalSigmaOnlyRunningBoundary

/-!
# Optimal contour-limited height for the reciprocal transfer

Once reciprocal summation removes the low-layer polynomial cost, the only
strict lower constraint on the selected-height exponents is the contour
threshold `1 - beta`.  This module proves that threshold is the exact
infimum, and realizes every positive distance from it with the actual uniform
good-height selector and contour remainder certificate.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- Feasibility conditions needed by a reciprocal selected-height window. -/
def IsReciprocalContourHeightWindow
    (beta inner outer : ℝ) : Prop :=
  0 < inner ∧ inner ≤ 1 ∧ 1 - beta < inner ∧ inner < outer

/-- Near-optimal inner exponent at distance `delta / 2` from the contour
floor. -/
noncomputable def reciprocalContourNearOptimalInnerExponent
    (beta delta : ℝ) : ℝ :=
  1 - beta + delta / 2

/-- Near-optimal outer exponent at exact distance `delta` from the contour
floor. -/
noncomputable def reciprocalContourNearOptimalOuterExponent
    (beta delta : ℝ) : ℝ :=
  1 - beta + delta

/-- Every feasible outer exponent lies strictly above the contour floor. -/
theorem reciprocalContourHeightFloor_lt_outer
    {beta inner outer : ℝ}
    (hwindow : IsReciprocalContourHeightWindow beta inner outer) :
    1 - beta < outer :=
  hwindow.2.2.1.trans hwindow.2.2.2

/-- The explicit near-optimal exponents form a feasible window and the outer
exponent is exactly `delta` above the contour floor. -/
theorem reciprocalContourNearOptimalWindow_spec
    {beta delta : ℝ}
    (hbetaOne : beta < 1)
    (hdelta : 0 < delta) (hdeltaBeta : delta < beta) :
    IsReciprocalContourHeightWindow beta
        (reciprocalContourNearOptimalInnerExponent beta delta)
        (reciprocalContourNearOptimalOuterExponent beta delta) ∧
      reciprocalContourNearOptimalOuterExponent beta delta =
        1 - beta + delta ∧
      reciprocalContourNearOptimalOuterExponent beta delta < 1 := by
  have hinner :
      0 < reciprocalContourNearOptimalInnerExponent beta delta := by
    unfold reciprocalContourNearOptimalInnerExponent
    linarith
  have hinnerOne :
      reciprocalContourNearOptimalInnerExponent beta delta ≤ 1 := by
    unfold reciprocalContourNearOptimalInnerExponent
    linarith
  have hcontour :
      1 - beta < reciprocalContourNearOptimalInnerExponent beta delta := by
    unfold reciprocalContourNearOptimalInnerExponent
    linarith
  have hstrict :
      reciprocalContourNearOptimalInnerExponent beta delta <
        reciprocalContourNearOptimalOuterExponent beta delta := by
    unfold reciprocalContourNearOptimalInnerExponent
      reciprocalContourNearOptimalOuterExponent
    linarith
  refine ⟨⟨hinner, hinnerOne, hcontour, hstrict⟩, rfl, ?_⟩
  unfold reciprocalContourNearOptimalOuterExponent
  linarith

/-- The contour floor is the exact infimum in elementary form: it is a strict
lower bound for every feasible outer exponent, and feasible windows exist
inside every positive neighborhood above it. -/
theorem reciprocalContourHeightFloor_optimal
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1) :
    (∀ inner outer : ℝ,
        IsReciprocalContourHeightWindow beta inner outer →
          1 - beta < outer) ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ inner outer : ℝ,
          IsReciprocalContourHeightWindow beta inner outer ∧
            outer < 1 - beta + epsilon := by
  constructor
  · intro inner outer hwindow
    exact reciprocalContourHeightFloor_lt_outer hwindow
  · intro epsilon hepsilon
    let delta : ℝ := min (epsilon / 2) (beta / 2)
    have hdelta : 0 < delta := by
      dsimp [delta]
      exact lt_min (by linarith) (by linarith)
    have hdeltaBeta : delta < beta := by
      have hle : delta ≤ beta / 2 := by
        exact min_le_right _ _
      linarith
    have hdeltaEpsilon : delta < epsilon := by
      have hle : delta ≤ epsilon / 2 := by
        exact min_le_left _ _
      linarith
    refine ⟨reciprocalContourNearOptimalInnerExponent beta delta,
      reciprocalContourNearOptimalOuterExponent beta delta, ?_, ?_⟩
    · exact (reciprocalContourNearOptimalWindow_spec
        hbetaOne hdelta hdeltaBeta).1
    · unfold reciprocalContourNearOptimalOuterExponent
      linarith

/-- Every explicit near-optimal window is realized by a cofinal selected
height with the actual natural-point contour remainder certificate. -/
theorem reciprocalContourNearOptimalSelectedHeight_spec
    {beta delta : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hdelta : 0 < delta) (hdeltaBeta : delta < beta)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ m : ℕ in atTop,
        selectedUniformGoodHeight
              (reciprocalContourNearOptimalInnerExponent beta delta)
              selection (m : ℝ) ≤
          carlsonPolynomialHeight
            (reciprocalContourNearOptimalOuterExponent beta delta) (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          selectedUniformGoodHeight
            (reciprocalContourNearOptimalInnerExponent beta delta)
            selection (m : ℝ))
        atTop atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate beta
        (selectedUniformGoodHeight
          (reciprocalContourNearOptimalInnerExponent beta delta) selection) ∧
      reciprocalContourNearOptimalOuterExponent beta delta < 1 := by
  rcases reciprocalContourNearOptimalWindow_spec
      hbetaOne hdelta hdeltaBeta with
    ⟨hwindow, _, houterOne⟩
  refine ⟨?_, ?_, ?_, houterOne⟩
  · exact tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_le_polynomialHeight
        hwindow.1 hwindow.2.2.2 selection)
  · exact
      (selectedUniformGoodHeight_tendsto_atTop hwindow.1 selection).comp
        tendsto_natCast_atTop_atTop
  · exact selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta hwindow.1 hwindow.2.1 hwindow.2.2.1 selection

/-- Actual selected-height windows approach the contour floor within every
prescribed positive tolerance. -/
theorem exists_reciprocalContourSelectedHeight_within
    {beta epsilon : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hepsilon : 0 < epsilon)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∃ delta : ℝ,
      0 < delta ∧ delta < beta ∧
      reciprocalContourNearOptimalOuterExponent beta delta <
        1 - beta + epsilon ∧
      (∀ᶠ m : ℕ in atTop,
        selectedUniformGoodHeight
              (reciprocalContourNearOptimalInnerExponent beta delta)
              selection (m : ℝ) ≤
          carlsonPolynomialHeight
            (reciprocalContourNearOptimalOuterExponent beta delta) (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          selectedUniformGoodHeight
            (reciprocalContourNearOptimalInnerExponent beta delta)
            selection (m : ℝ))
        atTop atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate beta
        (selectedUniformGoodHeight
          (reciprocalContourNearOptimalInnerExponent beta delta) selection) := by
  let delta : ℝ := min (epsilon / 2) (beta / 2)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith) (by linarith)
  have hdeltaBeta : delta < beta := by
    have hle : delta ≤ beta / 2 := min_le_right _ _
    linarith
  have hdeltaEpsilon : delta < epsilon := by
    have hle : delta ≤ epsilon / 2 := min_le_left _ _
    linarith
  rcases reciprocalContourNearOptimalSelectedHeight_spec
      hbeta hbetaOne hdelta hdeltaBeta selection with
    ⟨hheight, htop, remainder, _⟩
  refine ⟨delta, hdelta, hdeltaBeta, ?_, hheight, htop, remainder⟩
  unfold reciprocalContourNearOptimalOuterExponent
  linarith

end

end PrimeNumberTheorem
