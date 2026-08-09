import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightExponentFeasibility

/-!
# A shared actual selected-height exponent for finitely many strips

A finite Carlson decomposition uses one truncation height for every real-part
strip.  Pointwise feasibility of each strip is therefore not enough: one
exponent must satisfy all endpoint-aware density inequalities simultaneously.

This module proves the exact finite-family criterion.  Under `0 < beta < 1`,
the conjunction of the individual endpoint thresholds is equivalent to the
existence of one `0 < alpha ≤ 1` above the contour transition `1 - beta` for
which every strip exponent is negative.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- Finitely many strict upper bounds above one real lower bound admit a
common strict intermediate point. -/
private theorem exists_real_between_all_fin
    (lower : ℝ) {n : ℕ} (upper : Fin n → ℝ)
    (hupper : ∀ i, lower < upper i) :
    ∃ value : ℝ, lower < value ∧ ∀ i, value < upper i := by
  induction n with
  | zero =>
      refine ⟨lower + 1, by linarith, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨value, hlower, hvalue⟩ :=
        ih (fun i : Fin n => upper i.castSucc)
          (fun i => hupper i.castSucc)
      have hlowerMin :
          lower < min value (upper (Fin.last n)) :=
        lt_min hlower (hupper (Fin.last n))
      obtain ⟨shared, hsharedLower, hsharedMin⟩ :=
        exists_between hlowerMin
      have hsharedValue : shared < value :=
        (lt_min_iff.mp hsharedMin).1
      have hsharedLast : shared < upper (Fin.last n) :=
        (lt_min_iff.mp hsharedMin).2
      refine ⟨shared, hsharedLower, fun i => ?_⟩
      exact
        Fin.lastCases hsharedLast
          (fun j => hsharedValue.trans (hvalue j)) i

/-- Exact criterion for one actual selected-height exponent shared by a finite
family of endpoint-aware Carlson strips. -/
theorem exists_actualSelectedHeightExponent_finiteStrips_decay_iff
    {beta : ℝ} {n : ℕ} (sigma tau : Fin n → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    (∃ alpha : ℝ,
        0 < alpha ∧ alpha ≤ 1 ∧ 1 - beta < alpha ∧
        ∀ i,
          targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) <
              0) ↔
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta := by
  constructor
  · rintro ⟨alpha, _halpha, _halphaOne, hmargin, hdecay⟩ i
    exact
      (exists_carlsonPolynomialHeight_stripEndpoint_decay_iff
        (hsigma i) (hsigmaOne i)).1
        ⟨alpha, hmargin, hdecay i⟩
  · intro hthreshold
    have hexists :
        ∀ i, ∃ alpha : ℝ,
          1 - beta < alpha ∧
          targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) <
              0 := by
      intro i
      exact
        (exists_carlsonPolynomialHeight_stripEndpoint_decay_iff
          (hsigma i) (hsigmaOne i)).2 (hthreshold i)
    let upper : Fin n → ℝ :=
      fun i => Classical.choose (hexists i)
    have hupperSpec :
        ∀ i,
          1 - beta < upper i ∧
          targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent
              (upper i) (sigma i)) < 0 := by
      intro i
      exact Classical.choose_spec (hexists i)
    obtain ⟨candidate, hcandidateLower, hcandidateUpper⟩ :=
      exists_real_between_all_fin (1 - beta) upper
        (fun i => (hupperSpec i).1)
    have hlowerOne : 1 - beta < 1 := by linarith
    have hlowerMin : 1 - beta < min candidate 1 :=
      lt_min hcandidateLower hlowerOne
    obtain ⟨alpha, hmargin, halphaMin⟩ :=
      exists_between hlowerMin
    have halphaCandidate : alpha < candidate :=
      (lt_min_iff.mp halphaMin).1
    have halphaOneLt : alpha < 1 :=
      (lt_min_iff.mp halphaMin).2
    have halpha : 0 < alpha := by
      have : 0 < 1 - beta := by linarith
      exact this.trans hmargin
    refine ⟨alpha, halpha, halphaOneLt.le, hmargin, fun i => ?_⟩
    have halphaUpper : alpha ≤ upper i :=
      (halphaCandidate.trans (hcandidateUpper i)).le
    have hslope :
        0 ≤ 4 * sigma i * (1 - sigma i) :=
      (carlsonClassicalDensitySlope_pos
        (hsigma i) (hsigmaOne i)).le
    have hmono :
        alpha * (4 * sigma i * (1 - sigma i)) ≤
          upper i * (4 * sigma i * (1 - sigma i)) :=
      mul_le_mul_of_nonneg_right halphaUpper hslope
    have hdecay := (hupperSpec i).2
    simp only [targetAmplitudeStripEndpointExponent,
      carlsonClassicalPolynomialDensityExponent,
      carlsonPolynomialHeightDensityExponent] at hdecay ⊢
    nlinarith

/-- Canonically selected exponent shared by all strips under the exact
pointwise endpoint-threshold hypotheses. -/
noncomputable def actualSelectedHeightFiniteStripExponent
    (beta : ℝ) {n : ℕ} (sigma tau : Fin n → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) : ℝ :=
  Classical.choose
    ((exists_actualSelectedHeightExponent_finiteStrips_decay_iff
      sigma tau hbeta hbetaOne hsigma hsigmaOne).2 hthreshold)

/-- Full actual-remainder and Carlson-decay specification of the canonical
shared finite-strip exponent. -/
theorem actualSelectedHeightFiniteStripExponent_spec
    (beta : ℝ) {n : ℕ} (sigma tau : Fin n → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) :
    0 <
        actualSelectedHeightFiniteStripExponent beta sigma tau
          hbeta hbetaOne hsigma hsigmaOne hthreshold ∧
      actualSelectedHeightFiniteStripExponent beta sigma tau
          hbeta hbetaOne hsigma hsigmaOne hthreshold ≤ 1 ∧
      1 - beta <
        actualSelectedHeightFiniteStripExponent beta sigma tau
          hbeta hbetaOne hsigma hsigmaOne hthreshold ∧
      ∀ i,
        targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent
            (actualSelectedHeightFiniteStripExponent beta sigma tau
              hbeta hbetaOne hsigma hsigmaOne hthreshold)
            (sigma i)) < 0 :=
  Classical.choose_spec
    ((exists_actualSelectedHeightExponent_finiteStrips_decay_iff
      sigma tau hbeta hbetaOne hsigma hsigmaOne).2 hthreshold)

end PrimeNumberTheorem
