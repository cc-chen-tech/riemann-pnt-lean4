import WeilExtremalKernels.FiniteQuadraticForm

/-!
# Sufficient finite-to-infinite positivity bridges

This module isolates two abstract implications needed by a future analytic
Weil-form argument:

* a certified normalized finite margin dominates a global truncation error;
* certified low- and high-frequency margins dominate their Schur coupling.

The hypotheses supplying the infinite-dimensional tail, high block, and
coupling estimates are not proved here. In particular, this file makes no
claim that a finite Weil certificate implies the infinite-dimensional Weil
criterion or RH.
-/

namespace WeilExtremalKernels

/-- A finite normalized lower bound transfers to the target form when it
dominates the target-to-truncation error. -/
theorem nonneg_of_normalized_truncation_bound {X : Type*}
    (q qN sizeSq : X → ℝ) (epsilon delta : ℝ)
    (hsize : ∀ x, 0 ≤ sizeSq x)
    (hfinite : ∀ x, epsilon * sizeSq x ≤ qN x)
    (herror : ∀ x, |q x - qN x| ≤ delta * sizeSq x)
    (hbudget : delta ≤ epsilon) :
    ∀ x, 0 ≤ q x := by
  intro x
  have hdiff : -(delta * sizeSq x) ≤ q x - qN x := by
    have habs := neg_abs_le (q x - qN x)
    linarith [herror x]
  have hscaled :
      delta * sizeSq x ≤ epsilon * sizeSq x :=
    mul_le_mul_of_nonneg_right hbudget (hsize x)
  linarith [hfinite x]

/-- Strict normalized budget slack gives a positive target value whenever
the chosen size is positive. -/
theorem pos_of_normalized_truncation_bound {X : Type*}
    (q qN sizeSq : X → ℝ) (epsilon delta : ℝ)
    (hfinite : ∀ x, epsilon * sizeSq x ≤ qN x)
    (herror : ∀ x, |q x - qN x| ≤ delta * sizeSq x)
    (hbudget : delta < epsilon) :
    ∀ x, 0 < sizeSq x → 0 < q x := by
  intro x hx
  have hdiff : -(delta * sizeSq x) ≤ q x - qN x := by
    have habs := neg_abs_le (q x - qN x)
    linarith [herror x]
  have hscaled :
      delta * sizeSq x < epsilon * sizeSq x :=
    mul_lt_mul_of_pos_right hbudget hx
  linarith [hfinite x]

/-- Scalar Schur/Young inequality derived from `beta^2 ≤ epsilon * gamma`. -/
theorem two_mul_coupling_le_of_sq_le
    (lowSize highSize epsilon beta gamma : ℝ)
    (hlowSize : 0 ≤ lowSize) (hhighSize : 0 ≤ highSize)
    (hepsilon : 0 < epsilon) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hschur : beta ^ 2 ≤ epsilon * gamma) :
    2 * beta * lowSize * highSize ≤
      epsilon * lowSize ^ 2 + gamma * highSize ^ 2 := by
  have hscaled :
      beta ^ 2 * highSize ^ 2 ≤
        (epsilon * gamma) * highSize ^ 2 :=
    mul_le_mul_of_nonneg_right hschur (sq_nonneg highSize)
  have hsquare := sq_nonneg (epsilon * lowSize - beta * highSize)
  nlinarith

/-- Strict scalar Schur inequality when the determinant condition has slack
and at least one size is positive. -/
theorem two_mul_coupling_lt_of_sq_lt
    (lowSize highSize epsilon beta gamma : ℝ)
    (hlowSize : 0 ≤ lowSize) (hhighSize : 0 ≤ highSize)
    (hepsilon : 0 < epsilon) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hschur : beta ^ 2 < epsilon * gamma)
    (hsizes : 0 < lowSize ∨ 0 < highSize) :
    2 * beta * lowSize * highSize <
      epsilon * lowSize ^ 2 + gamma * highSize ^ 2 := by
  by_cases hhighZero : highSize = 0
  · subst highSize
    rcases hsizes with hlow | hhigh
    · have hpositive : 0 < epsilon * lowSize ^ 2 :=
        mul_pos hepsilon (sq_pos_of_pos hlow)
      simpa using hpositive
    · simp at hhigh
  · have hhighPos : 0 < highSize :=
      lt_of_le_of_ne hhighSize (Ne.symm hhighZero)
    have hscaled :
        beta ^ 2 * highSize ^ 2 <
          (epsilon * gamma) * highSize ^ 2 :=
      mul_lt_mul_of_pos_right hschur (sq_pos_of_pos hhighPos)
    have hsquare := sq_nonneg (epsilon * lowSize - beta * highSize)
    nlinarith

/-- A pointwise Schur complement criterion for a low/high decomposition.

Analytic callers must supply all three block estimates in the same
normalization. -/
theorem schur_nonneg_of_bounds {Low High : Type*}
    (qLow : Low → ℝ) (qCross : Low → High → ℝ) (qHigh : High → ℝ)
    (lowSize : Low → ℝ) (highSize : High → ℝ)
    (epsilon beta gamma : ℝ)
    (hlowSize : ∀ u, 0 ≤ lowSize u)
    (hhighSize : ∀ v, 0 ≤ highSize v)
    (hepsilon : 0 < epsilon) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hlow : ∀ u, epsilon * (lowSize u) ^ 2 ≤ qLow u)
    (hhigh : ∀ v, gamma * (highSize v) ^ 2 ≤ qHigh v)
    (hcross : ∀ u v,
      |qCross u v| ≤ beta * lowSize u * highSize v)
    (hschur : beta ^ 2 ≤ epsilon * gamma) :
    ∀ u v, 0 ≤ qLow u + 2 * qCross u v + qHigh v := by
  intro u v
  have hcrossLower :
      -(beta * lowSize u * highSize v) ≤ qCross u v := by
    have habs := neg_abs_le (qCross u v)
    linarith [hcross u v]
  have hcoupling := two_mul_coupling_le_of_sq_le
    (lowSize u) (highSize v) epsilon beta gamma
    (hlowSize u) (hhighSize v) hepsilon hbeta hgamma hschur
  linarith [hlow u, hhigh v]

/-- Strict Schur determinant slack gives positivity away from simultaneous
zero size. -/
theorem schur_pos_of_bounds {Low High : Type*}
    (qLow : Low → ℝ) (qCross : Low → High → ℝ) (qHigh : High → ℝ)
    (lowSize : Low → ℝ) (highSize : High → ℝ)
    (epsilon beta gamma : ℝ)
    (hlowSize : ∀ u, 0 ≤ lowSize u)
    (hhighSize : ∀ v, 0 ≤ highSize v)
    (hepsilon : 0 < epsilon) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hlow : ∀ u, epsilon * (lowSize u) ^ 2 ≤ qLow u)
    (hhigh : ∀ v, gamma * (highSize v) ^ 2 ≤ qHigh v)
    (hcross : ∀ u v,
      |qCross u v| ≤ beta * lowSize u * highSize v)
    (hschur : beta ^ 2 < epsilon * gamma) :
    ∀ u v, 0 < lowSize u ∨ 0 < highSize v →
      0 < qLow u + 2 * qCross u v + qHigh v := by
  intro u v hsizes
  have hcrossLower :
      -(beta * lowSize u * highSize v) ≤ qCross u v := by
    have habs := neg_abs_le (qCross u v)
    linarith [hcross u v]
  have hcoupling := two_mul_coupling_lt_of_sq_lt
    (lowSize u) (highSize v) epsilon beta gamma
    (hlowSize u) (hhighSize v) hepsilon hbeta hgamma hschur hsizes
  linarith [hlow u, hhigh v]

end WeilExtremalKernels
