import HardyTheorem.SelbergJFubiniAssembled

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Exact diagonal / two-sided off-diagonal partition of Selberg's `J` -/

noncomputable def selbergJIntegratedExpandedPair
    (delta x theta : ℝ) (X : ℕ)
    (q : SelbergJOuterIndex X × (ℕ × ℕ)) : ℂ :=
  ∫ u in Ioi x, selbergJGlobalExpandedPairIntegrand delta theta X q u

def selbergJLeftFrequencyNumerator
    {X : ℕ} (q : SelbergJOuterIndex X × (ℕ × ℕ)) : ℕ :=
  (q.2.1 + 1) * q.1.val.1.1 * q.1.val.2.2

def selbergJRightFrequencyNumerator
    {X : ℕ} (q : SelbergJOuterIndex X × (ℕ × ℕ)) : ℕ :=
  (q.2.2 + 1) * q.1.val.1.2 * q.1.val.2.1

def selbergJDiagonalIndexSet (X : ℕ) :
    Set (SelbergJOuterIndex X × (ℕ × ℕ)) :=
  {q | selbergJLeftFrequencyNumerator q = selbergJRightFrequencyNumerator q}

def selbergJForwardIndexSet (X : ℕ) :
    Set (SelbergJOuterIndex X × (ℕ × ℕ)) :=
  {q | selbergJRightFrequencyNumerator q < selbergJLeftFrequencyNumerator q}

def selbergJReverseIndexSet (X : ℕ) :
    Set (SelbergJOuterIndex X × (ℕ × ℕ)) :=
  {q | selbergJLeftFrequencyNumerator q < selbergJRightFrequencyNumerator q}

noncomputable def selbergJDiagonalPart
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑' q, (selbergJDiagonalIndexSet X).indicator
    (selbergJIntegratedExpandedPair delta x theta X) q

noncomputable def selbergJForwardPart
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑' q, (selbergJForwardIndexSet X).indicator
    (selbergJIntegratedExpandedPair delta x theta X) q

noncomputable def selbergJReversePart
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑' q, (selbergJReverseIndexSet X).indicator
    (selbergJIntegratedExpandedPair delta x theta X) q

theorem summable_selbergJIntegratedExpandedPair
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X : ℕ} (hX : 2 ≤ X) :
    Summable (selbergJIntegratedExpandedPair delta x theta X) := by
  have hnorm := summable_integral_norm_selbergJGlobalExpandedPairIntegrand
    hdelta hdelta1 htheta hx hX
  apply Summable.of_norm_bounded hnorm
  intro q
  exact norm_integral_le_integral_norm _

theorem selbergJGlobalIntegratedSeries_eq_three_parts
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X : ℕ} (hX : 2 ≤ X) :
    (∑' q, selbergJIntegratedExpandedPair delta x theta X q) =
      selbergJDiagonalPart delta x theta X +
        selbergJForwardPart delta x theta X +
          selbergJReversePart delta x theta X := by
  let f := selbergJIntegratedExpandedPair delta x theta X
  let D := selbergJDiagonalIndexSet X
  let P := selbergJForwardIndexSet X
  let R := selbergJReverseIndexSet X
  have hf : Summable f := summable_selbergJIntegratedExpandedPair
    hdelta hdelta1 htheta hx hX
  have hD : Summable (D.indicator f) := hf.indicator D
  have hP : Summable (P.indicator f) := hf.indicator P
  have hR : Summable (R.indicator f) := hf.indicator R
  calc
    (∑' q, f q) = ∑' q, ((D.indicator f q + P.indicator f q) +
        R.indicator f q) := by
      apply tsum_congr
      intro q
      rcases lt_trichotomy (selbergJLeftFrequencyNumerator q)
          (selbergJRightFrequencyNumerator q) with hlt | heq | hgt
      · simp [D, P, R, selbergJDiagonalIndexSet,
          selbergJForwardIndexSet, selbergJReverseIndexSet,
          hlt, hlt.ne, not_lt_of_ge hlt.le]
      · simp [D, P, R, selbergJDiagonalIndexSet,
          selbergJForwardIndexSet, selbergJReverseIndexSet, heq]
      · simp [D, P, R, selbergJDiagonalIndexSet,
          selbergJForwardIndexSet, selbergJReverseIndexSet,
          hgt, hgt.ne', not_lt_of_ge hgt.le]
    _ = (∑' q, (D.indicator f q + P.indicator f q)) +
        ∑' q, R.indicator f q := (hD.add hP).tsum_add hR
    _ = ((∑' q, D.indicator f q) + ∑' q, P.indicator f q) +
        ∑' q, R.indicator f q := by rw [hD.tsum_add hP]
    _ = _ := rfl

theorem selbergJ_eq_diagonal_add_forward_add_reverse
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X : ℕ} (hX : 2 ≤ X) :
    (selbergJ delta x theta X : ℂ) =
      selbergJDiagonalPart delta x theta X +
        selbergJForwardPart delta x theta X +
          selbergJReversePart delta x theta X := by
  rw [selbergJ_eq_tsum_integral_globalExpandedPair
    hdelta hdelta1 htheta hx hX]
  change (∑' q, selbergJIntegratedExpandedPair delta x theta X q) = _
  exact selbergJGlobalIntegratedSeries_eq_three_parts
    hdelta hdelta1 htheta hx hX

end HardyTheorem
