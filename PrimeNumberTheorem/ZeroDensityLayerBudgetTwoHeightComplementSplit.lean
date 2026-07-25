import PrimeNumberTheorem.ZeroDensityLayerBudgetBidirectionalHeightStrategy

/-!
# Target-amplitude aggregation for a two-height explicit formula

A split-height argument naturally separates the complementary zero contribution
into zeros already visible below the upper height and an annulus of new zeros
between the upper and lower heights.  This file proves the elementary but
essential normalized aggregation step: separately negligible layers combine to
a negligible total complement.

The finite-sum theorem also supports a dynamic real-part strip partition.  It
does not prove that any concrete zeta-zero layer is negligible; those analytic
estimates remain explicit inputs.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

/-- The zero remainder is negligible relative to every amplitude. -/
theorem targetAmplitudeNegligible_zero (amplitude : ℝ → ℝ) :
    TargetAmplitudeNegligible amplitude (fun _ => 0) := by
  unfold TargetAmplitudeNegligible
  simp

/-- Target-amplitude negligibility is closed under addition when the amplitude
is eventually positive. -/
theorem TargetAmplitudeNegligible.add
    {amplitude left right : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (hleft : TargetAmplitudeNegligible amplitude left)
    (hright : TargetAmplitudeNegligible amplitude right) :
    TargetAmplitudeNegligible amplitude (fun x => left x + right x) := by
  unfold TargetAmplitudeNegligible at hleft hright ⊢
  have hupper :
      Filter.Tendsto
        (fun x => |left x| / amplitude x + |right x| / amplitude x)
        Filter.atTop (nhds 0) := by
    simpa using hleft.add hright
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hamplitude] with x hx
    exact div_nonneg (abs_nonneg _) (le_of_lt hx)
  · filter_upwards [hamplitude] with x hx
    have habs : |left x + right x| ≤ |left x| + |right x| :=
      abs_add_le (left x) (right x)
    calc
      |left x + right x| / amplitude x
          ≤ (|left x| + |right x|) / amplitude x :=
        div_le_div_of_nonneg_right habs (le_of_lt hx)
      _ = |left x| / amplitude x + |right x| / amplitude x := by
        ring

/-- A finite collection of separately negligible dynamic layers has negligible
total contribution.  This is the aggregation rule used by finite real-part
strip decompositions. -/
theorem targetAmplitudeNegligible_finset_sum
    {ι : Type*} {amplitude : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (layers : Finset ι) (term : ι → ℝ → ℝ)
    (hterm :
      ∀ i ∈ layers, TargetAmplitudeNegligible amplitude (term i)) :
    TargetAmplitudeNegligible amplitude
      (fun x => layers.sum (fun i => term i x)) := by
  classical
  induction layers using Finset.induction_on with
  | empty =>
      simpa using targetAmplitudeNegligible_zero amplitude
  | @insert i layers hi ih =>
      have hiNegligible :
          TargetAmplitudeNegligible amplitude (term i) :=
        hterm i (Finset.mem_insert_self i layers)
      have hlayersNegligible :
          TargetAmplitudeNegligible amplitude
            (fun x => layers.sum (fun j => term j x)) := by
        apply ih
        intro j hj
        exact hterm j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert hi] using
        hiNegligible.add hamplitude hlayersNegligible

/-- The complementary zero term associated with two truncation heights:
an inner complement below the upper height plus the intervening height annulus. -/
def twoHeightComplement
    (innerComplement heightAnnulus : ℝ → ℝ) (x : ℝ) : ℝ :=
  innerComplement x + heightAnnulus x

/-- Separate normalized certificates for the two pieces of a split-height
complementary zero sum. -/
structure TwoHeightTargetComplementControl
    (amplitude innerComplement heightAnnulus : ℝ → ℝ) : Prop where
  amplitude_eventually_pos :
    ∀ᶠ x in Filter.atTop, 0 < amplitude x
  inner_negligible :
    TargetAmplitudeNegligible amplitude innerComplement
  annulus_negligible :
    TargetAmplitudeNegligible amplitude heightAnnulus

/-- The two separately audited pieces automatically provide the combined
complementary hypothesis expected by the target-amplitude transfer machine. -/
theorem TwoHeightTargetComplementControl.combined_negligible
    {amplitude innerComplement heightAnnulus : ℝ → ℝ}
    (control :
      TwoHeightTargetComplementControl amplitude innerComplement heightAnnulus) :
    TargetAmplitudeNegligible amplitude
      (twoHeightComplement innerComplement heightAnnulus) := by
  exact control.inner_negligible.add control.amplitude_eventually_pos
    control.annulus_negligible

end PrimeNumberTheorem
