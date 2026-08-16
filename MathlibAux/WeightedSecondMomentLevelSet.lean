import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set

namespace MathlibAux

/-!
# Quantitative level-set bounds from a weighted second moment

The main lemma turns a weighted second-moment surplus above a fixed threshold
into a lower bound for the measure of the corresponding strict level set.  It
uses only a pointwise envelope, so applications do not need a fourth-moment
estimate.
-/

/-- A weighted second moment above the threshold contribution must be carried
by the strict level set.  The conclusion is kept in product form, avoiding any
division by a possibly zero envelope. -/
theorem weightedSecondMoment_sub_thresholdMass_le_envelope_mul_measure
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    {s : Set alpha} {f w : alpha -> Real} {C B : Real}
    (hs : MeasurableSet s) (hmus : mu s ≠ ⊤)
    (hf : Measurable f)
    (hwNonneg : ∀ x, 0 ≤ w x)
    (hweighted : IntegrableOn (fun x => f x ^ 2 * w x) s mu)
    (hweight : IntegrableOn w s mu)
    (hC : 0 ≤ C)
    (hbound : ∀ x ∈ s, f x ^ 2 * w x ≤ B) :
    (∫ x in s, f x ^ 2 * w x ∂mu) -
          C ^ 2 * ∫ x in s, w x ∂mu ≤
        B * mu.real {x ∈ s | C < |f x|} := by
  let good : Set alpha := {x ∈ s | C < |f x|}
  have hgood : MeasurableSet good :=
    hs.inter (hf.norm measurableSet_Ioi)
  have hgoodSubset : good ⊆ s := fun _ hx => hx.1
  have hgoodFinite : mu good ≠ ⊤ :=
    measure_ne_top_of_subset hgoodSubset hmus
  have hbadWeighted :
      IntegrableOn (fun x => f x ^ 2 * w x) (s \ good) mu :=
    hweighted.mono_set diff_subset
  have hgoodWeighted :
      IntegrableOn (fun x => f x ^ 2 * w x) good mu :=
    hweighted.mono_set hgoodSubset
  have hbadThreshold :
      IntegrableOn (fun x => C ^ 2 * w x) (s \ good) mu :=
    (hweight.mono_set diff_subset).const_mul (C ^ 2)
  have hgoodEnvelope :
      IntegrableOn (fun _ : alpha => B) good mu :=
    integrableOn_const hgoodFinite
  have hbadLe :
      (∫ x in s \ good, f x ^ 2 * w x ∂mu) ≤
        C ^ 2 * ∫ x in s, w x ∂mu := by
    calc
      (∫ x in s \ good, f x ^ 2 * w x ∂mu) ≤
          ∫ x in s \ good, C ^ 2 * w x ∂mu := by
        apply setIntegral_mono_on hbadWeighted hbadThreshold
          (hs.diff hgood)
        intro x hx
        have habs : |f x| ≤ C := by
          exact le_of_not_gt fun hlarge => hx.2 ⟨hx.1, hlarge⟩
        have hsq : f x ^ 2 ≤ C ^ 2 := by
          nlinarith [sq_abs (f x), abs_nonneg (f x)]
        exact mul_le_mul_of_nonneg_right hsq (hwNonneg x)
      _ = C ^ 2 * ∫ x in s \ good, w x ∂mu := by
        rw [integral_const_mul]
      _ ≤ C ^ 2 * ∫ x in s, w x ∂mu := by
        exact mul_le_mul_of_nonneg_left
          (setIntegral_mono_set hweight
            (Filter.Eventually.of_forall hwNonneg)
            (Filter.Eventually.of_forall fun x hx => hx.1))
          (sq_nonneg C)
  have hgoodLe :
      (∫ x in good, f x ^ 2 * w x ∂mu) ≤
        B * mu.real good := by
    calc
      (∫ x in good, f x ^ 2 * w x ∂mu) ≤
          ∫ _x in good, B ∂mu := by
        apply setIntegral_mono_on hgoodWeighted hgoodEnvelope hgood
        intro x hx
        exact hbound x hx.1
      _ = B * mu.real good := by
        simp [measureReal_def, mul_comm]
  have hdiff :=
    setIntegral_diff hgood hweighted hgoodSubset
  have htotalLe :
      (∫ x in s, f x ^ 2 * w x ∂mu) ≤
        C ^ 2 * ∫ x in s, w x ∂mu +
          B * mu.real good := by
    linarith [hdiff]
  dsimp [good] at htotalLe ⊢
  linarith

end MathlibAux
