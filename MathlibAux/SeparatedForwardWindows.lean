import Mathlib

open MeasureTheory Set
open scoped BigOperators

namespace MathlibAux

noncomputable section

/-!
# Separated forward half-open windows

The window based at `a` is `[a, a + L)`.  The half-open convention is
essential: two windows whose centers differ by exactly `L` do not both own
their common endpoint.  Consequently pairwise `L`-separation gives the
actual overlap constant one, rather than an assumed overlap parameter.

The integration interface keeps the local integrand indexed by its center.
This permits genuinely moving window weights such as `weight a y`.
-/

/-- The forward half-open window `[a, a + L)`. -/
def forwardWindow (a L : ℝ) : Set ℝ :=
  Set.Ico a (a + L)

/-- The union of a finite family of forward windows. -/
def forwardWindowUnion (centers : Finset ℝ) (L : ℝ) : Set ℝ :=
  ⋃ a ∈ centers, forwardWindow a L

/-- Distinct finite centers have distance at least `L`. -/
def finiteCentersPairwiseSeparated (centers : Finset ℝ) (L : ℝ) : Prop :=
  ∀ ⦃a⦄, a ∈ centers → ∀ ⦃b⦄, b ∈ centers →
    a ≠ b → L ≤ |a - b|

/-- A right endpoint is excluded from its forward half-open window. -/
theorem forwardWindow_endpoint_not_mem (a L : ℝ) :
    a + L ∉ forwardWindow a L := by
  simp [forwardWindow]

/-- Pairwise center separation directly makes the forward windows disjoint.
Exact spacing by `L` is allowed because the right endpoint is excluded. -/
theorem pairwiseDisjoint_forwardWindow_of_pairwiseSeparated
    {centers : Finset ℝ} {L : ℝ}
    (hsep : finiteCentersPairwiseSeparated centers L) :
    (centers : Set ℝ).PairwiseDisjoint (fun a ↦ forwardWindow a L) := by
  intro a ha b hb hab
  change Disjoint (forwardWindow a L) (forwardWindow b L)
  rw [Set.disjoint_left]
  intro y hya hyb
  have hgap := hsep ha hb hab
  rcases le_total a b with habLe | hbaLe
  · have hdiff : |a - b| = b - a := by
      rw [abs_of_nonpos (sub_nonpos.mpr habLe)]
      ring
    have hright : a + L ≤ b := by
      rw [hdiff] at hgap
      linarith
    exact (not_lt_of_ge (hright.trans hyb.1)) hya.2
  · have hdiff : |a - b| = a - b := by
      rw [abs_of_nonneg (sub_nonneg.mpr hbaLe)]
    have hright : b + L ≤ a := by
      rw [hdiff] at hgap
      linarith
    exact (not_lt_of_ge (hright.trans hya.1)) hyb.2

/-- At every point, at most one separated forward window is active.  This is
the pointwise overlap bound with the actual constant `B = 1`. -/
noncomputable def activeForwardWindowCenters
    (centers : Finset ℝ) (L y : ℝ) : Finset ℝ := by
  classical
  exact centers.filter fun a ↦ y ∈ forwardWindow a L

theorem card_filter_mem_forwardWindow_le_one
    {centers : Finset ℝ} {L y : ℝ}
    (hsep : finiteCentersPairwiseSeparated centers L) :
    (activeForwardWindowCenters centers L y).card ≤ 1 := by
  classical
  unfold activeForwardWindowCenters
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  simp only [Finset.mem_filter] at ha hb
  by_contra hab
  have hdisjoint :=
    pairwiseDisjoint_forwardWindow_of_pairwiseSeparated hsep
      ha.1 hb.1 hab
  exact Set.disjoint_left.mp hdisjoint ha.2 hb.2

/-- Sum of local window integrals.  The integrand is indexed by the window
center, so this API supports center-dependent kernels. -/
noncomputable def accumulatedForwardWindowIntegral
    (centers : Finset ℝ) (L : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∑ a ∈ centers, ∫ y : ℝ in forwardWindow a L, f a y

/-- The global kernel obtained by extending every center-dependent local
integrand by zero outside its own forward window. -/
def globalForwardWindowKernel
    (centers : Finset ℝ) (L : ℝ) (f : ℝ → ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ a ∈ centers, (forwardWindow a L).indicator (f a) y

/-- Accumulated local energy is exactly the integral of its global finite
window kernel. -/
theorem accumulatedForwardWindowIntegral_eq_integral_globalWindowKernel
    (centers : Finset ℝ) (L : ℝ) (f : ℝ → ℝ → ℝ)
    (hInt : ∀ a ∈ centers, IntegrableOn (f a) (forwardWindow a L)) :
    accumulatedForwardWindowIntegral centers L f =
      ∫ y : ℝ, globalForwardWindowKernel centers L f y := by
  classical
  unfold accumulatedForwardWindowIntegral globalForwardWindowKernel
  rw [MeasureTheory.integral_finset_sum centers]
  · apply Finset.sum_congr rfl
    intro a ha
    simpa only [forwardWindow] using
      (MeasureTheory.integral_indicator
        (f := f a) (measurableSet_Ico : MeasurableSet (Set.Ico a (a + L)))).symm
  · intro a ha
    exact (hInt a ha).integrable_indicator measurableSet_Ico

/-- With pairwise separated centers, comparison on each local window sums to
one comparison on the union.  There is no overlap-loss factor: separation
proves the multiplicity is exactly at most one. -/
theorem accumulatedForwardWindowIntegral_le_unionIntegral_of_pairwiseSeparated
    {centers : Finset ℝ} {L : ℝ}
    {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ}
    (hsep : finiteCentersPairwiseSeparated centers L)
    (hfInt : ∀ a ∈ centers, IntegrableOn (f a) (forwardWindow a L))
    (hgInt : IntegrableOn g (forwardWindowUnion centers L))
    (hfg : ∀ a ∈ centers, ∀ y ∈ forwardWindow a L, f a y ≤ g y) :
    accumulatedForwardWindowIntegral centers L f ≤
      ∫ y : ℝ in forwardWindowUnion centers L, g y := by
  classical
  have hwindowSubset (a : ℝ) (ha : a ∈ centers) :
      forwardWindow a L ⊆ forwardWindowUnion centers L := by
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨a, ha, hy⟩
  have hgLocal : ∀ a ∈ centers,
      IntegrableOn g (forwardWindow a L) := by
    intro a ha
    exact hgInt.mono_set (hwindowSubset a ha)
  calc
    accumulatedForwardWindowIntegral centers L f ≤
        ∑ a ∈ centers, ∫ y : ℝ in forwardWindow a L, g y := by
      unfold accumulatedForwardWindowIntegral
      apply Finset.sum_le_sum
      intro a ha
      exact setIntegral_mono_on
        (hfInt a ha) (hgLocal a ha) measurableSet_Ico (hfg a ha)
    _ = ∫ y : ℝ in forwardWindowUnion centers L, g y := by
      unfold forwardWindowUnion
      exact
        (MeasureTheory.integral_biUnion_finset centers
          (fun _ _ ↦ measurableSet_Ico)
          (pairwiseDisjoint_forwardWindow_of_pairwiseSeparated hsep)
          hgLocal).symm

end

end MathlibAux
