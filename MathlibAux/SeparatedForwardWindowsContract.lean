import MathlibAux.SeparatedForwardWindows

open MeasureTheory Set
open scoped BigOperators

namespace MathlibAux

#check forwardWindow
#check forwardWindowUnion
#check finiteCentersPairwiseSeparated
#check activeForwardWindowCenters
#check accumulatedForwardWindowIntegral
#check globalForwardWindowKernel

#check
  (forwardWindow_endpoint_not_mem :
    ∀ (a L : ℝ), a + L ∉ forwardWindow a L)

#check
  (pairwiseDisjoint_forwardWindow_of_pairwiseSeparated :
    ∀ {centers : Finset ℝ} {L : ℝ},
      finiteCentersPairwiseSeparated centers L →
      (centers : Set ℝ).PairwiseDisjoint
        (fun a ↦ forwardWindow a L))

#check
  (card_filter_mem_forwardWindow_le_one :
    ∀ {centers : Finset ℝ} {L y : ℝ},
      finiteCentersPairwiseSeparated centers L →
      (activeForwardWindowCenters centers L y).card ≤ 1)

#check
  (accumulatedForwardWindowIntegral_eq_integral_globalWindowKernel :
    ∀ (centers : Finset ℝ) (L : ℝ) (f : ℝ → ℝ → ℝ),
      (∀ a ∈ centers, IntegrableOn (f a) (forwardWindow a L)) →
      accumulatedForwardWindowIntegral centers L f =
        ∫ y : ℝ, globalForwardWindowKernel centers L f y)

#check
  (accumulatedForwardWindowIntegral_le_unionIntegral_of_pairwiseSeparated :
    ∀ {centers : Finset ℝ} {L : ℝ}
      {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ},
      finiteCentersPairwiseSeparated centers L →
      (∀ a ∈ centers, IntegrableOn (f a) (forwardWindow a L)) →
      IntegrableOn g (forwardWindowUnion centers L) →
      (∀ a ∈ centers, ∀ y ∈ forwardWindow a L, f a y ≤ g y) →
      accumulatedForwardWindowIntegral centers L f ≤
        ∫ y : ℝ in forwardWindowUnion centers L, g y)

/-- Exact spacing by `L` is allowed, and the shared endpoint belongs only to
the later half-open window. -/
example {a L : ℝ} (hL : 0 < L) :
    a + L ∉ forwardWindow a L ∧
      a + L ∈ forwardWindow (a + L) L := by
  constructor
  · exact forwardWindow_endpoint_not_mem a L
  · simp [forwardWindow, hL]

/-- An empty family has no active windows. -/
example (L y : ℝ) :
    (activeForwardWindowCenters ∅ L y).card = 0 := by
  simp [activeForwardWindowCenters]

/-- A single nonempty window has occupancy one at an interior point. -/
example :
    (activeForwardWindowCenters {0} 1 (1 / 2)).card = 1 := by
  norm_num [activeForwardWindowCenters, forwardWindow,
    Finset.filter_insert, Finset.filter_singleton]

/-- At exact spacing, the shared coordinate is owned only by the later
window, so the occupancy is one. -/
example :
    (activeForwardWindowCenters {0, 1} 1 1).card = 1 := by
  norm_num [activeForwardWindowCenters, forwardWindow,
    Finset.filter_insert, Finset.filter_singleton]

/-- Without separation, two forward windows can really overlap. -/
example :
    (activeForwardWindowCenters {0, 1 / 2} 1 (3 / 4)).card = 2 := by
  norm_num [activeForwardWindowCenters, forwardWindow,
    Finset.filter_insert, Finset.filter_singleton]

end MathlibAux
