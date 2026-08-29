import MathlibAux.ArgumentCrossing

open scoped BigOperators

open Set
open MathlibAux

-- Mutation caught: deleting arbitrary bad levels costs at most their full
-- cardinality, while the endpoint-rounding loss remains the single global
-- loss already present in `argumentCrossingIndices_card_lower_bound`.
example {alpha beta : ℝ} (bad : Finset ℤ) :
    (beta - alpha) / Real.pi - 1 - bad.card ≤
      ((argumentCrossingIndices alpha beta) \ bad).card := by
  exact argumentCrossingIndices_sdiff_card_lower_bound bad

#print axioms argumentCrossingIndices_sdiff_card_lower_bound

-- A half-open phase bridge of length `m * pi` contains exactly `m` global
-- crossing levels, including the endpoint-aligned cases.
example {alpha : ℝ} {m : ℕ} {k : ℤ} :
    k ∈ argumentCrossingBridgeIndices alpha m ↔
      argumentCrossingLevel k ∈ Set.Ico alpha (alpha + m * Real.pi) := by
  exact mem_argumentCrossingBridgeIndices_iff

example (alpha : ℝ) (m : ℕ) :
    (argumentCrossingBridgeIndices alpha m).card = m := by
  exact argumentCrossingBridgeIndices_card alpha m

#print axioms argumentCrossingBridgeIndices_card

-- The union of all local order bridges costs at most the total multiplicity;
-- overlaps can only decrease the number of deleted global levels.
example {ι : Type*} [DecidableEq ι] (zeros : Finset ι)
    (alpha : ι → ℝ) (multiplicity : ι → ℕ) :
    (zeros.biUnion fun i =>
      argumentCrossingBridgeIndices (alpha i) (multiplicity i)).card ≤
      ∑ i ∈ zeros, multiplicity i := by
  exact card_biUnion_argumentCrossingBridgeIndices_le zeros alpha multiplicity

-- Deleting every bridge level retains the single global endpoint loss and
-- pays only the sum of zero orders.
example {ι : Type*} [DecidableEq ι] {alpha beta : ℝ}
    (zeros : Finset ι) (bridgeStart : ι → ℝ) (multiplicity : ι → ℕ) :
    (beta - alpha) / Real.pi - 1 - (∑ i ∈ zeros, multiplicity i) ≤
      ((argumentCrossingIndices alpha beta) \
        (zeros.biUnion fun i =>
          argumentCrossingBridgeIndices (bridgeStart i) (multiplicity i))).card := by
  exact argumentCrossingIndices_sdiff_bridgeUnion_card_lower_bound
    zeros bridgeStart multiplicity

#print axioms card_biUnion_argumentCrossingBridgeIndices_le
#print axioms argumentCrossingIndices_sdiff_bridgeUnion_card_lower_bound

-- The explicit logarithms of the two vertical power factors exponentiate to
-- the correct sides and differ in argument by exactly `m * pi`.
example (m : ℕ) {r : ℝ} (hr : 0 < r) :
    Complex.exp (verticalPowerLeftLog m r) =
      (-Complex.I * (r : ℂ)) ^ m := by
  exact exp_verticalPowerLeftLog m hr

example (m : ℕ) {r : ℝ} (hr : 0 < r) :
    Complex.exp (verticalPowerRightLog m r) =
      (Complex.I * (r : ℂ)) ^ m := by
  exact exp_verticalPowerRightLog m hr

example (m : ℕ) (r : ℝ) :
    (verticalPowerRightLog m r).im -
        (verticalPowerLeftLog m r).im = (m : ℝ) * Real.pi := by
  exact verticalPowerRightLog_im_sub_left m r

#print axioms verticalPowerRightLog_im_sub_left

-- A nonvanishing continuous complex curve on a real open interval admits one
-- continuous logarithm across the entire interval, even when the principal
-- logarithm would cross its branch cut.
example {g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, g x ≠ 0) :
    ∃ ell : ℝ → ℂ,
      ContinuousOn ell (Set.Ioo a b) ∧
      ∀ x ∈ Set.Ioo a b, Complex.exp (ell x) = g x := by
  exact exists_continuousLogOn_Ioo hab hg hne

#print axioms exists_continuousLogOn_Ioo
