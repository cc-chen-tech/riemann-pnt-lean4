import PrimeNumberTheorem.ZeroDensityClusterComparisonGrowth
import PrimeNumberTheorem.ZeroDensityLayerBudgetAsymptoticTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson
import PrimeNumberTheorem.ZeroDensityCount

namespace PrimeNumberTheorem
open scoped BigOperators

/-- Windowed local cluster slice used to force a disjointness hypothesis. -/
noncomputable def disjointWindowClusterSlice
    {ρ : Type*} (cluster : Finset ρ) (realPart ordinate : ρ → ℝ)
    (sigma start H : ℝ) : Finset ρ :=
  cluster.filter fun rho => sigma ≤ realPart rho ∧ start ≤ ordinate rho ∧ ordinate rho ≤ start + H

/-- Total local-cluster witness count from finitely many height windows at height `T`. -/
noncomputable def disjointWindowFamilyLowerCountNat
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) (T : ℝ) : ℕ :=
  Finset.sum (windows T) fun i =>
    localClusterLowerBound (cluster i) realPart ordinate sigma (windowStart i) H

/-- Real-valued variant used by the growth interface. -/
noncomputable def disjointWindowFamilyLowerCount
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) (T : ℝ) : ℝ :=
  (disjointWindowFamilyLowerCountNat windows cluster windowStart realPart ordinate sigma H T : ℝ)

/--
From explicit height-window disjointness and a global ambient finite truncation,
accumulate local window counts into a single lower bound for `N`.
This is the non-overlap bridge needed before applying the growth contradiction.
-/
theorem disjointWindowFamilyLowerCount_eventually_le_zeroDensity
    {ρ ι : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ)
    (hdisjoint :
      ∀ᶠ T in Filter.atTop,
        ((windows T : Set ι).PairwiseDisjoint (fun i =>
          disjointWindowClusterSlice (cluster i) realPart ordinate
            sigma (windowStart i) H)))
    (ambient : ℝ → Finset ρ)
    (hinside :
      ∀ᶠ T in Filter.atTop,
        ∀ i ∈ windows T,
          disjointWindowClusterSlice (cluster i) realPart ordinate
              sigma (windowStart i) H ⊆ ambient (T + H))
    (hambient :
      ∀ᶠ T in Filter.atTop,
        ((ambient (T + H)).card : ℝ) ≤
          (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ)) :
    ∀ᶠ T in Filter.atTop,
      disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate sigma H T ≤
        (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ) := by
  filter_upwards [hdisjoint, hinside, hambient] with T hdisj hinside_T hambient
  let slice : ι → Finset ρ := fun i =>
    disjointWindowClusterSlice (cluster i) realPart ordinate sigma (windowStart i) H
  have hcard :
      (Finset.sum (windows T) (fun i => (slice i).card) : ℕ) =
        ((windows T).biUnion slice).card := by
    simpa [slice] using
      (Finset.card_biUnion (s := windows T) (t := slice) hdisj).symm
  have hsubset :
      (windows T).biUnion slice ⊆ ambient (T + H) := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, hi, hz⟩
    exact hinside_T i hi hz
  have hcard_union :
      (Finset.sum (windows T) (fun i => (slice i).card) : ℕ) ≤
        (ambient (T + H)).card := by
    simpa [hcard] using Finset.card_le_card hsubset
  have hcard_real :
      disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate sigma H T ≤
        ((ambient (T + H)).card : ℝ) := by
    dsimp [disjointWindowFamilyLowerCount, disjointWindowFamilyLowerCountNat]
    exact_mod_cast hcard_union
  exact hcard_real.trans hambient

/-- A fixed finite family of windows cannot force a divergent additive gap. -/
theorem finiteDisjointWindowFamily_gap_not_tendsto_atTop
    {ρ ι : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) {upper : ℝ → ℝ}
    (hupper : Filter.Tendsto upper Filter.atTop Filter.atTop) :
    ¬ Filter.Tendsto
        (fun T =>
          disjointWindowFamilyLowerCount (fun _ => windows)
            cluster windowStart realPart ordinate sigma H T - upper T)
        Filter.atTop Filter.atTop := by
  let B : ℝ := Finset.sum windows fun i => ((cluster i).card : ℝ)
  have hbound :
      ∀ T, disjointWindowFamilyLowerCount (fun _ => windows)
          cluster windowStart realPart ordinate sigma H T ≤ B := by
    intro T
    have hnat :
        disjointWindowFamilyLowerCountNat (fun _ => windows)
          cluster windowStart realPart ordinate sigma H T ≤
            (Finset.sum windows fun i => (cluster i).card) := by
      simpa [disjointWindowFamilyLowerCountNat] using
        Finset.sum_le_sum (fun i hi => localClusterLowerBound_le_card
          (cluster i) realPart ordinate sigma (windowStart i) H)
    have hreal :
        (disjointWindowFamilyLowerCountNat (fun _ => windows)
          cluster windowStart realPart ordinate sigma H T : ℝ) ≤
          (Finset.sum windows fun i => (cluster i).card : ℕ) := by
      exact_mod_cast hnat
    simpa [disjointWindowFamilyLowerCount, B, Nat.cast_sum] using hreal
  exact bounded_lower_sub_diverging_upper_not_tendsto_atTop B hbound hupper

/--
Concrete Carlson upper interface for a fixed `sigma` and a concrete `hCarlson` certificate.
-/
theorem disjointWindowFamily_carlson_contradiction
    {ρ ι : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) (hCarlson : CarlsonEventualMajorant sigma)
    (hlower :
      ∀ᶠ T in Filter.atTop,
        disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate sigma H T ≤
          (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    (hgap :
      Filter.Tendsto
        (fun T =>
          disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate sigma H T -
            (hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
              (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False := by
  have hupper' :
      ∀ᶠ T in Filter.atTop,
        (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ) ≤
          hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
            (Real.log (T + H)) ^ 4‖ := by
    simpa using (tendsto_add_const_atTop H).eventually hCarlson.bound
  exact cluster_density_contradiction_of_gap_tendsto_atTop hlower hupper' hgap

/--
Parameterized Carlson contradiction theorem with explicit `hσ` constraints and concrete
majorant certificate selection. The resulting contradiction is a real theorem chain,
not a parameter placeholder.
-/
theorem disjointWindowFamily_carlson_instance_contradiction
    {ρ ι : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (hlower :
      ∀ᶠ T in Filter.atTop,
        disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate sigma H T ≤
          (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    (hgap :
      Filter.Tendsto
        (fun T =>
          disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate sigma H T -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False := by
  let hCarlson : CarlsonEventualMajorant sigma :=
    Classical.choice (exists_carlsonEventualMajorant hσ hσ1)
  have hgap' :
      Filter.Tendsto
        (fun T =>
          disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate sigma H T -
            (hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
              (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop := by
    simpa [hCarlson] using hgap
  exact disjointWindowFamily_carlson_contradiction windows cluster
    windowStart realPart ordinate sigma H hCarlson hlower hgap'

/-- The minimal quantitative contract for half-isolated detectors. -/
def HalfIsolatedDetectorContractOutput (detector : ℝ → ℝ) (amplitude : ℝ) : Prop :=
  IsEventuallyHalfSmall detector amplitude

/--
Half-isolated branch with an explicit dynamic budget certificate. This is the
minimal contract: an explicit half-smallness bound is sufficient to transfer signed
remainder terms.
-/
theorem halfIsolatedDetectorOutput_survives_signed_witnesses
    {error main detector : ℝ → ℝ} {A : ℝ}
    (hmain : HasFarSignedWitnesses main A)
    (hhalf : HalfIsolatedDetectorContractOutput detector A)
    (hdecomp : ∀ x, error x = main x + detector x) :
    HasFarSignedWitnesses error (A / 2) :=
  hasFarSignedWitnesses_add_of_eventuallyHalfSmall hmain hhalf hdecomp

/--
Half-isolated detector transfer along a dynamic height schedule.
-/
theorem halfIsolatedDetectorOutput_survives_along_dynamic_budget
    {error main remainder height : ℝ → ℝ}
    {layerBudget : ℝ → ℝ → ℝ} {A : ℝ}
    (hpositive : 0 < A)
    (hmain : HasFarSignedWitnesses main A)
    (hcertificate : DynamicLayerRemainderCertificate remainder height layerBudget)
    (hzero :
      Filter.Tendsto (dynamicLayerBudgetAlong height layerBudget)
        Filter.atTop (nhds 0))
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarSignedWitnesses error (A / 2) :=
  hasFarSignedWitnesses_add_of_dynamicLayerBudget_tendsto_zero
    hpositive hmain hcertificate hzero hdecomp

end PrimeNumberTheorem
