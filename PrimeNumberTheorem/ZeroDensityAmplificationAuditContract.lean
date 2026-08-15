import PrimeNumberTheorem.ZeroDensityAmplificationAudit

namespace PrimeNumberTheorem

/-- Finite-cluster comparison contract reused from the abstract growth layer. -/
example {ρ : Type*} (cluster : Finset ρ)
    (realPart ordinate : ρ → ℝ) (sigma H : ℝ) :
    ∀ᶠ T in Filter.atTop,
      (localClusterLowerBound
        cluster realPart ordinate sigma T H : ℝ) ≤ T :=
  finite_localClusterLowerBound_eventually_le_diverging_upper
    cluster realPart ordinate sigma H
    (Filter.tendsto_id : Filter.Tendsto (fun T : ℝ => T) Filter.atTop Filter.atTop)

/-- Growth-vs-upper-contract contract for a two-sided gap contradiction. -/
example {lower count upper : ℝ → ℝ}
    (hlower : ∀ᶠ T in Filter.atTop, lower T ≤ count T)
    (hupper : ∀ᶠ T in Filter.atTop, count T ≤ upper T)
    (hgap :
      Filter.Tendsto (fun T => lower T - upper T)
        Filter.atTop Filter.atTop) :
    False :=
  cluster_density_contradiction_of_gap_tendsto_atTop
    hlower hupper hgap

/-- Disjoint-window bridge into a concrete zero-count functional. -/
example {ρ ι : Type*} [DecidableEq ι] [DecidableEq ρ]
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
        (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ) :=
  disjointWindowFamilyLowerCount_eventually_le_zeroDensity windows cluster
    windowStart realPart ordinate sigma H hdisjoint ambient hinside hambient

/-- Finite disjoint-window family cannot realize a divergent additive gap. -/
example {ρ ι : Type*} [DecidableEq ι] [DecidableEq ρ]
    (windows : Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) {upper : ℝ → ℝ}
    (hupper : Filter.Tendsto upper Filter.atTop Filter.atTop) :
    ¬ Filter.Tendsto
        (fun T =>
          disjointWindowFamilyLowerCount (fun _ => windows)
            cluster windowStart realPart ordinate sigma H T - upper T)
        Filter.atTop Filter.atTop :=
  finiteDisjointWindowFamily_gap_not_tendsto_atTop
    windows cluster windowStart realPart ordinate sigma H hupper

/-- Explicit-Carlson contract instance (already available in repository). -/
example {ρ ι : Type*} [DecidableEq ι] [DecidableEq ρ]
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
    False :=
  disjointWindowFamily_carlson_instance_contradiction windows cluster
    windowStart realPart ordinate sigma H hσ hσ1 hlower hgap

/-- Half-isolated remainder contract is captured by `IsEventuallyHalfSmall`. -/
def HalfIsolatedDetectorAmplificationContract (detector : ℝ → ℝ) (amplitude : ℝ) : Prop :=
  HalfIsolatedDetectorContractOutput detector amplitude

/-- Half-isolated quantitative transfer contract shape from detector outputs. -/
example {error main detector : ℝ → ℝ} {A : ℝ}
    (hmain : HasFarSignedWitnesses main A)
    (hhalf : HalfIsolatedDetectorContractOutput detector A)
    (hdecomp : ∀ x, error x = main x + detector x) :
    HasFarSignedWitnesses error (A / 2) :=
  hasFarSignedWitnesses_add_of_eventuallyHalfSmall hmain hhalf hdecomp

end PrimeNumberTheorem
