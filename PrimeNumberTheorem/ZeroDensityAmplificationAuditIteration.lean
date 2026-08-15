import PrimeNumberTheorem.ZeroDensityAmplificationAudit

namespace PrimeNumberTheorem
open scoped BigOperators

/-- Window starts of a family at scale `T` are pairwise separated by at least `H`. -/
def windowStartPairwiseSeparated
    {ι : Type*} (I : Finset ι) (start : ι → ℝ) (H : ℝ) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
    start i + H < start j ∨ start j + H < start i

/-- Separated starts imply pairwise disjoint filtered slices inside those windows. -/
theorem windowStartPairwiseSeparated_disjointWindowClusterSlice
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (I : Finset ι) (cluster : ι → Finset ρ)
    (start : ι → ℝ) (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) (hsep : windowStartPairwiseSeparated I start H) :
    ((I : Set ι).PairwiseDisjoint fun i =>
      disjointWindowClusterSlice (cluster i) realPart ordinate sigma (start i) H) := by
  intro i hi j hj hij
  refine Finset.disjoint_left.2 ?_
  intro z hz_i hz_j
  have hz_i' := Finset.mem_filter.mp hz_i
  have hz_j' := Finset.mem_filter.mp hz_j
  have hz_i'1 : start i ≤ ordinate z := hz_i'.2.2.1
  have hz_i'2 : ordinate z ≤ start i + H := hz_i'.2.2.2
  have hz_j'1 : start j ≤ ordinate z := hz_j'.2.2.1
  have hz_j'2 : ordinate z ≤ start j + H := hz_j'.2.2.2
  have hpair : start i + H < start j ∨ start j + H < start i := hsep i hi j hj hij
  rcases hpair with hpair | hpair
  · have : start i + H < ordinate z := lt_of_lt_of_le hpair hz_j'1
    exact (not_lt_of_ge hz_i'2) this
  · have : start j + H < ordinate z := lt_of_lt_of_le hpair hz_i'1
    exact (not_lt_of_ge hz_j'2) this

/-- An iterable local-branch certificate for an amplification input.
`branchCount n T` is the extracted number of candidate windows at depth `n`.
`localContribution` is a depth-independent per-window lower bound. -/
structure IterativeLocalBranchCertificate
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (realPart ordinate : ρ → ℝ) (sigma H : ℝ) where
  depth : ℕ
  windows : ℕ → ℝ → Finset ι
  cluster : ℕ → ι → Finset ρ
  windowStart : ℕ → ι → ℝ
  branchCount : ℕ → ℝ → ℕ
  localContribution : ℕ
  hdepth_pos : 0 < depth
  hlocalContribution_pos : 0 < localContribution
  hadjacent :
    ∀ n, n < depth →
      ∀ᶠ T in Filter.atTop,
        windowStartPairwiseSeparated (windows n T) (windowStart n) H
  hbranches :
    ∀ n, n < depth →
      ∀ᶠ T in Filter.atTop, branchCount n T ≤ (windows n T).card
  hlocal :
    ∀ n, n < depth →
      ∀ᶠ T in Filter.atTop, ∀ i ∈ windows n T,
        localContribution ≤
          localClusterLowerBound (cluster n i) realPart ordinate sigma (windowStart n i) H

/-- Build explicit disjointness from the adjacency certificate. -/
theorem IterativeLocalBranchCertificate.disjointWindowClusterSlices
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth) :
    ∀ᶠ T in Filter.atTop,
      ((C.windows n T : Set ι).PairwiseDisjoint fun i =>
        disjointWindowClusterSlice (C.cluster n i) realPart ordinate sigma (C.windowStart n i) H) := by
  filter_upwards [C.hadjacent n hn] with T hsep
  exact windowStartPairwiseSeparated_disjointWindowClusterSlice
    (C.windows n T) (C.cluster n) (C.windowStart n) realPart ordinate sigma H hsep

/--
From a depth-`n` branch certificate: if each used local cluster contributes at least
`k` and there are at least `q(n, T)` branches at height `T`, then the disjoint window
count is at least `k * q(n, T)` from that depth alone.
-/
theorem iterativeBranch_lowerCount_ge_q
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth) :
    ∀ᶠ T in Filter.atTop,
      disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
        (C.windowStart n) realPart ordinate sigma H T ≥
          ((C.localContribution : ℝ) * (C.branchCount n T)) := by
  filter_upwards [C.hlocal n hn, C.hbranches n hn] with T hlocal hbranch
  have hcard :
      C.localContribution * (C.branchCount n T) ≤
        Finset.sum (C.windows n T) (fun i =>
          localClusterLowerBound (C.cluster n i) realPart ordinate
            sigma (C.windowStart n i) H) := by
    have hcard' :
        C.localContribution * (C.branchCount n T) ≤
          C.localContribution * (C.windows n T).card :=
      Nat.mul_le_mul_left _ hbranch
    have hsum :
        C.localContribution * (C.windows n T).card ≤
          Finset.sum (C.windows n T) (fun i =>
            localClusterLowerBound (C.cluster n i) realPart ordinate
              sigma (C.windowStart n i) H) := by
      have hsum' :
          C.localContribution * (C.windows n T).card =
            Finset.sum (C.windows n T) (fun _ =>
              (C.localContribution : ℕ)) := by
        calc
          C.localContribution * (C.windows n T).card =
              (C.windows n T).card * C.localContribution := by
            exact Nat.mul_comm _ _
          _ = Finset.sum (C.windows n T) (fun _ =>
                (C.localContribution : ℕ)) := by
            simp
      have hsum'' :
          Finset.sum (C.windows n T) (fun _ =>
            (C.localContribution : ℕ)) ≤
            Finset.sum (C.windows n T) (fun i =>
              localClusterLowerBound (C.cluster n i) realPart ordinate
                sigma (C.windowStart n i) H) :=
        Finset.sum_le_sum (fun i hi => by
          exact hlocal i hi)
      exact (le_of_eq hsum').trans hsum''
    exact hcard'.trans hsum
  have hcardReal :
      (C.localContribution * (C.branchCount n T) : ℝ) ≤
        disjointWindowFamilyLowerCountNat (C.windows n) (C.cluster n)
          (C.windowStart n) realPart ordinate sigma H T := by
    exact_mod_cast hcard
  simpa [disjointWindowFamilyLowerCount, Nat.cast_mul, mul_assoc] using hcardReal

/--
Depth-`n`, branch-count witness `q(n, T)` together with Carlson's eventual majorant
implies contradiction if the amplified lower bound forces a divergent additive gap.
-/
theorem iterativeBranch_carlson_contradiction
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (hlower :
      ∀ᶠ T in Filter.atTop,
        disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
          (C.windowStart n) realPart ordinate sigma H T ≤
          (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    (hgap :
      Filter.Tendsto
        (fun T =>
          (C.localContribution : ℝ) * (C.branchCount n T) -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False := by
  let hCarlson : CarlsonEventualMajorant sigma :=
    Classical.choice (exists_carlsonEventualMajorant hσ hσ1)
  have hlower' :
      ∀ᶠ T in Filter.atTop, (C.localContribution : ℝ) * (C.branchCount n T) ≤
        disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
          (C.windowStart n) realPart ordinate sigma H T :=
    iterativeBranch_lowerCount_ge_q (realPart := realPart) (ordinate := ordinate)
      (sigma := sigma) (H := H) C n hn
  have hgap' :
      Filter.Tendsto
        (fun T =>
          disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
            (C.windowStart n) realPart ordinate sigma H T -
            (hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
              (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop := by
    refine (Filter.tendsto_atTop.2 ?_)
    intro r
    have hA := (Filter.tendsto_atTop.1 hgap) r
    filter_upwards [hA, hlower'] with T hA' hlower''
    have hupper : (C.localContribution : ℝ) * (C.branchCount n T) ≤
        disjointWindowFamilyLowerCount (C.windows n) (C.cluster n) (C.windowStart n)
          realPart ordinate sigma H T := hlower''
    linarith
  have hgapCarlson :
      Filter.Tendsto
        (fun T =>
          disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
            (C.windowStart n) realPart ordinate sigma H T -
              (hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop := by
    simpa [hCarlson] using hgap'
  exact disjointWindowFamily_carlson_instance_contradiction
    (windows := C.windows n) (cluster := C.cluster n)
    (windowStart := C.windowStart n) (realPart := realPart)
    (ordinate := ordinate) (sigma := sigma) (H := H) hσ hσ1 hlower hgapCarlson

/--
Strict no-go theorem for a single-window (single zero) offline certificate:
if only one window survives and each per-window cluster has size at most 1,
then no divergent `k*q(T) - Carlson(T)` gap can be produced.
-/
theorem one_offline_zero_certificate_does_not_yield_diverging_gap
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (sigma H : ℝ)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ)
    (realPart ordinate : ρ → ℝ)
    (hwindow_card : ∀ T, (windows T).card ≤ 1)
    (hcluster_card : ∀ i, (cluster i).card ≤ 1)
    (hmajorant_diverges :
      Filter.Tendsto
        (fun T =>
          (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
            ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖)
        Filter.atTop Filter.atTop) :
    ¬ Filter.Tendsto
        (fun T =>
          disjointWindowFamilyLowerCount windows cluster windowStart
            realPart ordinate sigma H T -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop := by
  have hbound : ∀ T, disjointWindowFamilyLowerCount windows cluster windowStart
      realPart ordinate sigma H T ≤ (1 : ℝ) := by
    intro T
    have hnat :
        disjointWindowFamilyLowerCountNat windows cluster windowStart
            realPart ordinate sigma H T ≤ (windows T).card := by
      unfold disjointWindowFamilyLowerCountNat
      have hsum :
          Finset.sum (windows T) (fun i =>
            localClusterLowerBound (cluster i) realPart ordinate
              sigma (windowStart i) H) ≤
            Finset.sum (windows T) (fun i => (cluster i).card) := by
        exact Finset.sum_le_sum (fun i hi =>
          localClusterLowerBound_le_card (cluster i) realPart ordinate
            sigma (windowStart i) H)
      have hsum' :
          Finset.sum (windows T) (fun i => (cluster i).card) ≤
            Finset.sum (windows T) (fun _ => (1 : ℕ)) := by
        exact Finset.sum_le_sum (fun i hi =>
          by simpa using hcluster_card i)
      have hsum'' : Finset.sum (windows T) (fun _ => (1 : ℕ)) = (windows T).card := by
        simp
      exact hsum.trans (hsum'.trans (le_of_eq hsum''))
    have hcard : (windows T).card ≤ 1 := hwindow_card T
    have hnat' : disjointWindowFamilyLowerCountNat windows cluster windowStart
        realPart ordinate sigma H T ≤ 1 := hnat.trans hcard
    exact (show
      disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate sigma H T ≤ (1 : ℝ) from
      by
        simpa [disjointWindowFamilyLowerCount] using
          (show (disjointWindowFamilyLowerCountNat windows cluster windowStart realPart
              ordinate sigma H T : ℝ) ≤ (1 : ℝ) by
            exact_mod_cast hnat'))
  exact bounded_lower_sub_diverging_upper_not_tendsto_atTop (1 : ℝ) hbound
    hmajorant_diverges

end PrimeNumberTheorem
