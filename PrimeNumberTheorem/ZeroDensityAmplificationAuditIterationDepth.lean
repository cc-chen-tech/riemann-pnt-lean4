import PrimeNumberTheorem.ZeroDensityAmplificationAuditIteration

namespace PrimeNumberTheorem

open scoped BigOperators

/-- If each depth-`n` certificate provides `q(T)^n` branches, then the windowed
lower count is at least `k · q(T)^n`, where `k = localContribution`. -/
theorem iterativeBranch_qpow_lowerCount_ge_qpow
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (q : ℝ → ℕ) (n : ℕ) (hn : n < C.depth)
    (hbranch : ∀ᶠ T in Filter.atTop, (q T ^ n) ≤ C.branchCount n T) :
    ∀ᶠ T in Filter.atTop,
      disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
          (C.windowStart n) realPart ordinate sigma H T ≥
          ((C.localContribution : ℝ) * (q T ^ n)) := by
  filter_upwards [iterativeBranch_lowerCount_ge_q (C := C) (n := n) hn, hbranch] with T
      hlocal hq
  have hq' : (q T ^ n : ℝ) ≤ (C.branchCount n T : ℝ) := by
    exact_mod_cast hq
  exact (mul_le_mul_of_nonneg_left hq' (by exact_mod_cast (Nat.zero_le _))).trans hlocal

/-- A sharper contradiction template: to force the Carlson gap it is enough to
have a depth-`n` branching lower bound of size `q(T)^n`. -/
theorem iterativeBranch_qpow_carlson_contradiction
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (q : ℝ → ℕ)
    (hbranch : ∀ᶠ T in Filter.atTop, (q T ^ n) ≤ C.branchCount n T)
    (hlower :
      ∀ᶠ T in Filter.atTop,
        disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
          (C.windowStart n) realPart ordinate sigma H T ≤
          (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    (hgap :
      Filter.Tendsto
        (fun T =>
          (C.localContribution : ℝ) * (q T ^ n) -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False := by
  let hCarlson : CarlsonEventualMajorant sigma :=
    Classical.choice (exists_carlsonEventualMajorant hσ hσ1)
  have hbranch_lb :
      ∀ᶠ T in Filter.atTop,
        disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
          (C.windowStart n) realPart ordinate sigma H T ≥
            (C.localContribution : ℝ) * (q T ^ n) :=
    iterativeBranch_qpow_lowerCount_ge_qpow
      (C := C) (q := q) n hn hbranch
  have hgapBranch :
      Filter.Tendsto
        (fun T =>
          (C.localContribution : ℝ) * (C.branchCount n T) -
            (hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
              (Real.log (T + H)) ^ 4‖)) Filter.atTop Filter.atTop := by
    refine (Filter.tendsto_atTop.2 ?_)
    intro r
    have hgap_evt : ∀ᶠ T in Filter.atTop,
        r ≤ (C.localContribution : ℝ) * (q T ^ n) -
          (hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
            (Real.log (T + H)) ^ 4‖) :=
      by
        simpa [hCarlson] using (Filter.tendsto_atTop.1 hgap) r
    have hbranch_evt : ∀ᶠ T in Filter.atTop,
        (C.localContribution : ℝ) * (q T ^ n) -
            (hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
              (Real.log (T + H)) ^ 4‖) ≤
            (C.localContribution : ℝ) * (C.branchCount n T) -
              (hCarlson.C * ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖) := by
      filter_upwards [hbranch] with T hbranchT
      have hbranchT' : (C.localContribution : ℝ) * (q T ^ n) ≤
          (C.localContribution : ℝ) * (C.branchCount n T) := by
        exact_mod_cast (Nat.mul_le_mul_left (C.localContribution) hbranchT)
      exact sub_le_sub_right hbranchT' _
    filter_upwards [hgap_evt, hbranch_evt] with T hgapT hbranchT
    exact hgapT.trans hbranchT
  exact iterativeBranch_carlson_contradiction (realPart := realPart) (ordinate := ordinate)
    C n hn hσ hσ1 hlower hgapBranch

/-- A direct no-go witness: if depth-`n` branching is pointwise below Carlson order,
then no divergent additive `q(T)^n - Carlson(T)` gap can occur. -/
theorem iterativeBranch_qpow_not_enough_for_divergence_if_eventually_subdominant
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (q : ℝ → ℕ)
    (hsubdom :
      ∀ᶠ T in Filter.atTop,
        (C.localContribution : ℝ) * (q T ^ n) ≤
          (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
            ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖) :
    ¬ Filter.Tendsto
      (fun T =>
        (C.localContribution : ℝ) * (q T ^ n) -
          (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
            ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖)
      Filter.atTop Filter.atTop := by
  intro hgap
  have hsubdom_event :
      ∀ᶠ T in Filter.atTop,
        (C.localContribution : ℝ) * (q T ^ n) -
          (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
            ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖ ≤
            (0 : ℝ) := by
    filter_upwards [hsubdom] with T hT
    linarith
  have hgap_one : ∀ᶠ T in Filter.atTop, (1 : ℝ) ≤
      (C.localContribution : ℝ) * (q T ^ n) -
        (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
          ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖ :=
    (Filter.tendsto_atTop.1 hgap) 1
  rcases Filter.eventually_atTop.1 hgap_one with ⟨A, hA⟩
  have hsubdom_event' :
      ∀ᶠ T in Filter.atTop,
        (C.localContribution : ℝ) * (q T ^ n) -
          (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
            ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖ ≤
            (0 : ℝ) := hsubdom_event
  rcases Filter.eventually_atTop.1 hsubdom_event' with ⟨B, hB⟩
  let T0 : ℝ := max A B
  have hA' : 1 ≤
      (C.localContribution : ℝ) * (q T0 ^ n) -
        (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
          ‖(T0 + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T0 + H)) ^ 4‖ :=
    hA T0 (by exact le_max_left _ _)
  have hB' :
      (C.localContribution : ℝ) * (q T0 ^ n) -
        (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
          ‖(T0 + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T0 + H)) ^ 4‖ ≤ 0 :=
    hB T0 (by exact le_max_right _ _)
  linarith

end PrimeNumberTheorem
