import PrimeNumberTheorem.ZeroDensityAmplificationAuditIteration

namespace PrimeNumberTheorem

/-- Local branch-to-window bridge. -/
example {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (sigma H : ℝ) (realPart ordinate : ρ → ℝ)
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth) :
  ∀ᶠ T in Filter.atTop,
      disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
        (C.windowStart n) realPart ordinate sigma H T ≥
          ((C.localContribution : ℝ) * (C.branchCount n T)) :=
  iterativeBranch_lowerCount_ge_q (realPart := realPart) (ordinate := ordinate)
    (sigma := sigma) (H := H) C n hn

/-- Depth-`n` branch certificate to Carlson contradiction. -/
example {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (sigma H : ℝ) (realPart ordinate : ρ → ℝ)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth)
    (hlower : ∀ᶠ T in Filter.atTop,
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
    False :=
  iterativeBranch_carlson_contradiction (realPart := realPart) (ordinate := ordinate)
    C n hn hσ hσ1 hlower hgap

/-- One-offline-zero certificate cannot provide a divergent branch-gap. -/
example {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (sigma H : ℝ) (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (realPart ordinate : ρ → ℝ)
    (windows : ℝ → Finset ι) (cluster : ι → Finset ρ)
    (windowStart : ι → ℝ)
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
        disjointWindowFamilyLowerCount windows cluster windowStart realPart ordinate
          sigma H T -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
      Filter.atTop Filter.atTop :=
  one_offline_zero_certificate_does_not_yield_diverging_gap
    (realPart := realPart) (ordinate := ordinate)
    sigma H hσ hσ1 windows cluster windowStart hwindow_card hcluster_card hmajorant_diverges

end PrimeNumberTheorem
