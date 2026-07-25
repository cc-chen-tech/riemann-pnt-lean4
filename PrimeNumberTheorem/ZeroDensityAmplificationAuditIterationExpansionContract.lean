import PrimeNumberTheorem.ZeroDensityAmplificationAuditIterationExpansion

namespace PrimeNumberTheorem

/-- Layer growth lower bound, expressed as a contract-style bridge use-case. -/
example {ι : Type*} [DecidableEq ι]
    (L : IterativeWindowLayerCertificate (ι := ι)) (n : ℕ) (hn : n ≤ L.depth) :
    ∀ᶠ T in Filter.atTop,
      L.q T ^ n ≤ (iterativeWindowLayer L.roots L.children n T).card :=
  iterativeWindowLayer_qpow_lowerBound (C := L) n hn

/-- Shared-neighbor countermodel is directly available as a non-derivable scenario. -/
example : ¬ ∀ᶠ T in Filter.atTop,
    (2 : ℕ) ^ 2 ≤ (iterativeWindowLayer overlappingRoots overlappingChildren 2 T).card :=
  sharedNeighborModel_not_exponential

/-- From disjoint-subcertificate expansion to Carlson contradiction for an iterative certificate. -/
example {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hdepth : n < C.depth)
    (L : IterativeWindowLayerCertificate (ι := ι)) (hn : n ≤ L.depth)
    (hbranch_le :
      ∀ᶠ T in Filter.atTop,
        (iterativeWindowLayer L.roots L.children n T).card ≤ C.branchCount n T)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (hlower :
      ∀ᶠ T in Filter.atTop,
        disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
            (C.windowStart n) realPart ordinate sigma H T ≤
            (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    (hgap :
      Filter.Tendsto
        (fun T =>
          (C.localContribution : ℝ) * (L.q T ^ n) -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False :=
  iterativeWindowLayer_to_carlson_contradiction (realPart := realPart)
    (ordinate := ordinate) C n hdepth L hn hbranch_le hσ hσ1 hlower hgap

end PrimeNumberTheorem
