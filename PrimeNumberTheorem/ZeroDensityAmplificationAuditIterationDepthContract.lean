import PrimeNumberTheorem.ZeroDensityAmplificationAuditIterationDepth

namespace PrimeNumberTheorem

/-- Depth-`n` q-powered local-branch bridge to Carlson contradiction. -/
example {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (sigma H : ℝ) (realPart ordinate : ρ → ℝ)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth)
    (q : ℝ → ℕ)
    (hbranch : ∀ᶠ T in Filter.atTop, (q T ^ n) ≤ C.branchCount n T)
    (hlower : ∀ᶠ T in Filter.atTop,
      disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
        (C.windowStart n) realPart ordinate sigma H T ≤
        (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    (hgap :
      Filter.Tendsto
        (fun T =>
          (C.localContribution : ℝ) * (q T ^ n) -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False :=
  iterativeBranch_qpow_carlson_contradiction
    (realPart := realPart) (ordinate := ordinate) C n hn hσ hσ1 q hbranch hlower hgap

/-- If q-powered lower bounds are eventually below Carlson scale, then the q-power
cannot produce a divergent gap. -/
example {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (sigma H : ℝ) (realPart ordinate : ρ → ℝ)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ) (hn : n < C.depth)
    (q : ℝ → ℕ)
    (hsubdom :
      ∀ᶠ T in Filter.atTop,
        (C.localContribution : ℝ) * (q T ^ n) ≤
          (Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
            ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖) :
    ¬
      Filter.Tendsto
        (fun T =>
          (C.localContribution : ℝ) * (q T ^ n) -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖))
      Filter.atTop Filter.atTop :=
  iterativeBranch_qpow_not_enough_for_divergence_if_eventually_subdominant
    (realPart := realPart) (ordinate := ordinate) C n hn hσ hσ1 q hsubdom

end PrimeNumberTheorem
