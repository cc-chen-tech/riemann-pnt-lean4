import PrimeNumberTheorem.ZeroDensityAmplificationAuditIterationDepth

namespace PrimeNumberTheorem

/-!
Strict compatibility shape for half-isolated end-to-end output from the sibling commits
`fd657c0` / `7cf002e`.

These commits expose theorems such as
`PrimeNumberTheorem.HalfIsolatedZeroDichotomy.zero_isolated_or_cluster_of_top_layer`
and related local-cluster objects.  We keep this file as a thin adapter layer only,
not a copy of that source.
-/

/-- Half-isolated branch outputs are consumed through this shared certificate shape. -/
abbrev HalfIsolatedLocalClusterCertificate
    (ι ρ : Type*) [DecidableEq ι] [DecidableEq ρ]
    (realPart ordinate : ρ → ℝ) (sigma H : ℝ) :=
  IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
    (realPart := realPart) (ordinate := ordinate) sigma H

/-- Identity adapter: a half-isolated certificate produced by upstream code is directly
usable by the iterative bridge once it is shaped as
`HalfIsolatedLocalClusterCertificate`. -/
def halfIsolatedLocalCluster_to_iterative
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : HalfIsolatedLocalClusterCertificate (ι := ι) (ρ := ρ)
      realPart ordinate sigma H) :
    IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H :=
  C

/-- Consumer contract: the half-isolated adapter supports the q-power bridge once a
certified depth and q-bound are supplied. -/
theorem halfIsolatedAdapter_qpow_carlson_contradiction
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (Csrc : HalfIsolatedLocalClusterCertificate (ι := ι) (ρ := ρ)
      realPart ordinate sigma H)
    (n : ℕ) (hn : n < Csrc.depth)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (q : ℝ → ℕ)
    (hbranch : ∀ᶠ T in Filter.atTop, (q T ^ n) ≤ Csrc.branchCount n T)
    (hlower :
      ∀ᶠ T in Filter.atTop,
        disjointWindowFamilyLowerCount (Csrc.windows n) (Csrc.cluster n)
          (Csrc.windowStart n) realPart ordinate sigma H T ≤
          (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    (hgap :
      Filter.Tendsto
        (fun T =>
          (Csrc.localContribution : ℝ) * (q T ^ n) -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False := by
  -- `Csrc` is definitionally the same underlying structure as an
  -- `IterativeLocalBranchCertificate`, so this cast is definitional.
  exact iterativeBranch_qpow_carlson_contradiction
    (realPart := realPart) (ordinate := ordinate)
    (C := (Csrc : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H))
    n hn hσ hσ1 q hbranch hlower hgap

end PrimeNumberTheorem
