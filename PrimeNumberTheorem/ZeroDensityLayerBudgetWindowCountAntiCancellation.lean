import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterSeedExtension

/-!
# Window-count anti-cancellation transfer

Eventual pointwise smallness is stronger than needed to preserve an
oscillation witness.  It is enough that, arbitrarily far out, the number of
main-term good points exceeds the number of remainder-bad points.

This module records a finite-window counting interface.  It is intended to
accept good-point counts from local mean-square oscillation and bad-point
counts from density or second-moment estimates.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Arbitrarily far finite windows contain more `good` points than points
needed to cover all `bad` members of the chosen good set. -/
def HasFarWindowCardAdvantage
    (good bad : ℕ → Prop) : Prop :=
  ∀ M : ℕ, ∃ G B : Finset ℕ,
    (∀ m ∈ G, M ≤ m) ∧
    (∀ m ∈ G, good m) ∧
    (∀ m ∈ G, bad m → m ∈ B) ∧
    B.card < G.card

/-- A strict finite good-versus-bad cardinality advantage produces a point
that is good and not bad beyond every prescribed threshold. -/
theorem HasFarWindowCardAdvantage.exists_good_not_bad
    {good bad : ℕ → Prop}
    (hcount : HasFarWindowCardAdvantage good bad) :
    ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ good m ∧ ¬ bad m := by
  intro M
  rcases hcount M with ⟨G, B, hfar, hgood, hcover, hcard⟩
  by_contra hnone
  have hall :
      ∀ m : ℕ, M ≤ m → good m → bad m := by
    intro m hmM hgoodM
    by_contra hnotBad
    exact hnone ⟨m, hmM, hgoodM, hnotBad⟩
  have hsub : G ⊆ B := by
    intro m hmG
    exact hcover m hmG (hall m (hfar m hmG) (hgood m hmG))
  exact (not_lt_of_ge (Finset.card_le_card hsub)) hcard

/-- Unsigned oscillation survives when good main points outnumber bad
remainder points in arbitrarily far finite windows. -/
theorem HasFarWindowCardAdvantage.unsignedTransfer
    {f main remainder amplitude : ℕ → ℝ}
    {c loss : ℝ}
    (hcount :
      HasFarWindowCardAdvantage
        (fun m => c * amplitude m ≤ |main m|)
        (fun m => loss * amplitude m ≤ |remainder m|))
    (hdecomp : ∀ m, f m = main m + remainder m) :
    HasFarNaturalPointTargetAmplitudeWitness
      f (fun m => (c - loss) * amplitude m) := by
  intro M
  rcases hcount.exists_good_not_bad M with
    ⟨m, hmM, hmain, hnotBad⟩
  have hsmall : |remainder m| < loss * amplitude m :=
    lt_of_not_ge hnotBad
  have hrewrite :
      main m = (main m + remainder m) + (-remainder m) := by
    ring
  have htriangle :
      |main m| ≤ |main m + remainder m| + |remainder m| := by
    calc
      |main m| =
          |(main m + remainder m) + (-remainder m)| :=
        congrArg abs hrewrite
      _ ≤ |main m + remainder m| + |-remainder m| :=
        abs_add_le _ _
      _ = |main m + remainder m| + |remainder m| := by
        rw [abs_neg]
  refine ⟨m, hmM, ?_⟩
  rw [hdecomp m]
  linarith

/-- Positive signed oscillation obeys the same window-count transfer. -/
theorem HasFarWindowCardAdvantage.positiveTransfer
    {f main remainder amplitude : ℕ → ℝ}
    {c loss : ℝ}
    (hcount :
      HasFarWindowCardAdvantage
        (fun m => c * amplitude m ≤ main m)
        (fun m => loss * amplitude m ≤ |remainder m|))
    (hdecomp : ∀ m, f m = main m + remainder m) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness
      f (fun m => (c - loss) * amplitude m) := by
  intro M
  rcases hcount.exists_good_not_bad M with
    ⟨m, hmM, hmain, hnotBad⟩
  have hsmall : |remainder m| < loss * amplitude m :=
    lt_of_not_ge hnotBad
  have hlower : -|remainder m| ≤ remainder m :=
    neg_abs_le (remainder m)
  refine ⟨m, hmM, ?_⟩
  rw [hdecomp m]
  linarith

/-- Negative signed oscillation obeys the same window-count transfer. -/
theorem HasFarWindowCardAdvantage.negativeTransfer
    {f main remainder amplitude : ℕ → ℝ}
    {c loss : ℝ}
    (hcount :
      HasFarWindowCardAdvantage
        (fun m => main m ≤ -(c * amplitude m))
        (fun m => loss * amplitude m ≤ |remainder m|))
    (hdecomp : ∀ m, f m = main m + remainder m) :
    HasFarNaturalPointNegativeTargetAmplitudeWitness
      f (fun m => (c - loss) * amplitude m) := by
  intro M
  rcases hcount.exists_good_not_bad M with
    ⟨m, hmM, hmain, hnotBad⟩
  have hsmall : |remainder m| < loss * amplitude m :=
    lt_of_not_ge hnotBad
  have hupper : remainder m ≤ |remainder m| :=
    le_abs_self (remainder m)
  refine ⟨m, hmM, ?_⟩
  rw [hdecomp m]
  linarith

/-- Specialized unsigned transfer from a finite seed to an expanded visible
cluster using a window-count advantage instead of eventual smallness. -/
theorem
    hasFarNaturalPointTargetAmplitudeWitness_visibleCluster_of_seed_windowCount
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hcount :
      HasFarWindowCardAdvantage
        (fun m =>
          c * amplitude m ≤
            |dynamicVisibleClusterPNTMain T S₀ (m : ℝ)|)
        (fun m =>
          loss * amplitude m ≤
            |dynamicVisibleClusterPNTMain T (S \ S₀) (m : ℝ)|)) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m => dynamicVisibleClusterPNTMain T S (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hcount.unsignedTransfer
  intro m
  exact dynamicVisibleClusterPNTMain_eq_seed_add_extension T hsub (m : ℝ)

/-- Specialized positive signed seed-extension window transfer. -/
theorem
    hasFarNaturalPointPositiveTargetAmplitudeWitness_visibleCluster_of_seed_windowCount
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hcount :
      HasFarWindowCardAdvantage
        (fun m =>
          c * amplitude m ≤
            dynamicVisibleClusterPNTMain T S₀ (m : ℝ))
        (fun m =>
          loss * amplitude m ≤
            |dynamicVisibleClusterPNTMain T (S \ S₀) (m : ℝ)|)) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness
      (fun m => dynamicVisibleClusterPNTMain T S (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hcount.positiveTransfer
  intro m
  exact dynamicVisibleClusterPNTMain_eq_seed_add_extension T hsub (m : ℝ)

/-- Specialized negative signed seed-extension window transfer. -/
theorem
    hasFarNaturalPointNegativeTargetAmplitudeWitness_visibleCluster_of_seed_windowCount
    (T : ℝ → ℝ) {S₀ S : Finset ℂ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hcount :
      HasFarWindowCardAdvantage
        (fun m =>
          dynamicVisibleClusterPNTMain T S₀ (m : ℝ) ≤
            -(c * amplitude m))
        (fun m =>
          loss * amplitude m ≤
            |dynamicVisibleClusterPNTMain T (S \ S₀) (m : ℝ)|)) :
    HasFarNaturalPointNegativeTargetAmplitudeWitness
      (fun m => dynamicVisibleClusterPNTMain T S (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hcount.negativeTransfer
  intro m
  exact dynamicVisibleClusterPNTMain_eq_seed_add_extension T hsub (m : ℝ)

end PrimeNumberTheorem
