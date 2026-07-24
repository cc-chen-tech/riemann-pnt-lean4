import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.Contract
open PrimeNumberTheorem.ZeroForcedOscillation

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace HalfIsolatedZeroDichotomy

/-- If two centers are separated by more than `2δ` in imaginary part, their
`δ`-windows on the same top layer are disjoint. -/
theorem topLayerWindow_disjoint_of_imag_separation
    (T β δ : ℝ) {ρ₁ ρ₂ : ℂ}
    (hδ : 0 < δ) (hρ : ρ₁ ≠ ρ₂) (hsep : 2 * δ < |ρ₁.im - ρ₂.im|) :
    Disjoint (TopLayerWindow T β δ ρ₁) (TopLayerWindow T β δ ρ₂) := by
  refine Finset.disjoint_left.2 ?_
  intro x hx₁ hx₂
  have hdist₁ : |x.im - ρ₁.im| ≤ δ := (Finset.mem_filter.mp hx₁).2
  have hdist₂ : |x.im - ρ₂.im| ≤ δ := (Finset.mem_filter.mp hx₂).2
  have himageq :
      |ρ₁.im - ρ₂.im| ≤ |ρ₁.im - x.im| + |x.im - ρ₂.im| := by
    calc
      |ρ₁.im - ρ₂.im|
          = |(ρ₁.im - x.im) + (x.im - ρ₂.im)| := by ring_nf
      _ ≤ |ρ₁.im - x.im| + |x.im - ρ₂.im| := abs_add _ _
  have hle : |ρ₁.im - ρ₂.im| ≤ 2 * δ := by
    linarith [himageq, hdist₁, hdist₂]
  exact (not_lt_of_ge hle) hsep

/-- Pairwise disjointness of windows under pairwise `2δ` separation. -/
theorem topLayerWindow_pairwise_disjoint_of_centers
    (T β δ : ℝ) (hδ : 0 < δ) (centers : Finset ℂ)
    (hsep : centers.Pairwise (fun ρ₁ ρ₂ => 2 * δ < |ρ₁.im - ρ₂.im|)) :
    centers.Pairwise (fun ρ₁ ρ₂ =>
      Disjoint (TopLayerWindow T β δ ρ₁) (TopLayerWindow T β δ ρ₂)) := by
  intro ρ₁ hρ₁ ρ₂ hρ₂ hne
  exact topLayerWindow_disjoint_of_imag_separation T β δ hδ hne (hsep hρ₁ hρ₂ hne)

/-- Sum of window-cardinalities is controlled by top-layer cardinality whenever
windows are pairwise disjoint. -/
theorem sum_topLayerWindow_card_le_topLayer_of_disjoint
    (T β δ : ℝ) (centers : Finset ℂ)
    (hdisj :
      centers.Pairwise (fun ρ₁ ρ₂ =>
        Disjoint (TopLayerWindow T β δ ρ₁) (TopLayerWindow T β δ ρ₂))
      ) :
    (∑ ρ ∈ centers, (TopLayerWindow T β δ ρ).card) ≤
      (TopLayerFinset T β).card := by
  have hcard_eq :
      (∑ ρ ∈ centers, (TopLayerWindow T β δ ρ).card) =
        (Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ)).card := by
    simpa using Finset.card_biUnion hdisj
  have hsubset : (Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ))
      ⊆ TopLayerFinset T β := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨ρ, hρ, hx⟩
    exact topLayerWindow_subset T β δ ρ hx
  have hle : (Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ)).card ≤
      (TopLayerFinset T β).card := Finset.card_le_card hsubset
  simpa [hcard_eq] using hle

/-- For pairwise disjoint windows with each window having at least two points,
`∪`-extracted finite family yields many different zeros. -/
theorem extract_many_distinct_zeros_from_disjoint_windows
    (T β δ : ℝ) (hδ : 0 < δ) (centers : Finset ℂ)
    (hdisj :
      centers.Pairwise (fun ρ₁ ρ₂ =>
        Disjoint (TopLayerWindow T β δ ρ₁) (TopLayerWindow T β δ ρ₂))
      )
    (htwo : ∀ ρ ∈ centers, 2 ≤ (TopLayerWindow T β δ ρ).card) :
    ∃ zset : Finset ℂ, zset ⊆ TopLayerFinset T β ∧
      2 * centers.card ≤ zset.card := by
  let zset : Finset ℂ := Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ)
  have hsubset :
      Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ) ⊆ TopLayerFinset T β := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨ρ, hρ, hx'⟩
    exact topLayerWindow_subset T β δ ρ hx'
  have hcard_eq :
      (∑ ρ ∈ centers, (TopLayerWindow T β δ ρ).card) =
        (Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ)).card := by
    simpa using Finset.card_biUnion hdisj
  have hsum_lower : 2 * centers.card ≤ (∑ ρ ∈ centers, (TopLayerWindow T β δ ρ).card) := by
    have hconst : (∑ _ in centers, (2 : ℕ)) = 2 * centers.card := by
      simp
    have hterm : (∑ _ in centers, (2 : ℕ)) ≤ ∑ ρ ∈ centers, (TopLayerWindow T β δ ρ).card := by
      exact Finset.sum_le_sum (fun ρ hρ => htwo ρ hρ)
    simpa [hconst] using hterm
  refine ⟨zset, ?_, ?_⟩
  · simpa [zset] using hsubset
  · rw [← hcard_eq]
    exact hsum_lower

-- Analytic detector bridge (explicit assumption):
-- The phase-2 theorem below is a combinatorial extraction layer.  Any further
-- Maynard–Pratt-style conclusion still requires an explicit mean/large-value input
-- as an additional assumption; that requirement is expressed here for future
-- refinement without hiding it behind a typeclass placeholder.
def RequiredMaynardPrattHypothesis (T β δ : ℝ) : Prop :=
  ∀ y : ℝ,
    0 < y →
    ‖zeroPackageUncontrolledRemainder y T β + zeroPackageClosedTerms y‖ ≤ |y| + δ

theorem maynardPratt_detector_as_explicit_assumption
    (T β δ : ℝ) (hδ : 0 < δ) (hmp : RequiredMaynardPrattHypothesis T β δ) :
    True := by
  exact True.intro

end HalfIsolatedZeroDichotomy
end PrimeNumberTheorem
