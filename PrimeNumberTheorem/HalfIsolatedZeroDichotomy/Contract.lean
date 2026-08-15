import ZeroFreeRegion.MeromorphicAux
import PrimeNumberTheorem.NontrivialZeroMultiplicity
import PrimeNumberTheorem.ExplicitFormulaAux
import PrimeNumberTheorem.ExplicitFormulaAllHeights
import PrimeNumberTheorem.LocalSeparationKernel
import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace HalfIsolatedZeroDichotomy

open RiemannHypothesis
open PrimeNumberTheorem.ZeroForcedOscillation
noncomputable section

/-- Top layer as a concrete finite zero multiset (height truncation `T`, real part `β`).
This is definitionally the `equalRealPartZeroPackage` used in the explicit-formula
machinery. -/
def TopLayerFinset (T β : ℝ) : Finset ℂ :=
  equalRealPartZeroPackage T β

/-- Membership in the top layer finite set. -/
def IsTopLayerZero (T β : ℝ) (ρ : ℂ) : Prop :=
  ρ ∈ TopLayerFinset T β

/-- Window on the top layer around a zero in the imaginary direction. -/
def TopLayerWindow (T β δ : ℝ) (ρ : ℂ) : Finset ℂ :=
  (TopLayerFinset T β).filter (fun ρ' : ℂ => |ρ'.im - ρ.im| ≤ δ)

/-- C (combinatorial identity-level definition): right-layer separation
within a fixed strip and real part β. -/
def IsHalfIsolatedZero (T β : ℝ) (δ : ℝ) (ρ : ℂ) : Prop :=
  IsTopLayerZero T β ρ ∧
  0 < δ ∧
  ∀ ρ' : ℂ,
    ρ' ∈ TopLayerFinset T β →
    ρ' ≠ ρ →
    δ ≤ |ρ'.im - ρ.im|

/-- Quantitative cluster object used by the iterative extraction theorem. -/
structure QuantitativeLocalCluster (T β δ : ℝ) where
  seed : ℂ
  gap_radius : ℝ
  gap_radius_pos : 0 < gap_radius
  seed_mem_window : seed ∈ TopLayerWindow T β gap_radius seed
  card_at_least_two : 2 ≤ (TopLayerWindow T β gap_radius seed).card
  separated_by_delta : δ ≤ gap_radius

/-- C (definition): seed belongs to a certified finite local cluster. -/
def IsInQuantitativeLocalCluster (T β δ : ℝ) (ρ : ℂ) : Prop :=
  ∃ c : QuantitativeLocalCluster T β δ, c.seed = ρ

/-- C (definition): rightmost zero dichotomy hypothesis at one zero. -/
def HasHalfIsolatedDichotomy (T β δ : ℝ) (ρ : ℂ) : Prop :=
  IsTopLayerZero T β ρ ∧
    (IsHalfIsolatedZero T β δ ρ ∨ IsInQuantitativeLocalCluster T β δ ρ)

/-- Direct bridge to Carlson/explicit-formula package. -/
theorem topLayerFinset_eq_equalRealPartPackage (T β : ℝ) :
    TopLayerFinset T β = equalRealPartZeroPackage T β := rfl

/-- Local characterization of `IsTopLayerZero` via the explicit nontrivial zeros. -/
theorem topLayer_mem_iff {T β : ℝ} {ρ : ℂ} :
    IsTopLayerZero T β ρ ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T ∧ ρ.re = β := by
  simp [IsTopLayerZero, TopLayerFinset, mem_equalRealPartZeroPackage, and_assoc]

/-- Every top-layer window is a sub-finset of the top layer. -/
theorem topLayerWindow_subset (T β δ : ℝ) (ρ : ℂ) :
    TopLayerWindow T β δ ρ ⊆ TopLayerFinset T β := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- A top-layer zero belongs to its own height window (for positive `δ`). -/
theorem topLayerWindow_center_mem (T β δ : ℝ) {ρ : ℂ} :
    IsTopLayerZero T β ρ → 0 < δ → ρ ∈ TopLayerWindow T β δ ρ := by
  intro hTop hδ
  refine Finset.mem_filter.mpr ?_
  constructor
  · exact hTop
  · have h0le : (0 : ℝ) ≤ δ := le_of_lt hδ
    simpa [sub_self] using h0le

/-- Every top-layer zero admits a local combinatorial dichotomy, no analytic
additional assumptions beyond membership in `TopLayerFinset`. -/
theorem topLayer_dichotomy_local_window (T β δ : ℝ) :
    ∀ {z : ℂ},
      IsTopLayerZero T β z →
      0 < δ →
      IsHalfIsolatedZero T β δ z ∨ IsInQuantitativeLocalCluster T β δ z := by
  intro z hz hzδ
  by_cases hsep : ∀ z' : ℂ, z' ∈ TopLayerFinset T β → z' ≠ z → δ ≤ |z'.im - z.im|
  · exact Or.inl ⟨hz, hzδ, hsep⟩
  · push_neg at hsep
    rcases hsep with ⟨z', hz', hzne, hlt⟩
    have hzwindow : z ∈ TopLayerWindow T β δ z := by
      exact topLayerWindow_center_mem T β δ hz hzδ
    have hz'window : z' ∈ TopLayerWindow T β δ z := by
      exact Finset.mem_filter.mpr ⟨hz', le_of_lt hlt⟩
    have hpair_subset : ({z, z'} : Finset ℂ) ⊆ TopLayerWindow T β δ z := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hzwindow
      · have hx' : x = z' := by simpa using Finset.mem_singleton.mp hx
        simpa [hx'] using hz'window
    have hpair_card : ({z, z'} : Finset ℂ).card = 2 := by
      by_cases hzz' : z = z'
      · exfalso
        exact hzne hzz'.symm
      · simp [Finset.card_pair, hzz']
    have htwo : 2 ≤ (TopLayerWindow T β δ z).card := by
      have hpair_card_le : ({z, z'} : Finset ℂ).card ≤ (TopLayerWindow T β δ z).card :=
        Finset.card_le_card hpair_subset
      simpa [hpair_card] using hpair_card_le
    let c : QuantitativeLocalCluster T β δ :=
      { seed := z
      , gap_radius := δ
      , gap_radius_pos := hzδ
      , seed_mem_window := hzwindow
      , card_at_least_two := htwo
      , separated_by_delta := le_rfl }
    exact Or.inr ⟨c, rfl⟩

/-- C: bridge statement packaged as a theorem (no typeclass placeholder). -/
theorem zero_isolated_or_cluster_of_top_layer {T β δ : ℝ} {ρ : ℂ}
    (hTop : IsTopLayerZero T β ρ) (hδ : 0 < δ) :
    HasHalfIsolatedDichotomy T β δ ρ := by
  exact ⟨hTop, topLayer_dichotomy_local_window T β δ hTop hδ⟩

end
end HalfIsolatedZeroDichotomy
end PrimeNumberTheorem
