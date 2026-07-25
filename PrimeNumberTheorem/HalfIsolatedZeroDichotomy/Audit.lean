import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.Contract
import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound
import PrimeNumberTheorem.ExplicitFormulaTruncated
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
      _ ≤ |ρ₁.im - x.im| + |x.im - ρ₂.im| := by
        simpa using abs_add_le (ρ₁.im - x.im) (x.im - ρ₂.im)
  have hle : |ρ₁.im - ρ₂.im| ≤ 2 * δ := by
    have hsum : |ρ₁.im - x.im| + |x.im - ρ₂.im| ≤ 2 * δ := by
      have hdist₁' : |ρ₁.im - x.im| ≤ δ := by simpa [abs_sub_comm] using hdist₁
      calc
        |ρ₁.im - x.im| + |x.im - ρ₂.im| ≤ δ + δ := add_le_add hdist₁' hdist₂
        _ ≤ 2 * δ := by nlinarith
    exact le_trans himageq hsum
  exact (not_lt_of_ge hle) hsep

/-- Pairwise disjointness of windows under pairwise `2δ` separation. -/
theorem topLayerWindow_pairwise_disjoint_of_centers
    (T β δ : ℝ) (hδ : 0 < δ) (centers : Finset ℂ)
    (hsep : ∀ ρ₁ ∈ centers, ∀ ρ₂ ∈ centers, ρ₁ ≠ ρ₂ →
      Disjoint (TopLayerWindow T β δ ρ₁) (TopLayerWindow T β δ ρ₂)) :
    ((↑centers : Set ℂ)).PairwiseDisjoint (fun ρ => TopLayerWindow T β δ ρ) := by
  refine (Finset.pairwiseDisjoint_iff).2 ?_
  intro ρ₁ hρ₁ ρ₂ hρ₂ hinter
  have hρ₁' : ρ₁ ∈ centers := by simpa using hρ₁
  have hρ₂' : ρ₂ ∈ centers := by simpa using hρ₂
  by_contra hρ₁ne
  exact (Finset.not_disjoint_iff_nonempty_inter.mpr hinter) <|
    hsep ρ₁ hρ₁' ρ₂ hρ₂' hρ₁ne

/-- Sum of window-cardinalities is controlled by top-layer cardinality whenever
windows are pairwise disjoint. -/
theorem sum_topLayerWindow_card_le_topLayer_of_disjoint
    (T β δ : ℝ) (centers : Finset ℂ)
    (hdisj : ((↑centers : Set ℂ)).PairwiseDisjoint (fun ρ => TopLayerWindow T β δ ρ)) :
    centers.sum (fun ρ => (TopLayerWindow T β δ ρ).card) ≤
      (TopLayerFinset T β).card := by
  have hcard_eq :
      (Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ)).card =
        centers.sum (fun ρ => (TopLayerWindow T β δ ρ).card) := by
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
    (hdisj : ((↑centers : Set ℂ)).PairwiseDisjoint (fun ρ => TopLayerWindow T β δ ρ))
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
      (Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ)).card =
        centers.sum (fun ρ => (TopLayerWindow T β δ ρ).card) := by
    simpa using Finset.card_biUnion hdisj
  have hsum_lower : 2 * centers.card ≤ centers.sum (fun ρ => (TopLayerWindow T β δ ρ).card) := by
    have hsum_lower_aux : centers.card * 2 ≤ centers.sum (fun ρ => (TopLayerWindow T β δ ρ).card) := by
      calc
        centers.card * 2 = centers.sum (fun ρ => (2 : ℕ)) := by simp
        _ ≤ centers.sum (fun ρ => (TopLayerWindow T β δ ρ).card) :=
          Finset.sum_le_sum (fun ρ hρ => htwo ρ hρ)
    simpa [Nat.mul_comm] using hsum_lower_aux
  refine ⟨zset, ?_, ?_⟩
  · simpa [zset] using hsubset
  · have hz : 2 * centers.card ≤ (Finset.biUnion centers (fun ρ => TopLayerWindow T β δ ρ)).card := by
      exact by simpa [hcard_eq] using hsum_lower
    simpa [zset] using hz

/-- Exact oscillation-input shape required for a pointwise detector bound.
This keeps the analytic gap explicit and shows exactly which additional term is
not controlled by the current repository APIs.
-/
def HalfIsolatedSimplifiedDetectorInput (T : ℝ) : Prop :=
  4 ≤ T →
    ∀ y : ℝ, 0 < y →
      ∃ C : ℝ, 0 ≤ C ∧
        ‖zeroPackageUncontrolledRemainder y T (maximalZeroRealPart T)‖ ≤
          Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
            (C * (1 + Real.log (T + 6)) ^ 2) +
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖

/-- Current inputs give exactly the uncontrolled-remainder estimate above, with an
explicitly stated `y`-dependent constant `C`.

The closed-form term remains present; the missing step for a detector-style
smallness principle is an independent pointwise bound on the finite-height
approximation error.
-/
theorem halfIsolatedSimplifiedDetectorInput_available
    (T : ℝ) (hT : 4 ≤ T) : HalfIsolatedSimplifiedDetectorInput T := by
  intro hT' y hy
  have hy0 : 0 ≤ y := le_of_lt hy
  rcases
      exists_norm_complementaryZeroPackageContribution_le_exp_maximal_gap_mul_log_sq
        (y := y) hy0 with
    ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  have hcomplement :
      ‖complementaryZeroPackageContribution (Real.exp y) T (maximalZeroRealPart T)‖ ≤
        Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
          (C * (1 + Real.log (T + 6)) ^ 2) := by
    exact hCbound T hT
  have huncontrolled :=
    norm_zeroPackageUncontrolledRemainder_le_complementary_add_approximation y T
  have hsum : ‖complementaryZeroPackageContribution (Real.exp y) T (maximalZeroRealPart T)‖ +
      ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
        (chebyshevPsi0 (Real.exp y) : ℂ)‖
      ≤
      Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
        (C * (1 + Real.log (T + 6)) ^ 2) +
      ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
        (chebyshevPsi0 (Real.exp y) : ℂ)‖ := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hcomplement ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
        (chebyshevPsi0 (Real.exp y) : ℂ)‖
  exact le_trans huncontrolled hsum

 /-- Target detector form without explicit approximation split: zeroPackage error is
bounded only by the complementary-layer exponential envelope. -/
def HalfIsolatedPureSimplifiedDetectorInput (T : ℝ) : Prop :=
  4 ≤ T →
    ∀ y : ℝ, 0 < y →
      ∃ C : ℝ, 0 ≤ C ∧
        ‖zeroPackageUncontrolledRemainder y T (maximalZeroRealPart T)‖ ≤
          Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
            (C * (1 + Real.log (T + 6)) ^ 2)

/-- Exact missing analytic input that would remove the additive approximation term
from `HalfIsolatedSimplifiedDetectorInput`. -/
def HalfIsolatedResidualControlForDetector (T : ℝ) : Prop :=
  4 ≤ T →
    ∀ y : ℝ, 0 < y →
      ∃ C : ℝ, 0 ≤ C ∧
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
          Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
            (C * (1 + Real.log (T + 6)) ^ 2)

/-- The missing residual control is explicitly instantiated from existing
quantitative explicit-formula inputs at all truncation heights.

For `8 ≤ T`, we use the established all-heights estimate with an explicit
coefficient that absorbs `1 / T` into the detector residual scale.
For `T ≤ 8`, we use the compact-height constant and absorb the finite-size
factor into `C` directly.
-/
theorem halfIsolatedResidualControlForDetector_available
    (T : ℝ) (hT : 4 ≤ T) : HalfIsolatedResidualControlForDetector T := by
  intro _hT y hy
  have hTy : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
  let B : ℝ := (1 + Real.log (T + 6)) ^ 2
  have hTpos : 0 < T := by linarith
  have hB_pos : 0 < B := by
    dsimp [B]
    have hlog : 0 < Real.log (T + 6) := by
      exact Real.log_pos (by linarith)
    have hsum : 0 < 1 + Real.log (T + 6) := by linarith
    nlinarith [sq_pos_of_pos hsum]
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  by_cases hT8 : 8 ≤ T
  · rcases
      ExplicitFormulaResidues.exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div
        hTy with
    ⟨C₀, hC₀_nonneg, hC₀⟩
    let C : ℝ :=
      C₀ * (1 + Real.log (T + 8)) ^ 2 /
        (T * Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) * B)
    refine ⟨C, ?_, ?_⟩
    · dsimp [C]
      positivity
    · have hmain :
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
          C₀ * (1 + Real.log (T + 8)) ^ 2 / T := hC₀ T hT8
      have hrewrite :
          C₀ * (1 + Real.log (T + 8)) ^ 2 / T =
            Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
              (C * (1 + Real.log (T + 6)) ^ 2) := by
        dsimp [C]
        field_simp [hTpos.ne', hB_ne, Real.exp_ne_zero _]
        ring
      calc
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
            C₀ * (1 + Real.log (T + 8)) ^ 2 / T := hmain
        _ = Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
              (C * (1 + Real.log (T + 6)) ^ 2) := hrewrite
  · have hTle : T ≤ 8 := le_of_not_ge hT8
    rcases
      ExplicitFormulaTruncated.exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_of_le_eight
        (Real.exp y) with ⟨K, hK_nonneg, hK⟩
    let C : ℝ := K / (Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) * B)
    refine ⟨C, ?_, ?_⟩
    · dsimp [C]
      positivity
    · have hmain : ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤ K :=
        hK T hTle
      have hrewrite :
          K =
            Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
              (C * (1 + Real.log (T + 6)) ^ 2) := by
        dsimp [C]
        field_simp [hB_ne, Real.exp_ne_zero _]
        ring
      calc
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤ K := hmain
        _ = Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
              (C * (1 + Real.log (T + 6)) ^ 2) := hrewrite

/-- If the exact residual control is supplied, we can instantiate a pure
one-term detector. This isolates the missing inequality statement to a precise
place in the chain. -/
theorem halfIsolatedPureSimplifiedDetectorInput_of_residualControl
    (T : ℝ) (hT : 4 ≤ T)
    (hres : HalfIsolatedResidualControlForDetector T) :
    HalfIsolatedPureSimplifiedDetectorInput T := by
  intro hT' y hy
  rcases
      exists_norm_complementaryZeroPackageContribution_le_exp_maximal_gap_mul_log_sq
        (y := y) (by exact le_of_lt hy) with
    ⟨C₁, hC₁_nonneg, hC₁⟩
  rcases hres hT y hy with
    ⟨C₂, hC₂_nonneg, hC₂⟩
  have hcomp :
      ‖zeroPackageUncontrolledRemainder y T (maximalZeroRealPart T)‖ ≤
        ‖complementaryZeroPackageContribution (Real.exp y) T (maximalZeroRealPart T)‖ +
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ :=
    norm_zeroPackageUncontrolledRemainder_le_complementary_add_approximation y T
  have htail :
      ‖complementaryZeroPackageContribution (Real.exp y) T (maximalZeroRealPart T)‖ ≤
        Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
          (C₁ * (1 + Real.log (T + 6)) ^ 2) := by
    exact hC₁ T hT
  have hresbound :
      ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
        Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
          (C₂ * (1 + Real.log (T + 6)) ^ 2) := hC₂
  refine ⟨C₁ + C₂, add_nonneg hC₁_nonneg hC₂_nonneg, ?_⟩
  calc
    ‖zeroPackageUncontrolledRemainder y T (maximalZeroRealPart T)‖ ≤
        ‖complementaryZeroPackageContribution (Real.exp y) T (maximalZeroRealPart T)‖ +
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ := hcomp
    _ ≤ Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
          (C₁ * (1 + Real.log (T + 6)) ^ 2) +
        Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
          (C₂ * (1 + Real.log (T + 6)) ^ 2) := add_le_add htail hresbound
    _ = Real.exp ((maximalZeroRealPart T - maximalComplementaryRealPartGap T) * y) *
          ((C₁ + C₂) * (1 + Real.log (T + 6)) ^ 2) := by
      ring

/-- Directly instantiate the pure detector input needed by downstream usage. -/
theorem halfIsolatedPureSimplifiedDetectorInput_available
    (T : ℝ) (hT : 4 ≤ T) :
    HalfIsolatedPureSimplifiedDetectorInput T :=
  halfIsolatedPureSimplifiedDetectorInput_of_residualControl T hT
    (halfIsolatedResidualControlForDetector_available T hT)

/-- The currently defined top-layer dichotomy matches the expected zero-density
`HasHalfIsolatedDichotomy` shape; no extra adapter class or wrapper is needed. -/
theorem halfIsolatedDichotomy_zeroDensityAdapter
    {T β δ : ℝ} {ρ : ℂ} :
    HasHalfIsolatedDichotomy T β δ ρ ↔
      IsTopLayerZero T β ρ ∧
        (IsHalfIsolatedZero T β δ ρ ∨ IsInQuantitativeLocalCluster T β δ ρ) := by
  rfl

/-- Endpoint bridge from top-layer objects to usable detector bound and cluster
certificate. With `hseparation`, non-isolated centers have disjoint windows,
so extracted windows cannot be double-counted.

For non-isolated inputs, this returns an explicit finite multiseed certificate of
many distinct top-layer zeros.
-/
theorem halfIsolatedDetectorClusterEndpoint
    (T β δ : ℝ) (hT : 4 ≤ T) (hδ : 0 < δ)
    (centers : Finset ℂ)
    (hcenters : centers ⊆ TopLayerFinset T β)
    (hseparation :
      ∀ ρ₁ ∈ centers, ∀ ρ₂ ∈ centers, ρ₁ ≠ ρ₂ →
        2 * δ < |ρ₁.im - ρ₂.im|) :
    HalfIsolatedPureSimplifiedDetectorInput T ∧
      (∀ ρ ∈ centers, IsTopLayerZero T β ρ →
        IsHalfIsolatedZero T β δ ρ ∨ IsInQuantitativeLocalCluster T β δ ρ) ∧
      (∀ hnonIso : ∀ ρ ∈ centers, IsTopLayerZero T β ρ →
        ¬ IsHalfIsolatedZero T β δ ρ,
        (∀ ρ ∈ centers, IsTopLayerZero T β ρ →
          IsInQuantitativeLocalCluster T β δ ρ) ∧
        ∃ zset : Finset ℂ,
          zset ⊆ TopLayerFinset T β ∧
          2 * centers.card ≤ zset.card) := by
  let hdet : HalfIsolatedPureSimplifiedDetectorInput T :=
    halfIsolatedPureSimplifiedDetectorInput_available T hT
  have hdisj :
      ((↑centers : Set ℂ)).PairwiseDisjoint (fun ρ => TopLayerWindow T β δ ρ) := by
    exact topLayerWindow_pairwise_disjoint_of_centers T β δ hδ centers
      (fun ρ₁ hρ₁ ρ₂ hρ₂ hρ₁ne =>
        topLayerWindow_disjoint_of_imag_separation T β δ hδ hρ₁ne
          (hseparation ρ₁ hρ₁ ρ₂ hρ₂ hρ₁ne))
  refine ⟨hdet, ?_, ?_⟩
  · intro ρ hρ htop
    exact topLayer_dichotomy_local_window T β δ (hcenters hρ) hδ
  · intro hnonIso
    have hcluster : ∀ ρ ∈ centers, IsTopLayerZero T β ρ →
        IsInQuantitativeLocalCluster T β δ ρ := by
      intro ρ hρ htop
      have hdich : IsHalfIsolatedZero T β δ ρ ∨ IsInQuantitativeLocalCluster T β δ ρ :=
        topLayer_dichotomy_local_window T β δ htop hδ
      rcases hdich with hhalf | hcls
      · exact (hnonIso ρ hρ htop hhalf).elim
      · exact hcls
    have htwo : ∀ ρ ∈ centers, 2 ≤ (TopLayerWindow T β δ ρ).card := by
      intro ρ hρ
      have htop : IsTopLayerZero T β ρ := hcenters hρ
      have hnotSep : ¬ ∀ z' : ℂ,
          z' ∈ TopLayerFinset T β → z' ≠ ρ → δ ≤ |z'.im - ρ.im| := by
        intro hsep
        exact hnonIso ρ hρ htop ⟨htop, hδ, hsep⟩
      rcases not_forall.mp hnotSep with ⟨z', hnotImp⟩
      have hzmem : z' ∈ TopLayerFinset T β := by
        by_contra hznot
        exact hnotImp (fun _hz _hneq => (False.elim (hznot _hz)))
      have hnotImp' : ¬ (z' ≠ ρ → δ ≤ |z'.im - ρ.im|) := by
        intro hzImp
        exact hnotImp (fun _hz => hzImp)
      rcases Classical.not_imp.mp hnotImp' with ⟨hz'ne, hz'ltδ⟩
      have hzwindow : ρ ∈ TopLayerWindow T β δ ρ :=
        topLayerWindow_center_mem T β δ htop hδ
      have hz'window : z' ∈ TopLayerWindow T β δ ρ := by
        exact Finset.mem_filter.mpr ⟨hzmem, le_of_lt (lt_of_not_ge hz'ltδ)⟩
      have hpair_subset : ({ρ, z'} : Finset ℂ) ⊆ TopLayerWindow T β δ ρ := by
        intro x hx
        rcases Finset.mem_insert.mp hx with hx | hx
        · simpa [hx] using hzwindow
        · have hx' : x = z' := by simpa using Finset.mem_singleton.mp hx
          simpa [hx'] using hz'window
      have hpair_card : ({ρ, z'} : Finset ℂ).card = 2 := by
        by_cases hρz' : ρ = z'
        · exact (hz'ne hρz'.symm).elim
        · exact Finset.card_pair hρz'
      have hpair_card_le : ({ρ, z'} : Finset ℂ).card ≤ (TopLayerWindow T β δ ρ).card :=
        Finset.card_le_card hpair_subset
      simpa [hpair_card] using hpair_card_le
    rcases extract_many_distinct_zeros_from_disjoint_windows T β δ hδ centers hdisj htwo with
      ⟨zset, hsubset, hcard⟩
    exact ⟨hcluster, ⟨zset, hsubset, hcard⟩⟩

noncomputable def halfIsolatedClusterNext
    (T β : ℝ) (gapRadius : ℂ → ℝ) (ρ : ℂ) : Finset ℂ :=
  TopLayerWindow T β (gapRadius ρ) ρ

/-- Zero-level adjacency produced by a radius assignment `gapRadius`. -/
noncomputable def halfIsolatedClusterIteration
    (T β : ℝ) (gapRadius : ℂ → ℝ) : ℕ → Finset ℂ → Finset ℂ
  | 0, centers => centers
  | n+1, centers =>
      (halfIsolatedClusterIteration T β gapRadius n centers).biUnion
        (halfIsolatedClusterNext T β gapRadius)

 /-- Iteration for a generic zero-adjacency relation. -/
noncomputable def halfIsolatedClusterIterationOfNeighbor
    (neighbor : ℂ → Finset ℂ) : ℕ → Finset ℂ → Finset ℂ
  | 0, centers => centers
  | n+1, centers => (halfIsolatedClusterIterationOfNeighbor neighbor n centers).biUnion
      neighbor

lemma halfIsolatedClusterIteration_step_lower
    (T β : ℝ) (gapRadius : ℂ → ℝ) (centers : Finset ℂ)
    (q : ℕ)
  (hq : 1 ≤ q)
  (hdisj :
      ((↑centers : Set ℂ)).PairwiseDisjoint (halfIsolatedClusterNext T β gapRadius))
  (htwo : ∀ ρ ∈ centers, q ≤ (halfIsolatedClusterNext T β gapRadius ρ).card) :
  q * centers.card ≤
    (halfIsolatedClusterIteration T β gapRadius 1 centers).card := by
  have hcard_eq :
      (centers.biUnion (halfIsolatedClusterNext T β gapRadius)).card =
        centers.sum (fun ρ => (halfIsolatedClusterNext T β gapRadius ρ).card) := by
    simpa using (Finset.card_biUnion hdisj)
  have hsum_lower_aux : centers.card * q ≤ centers.sum (fun ρ =>
      (halfIsolatedClusterNext T β gapRadius ρ).card) := by
    calc
      centers.card * q = centers.sum (fun _ : ℂ => q) := by simp
      _ ≤ centers.sum (fun ρ => (halfIsolatedClusterNext T β gapRadius ρ).card) :=
        Finset.sum_le_sum (fun ρ hρ => htwo ρ hρ)
  have hsum_lower : q * centers.card ≤
      (centers.biUnion (halfIsolatedClusterNext T β gapRadius)).card := by
    have hsum_lower' : q * centers.card ≤ centers.sum (fun ρ =>
        (halfIsolatedClusterNext T β gapRadius ρ).card) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum_lower_aux
    simpa [hcard_eq] using hsum_lower'
  simpa [halfIsolatedClusterIteration] using hsum_lower

/-- If each iteration level has `q`-ary branching and level-wise disjoint windows,
the `n`-th frontier has at least `q^n` times the root count. -/
theorem halfIsolatedClusterIteration_exponential
    (T β : ℝ) (gapRadius : ℂ → ℝ) (centers : Finset ℂ)
    (q : ℕ)
    (hq : 1 ≤ q)
    (hdisj :
      ∀ n : ℕ,
        ((↑(halfIsolatedClusterIteration T β gapRadius n centers) : Set ℂ)).PairwiseDisjoint
          (halfIsolatedClusterNext T β gapRadius))
    (htwo :
      ∀ n ρ,
        ρ ∈ halfIsolatedClusterIteration T β gapRadius n centers →
          q ≤ (halfIsolatedClusterNext T β gapRadius ρ).card) :
    ∀ n : ℕ,
      q ^ n * centers.card ≤ (halfIsolatedClusterIteration T β gapRadius n centers).card := by
  intro n
  induction n with
  | zero =>
      simpa [halfIsolatedClusterIteration]
  | succ n ih =>
      have hdisj_succ := hdisj n
      have htwo_succ :
          ∀ ρ ∈ halfIsolatedClusterIteration T β gapRadius n centers,
            q ≤ (halfIsolatedClusterNext T β gapRadius ρ).card :=
        htwo n
      have hstep :
          q * (halfIsolatedClusterIteration T β gapRadius n centers).card ≤
            (halfIsolatedClusterIteration T β gapRadius (n + 1) centers).card := by
        simpa [halfIsolatedClusterIteration] using
          (halfIsolatedClusterIteration_step_lower T β gapRadius
            (halfIsolatedClusterIteration T β gapRadius n centers) q
            hq hdisj_succ htwo_succ)
      have hmul : q ^ (n + 1) * centers.card = q * (q ^ n * centers.card) := by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      calc
        q ^ (n + 1) * centers.card = q * (q ^ n * centers.card) := hmul
        _ ≤ q * (halfIsolatedClusterIteration T β gapRadius n centers).card :=
          Nat.mul_le_mul_left _ ih
        _ ≤ (halfIsolatedClusterIteration T β gapRadius (n + 1) centers).card := hstep

/-- A strict finite two-vertex counterexample: each vertex has two neighbors,
but two-step expansion does not double the frontier size. This isolates missing
`no-revisit/no-layer-overlap` hypotheses for a true replicate argument. -/
noncomputable def halfIsolatedLoopNeighbor (a b : ℂ) : ℂ → Finset ℂ :=
  fun z => if z = a then ({a, b} : Finset ℂ) else if z = b then ({a, b} : Finset ℂ) else ∅

noncomputable def halfIsolatedLoopCenters (a b : ℂ) : Finset ℂ := ({a, b} : Finset ℂ)

noncomputable def halfIsolatedLoopIteration (a b : ℂ) : ℕ → Finset ℂ :=
  fun n => halfIsolatedClusterIterationOfNeighbor (halfIsolatedLoopNeighbor a b) n (halfIsolatedLoopCenters a b)

theorem halfIsolatedLoopIteration_counterexample
    (a b : ℂ) (hab : a ≠ b) :
    ¬ (4 ≤ (halfIsolatedLoopIteration a b 2).card) ∧
    ∀ z ∈ halfIsolatedLoopCenters a b, 2 ≤ (halfIsolatedLoopNeighbor a b z).card := by
  have hloop_ne : halfIsolatedLoopIteration a b 2 = ({a, b} : Finset ℂ) := by
    simp [halfIsolatedLoopIteration, halfIsolatedClusterIterationOfNeighbor,
      halfIsolatedLoopNeighbor, halfIsolatedLoopCenters, hab]
  have hpair_card : ({a, b} : Finset ℂ).card = 2 := by
    simpa [Finset.card_pair, hab]
  refine ⟨?_, ?_⟩
  · intro h
    exact (show ¬ (4 : ℕ) ≤ 2 from by decide) (by simpa [hloop_ne, hpair_card] using h)
  · intro z hz
    have hz' : z = a ∨ z = b := by
      simpa [halfIsolatedLoopCenters, hab, Finset.mem_insert, Finset.mem_singleton] using hz
    rcases hz' with rfl | rfl
    · simp [halfIsolatedLoopNeighbor, hab]
    · simp [halfIsolatedLoopNeighbor, hab]

/-- Directed (imaginary-increasing) neighbors on a fixed top layer. -/
noncomputable def halfIsolatedDirectedNext
    (T β : ℝ) (δ : ℝ) (ρ : ℂ) : Finset ℂ :=
  (TopLayerWindow T β δ ρ).filter (fun σ => ρ.im < σ.im)

/-- Directed iteration using only strictly higher imaginary parts. -/
noncomputable def halfIsolatedDirectedIteration
    (T β : ℝ) (δ : ℝ) : ℕ → Finset ℂ → Finset ℂ
  | 0, centers => centers
  | n+1, centers => (halfIsolatedDirectedIteration T β δ n centers).biUnion
      (halfIsolatedDirectedNext T β δ)

lemma halfIsolatedDirectedIteration_step_lower
    (T β : ℝ) (δ : ℝ) (centers : Finset ℂ)
    (q : ℕ) (hq : 1 ≤ q)
    (hdisj :
      ((↑centers : Set ℂ)).PairwiseDisjoint (halfIsolatedDirectedNext T β δ))
    (htwo : ∀ ρ ∈ centers, q ≤ (halfIsolatedDirectedNext T β δ ρ).card) :
    q * centers.card ≤
      (halfIsolatedDirectedIteration T β δ 1 centers).card := by
  have hcard_eq :
      (centers.biUnion (halfIsolatedDirectedNext T β δ)).card =
        centers.sum (fun ρ => (halfIsolatedDirectedNext T β δ ρ).card) := by
    simpa using (Finset.card_biUnion hdisj)
  have hsum_lower_aux : centers.card * q ≤ centers.sum (fun ρ =>
      (halfIsolatedDirectedNext T β δ ρ).card) := by
    calc
      centers.card * q = centers.sum (fun _ : ℂ => q) := by simp
      _ ≤ centers.sum (fun ρ => (halfIsolatedDirectedNext T β δ ρ).card) :=
        Finset.sum_le_sum (fun ρ hρ => htwo ρ hρ)
  have hsum_lower : q * centers.card ≤
      (centers.biUnion (halfIsolatedDirectedNext T β δ)).card := by
    have hsum_lower' : q * centers.card ≤ centers.sum (fun ρ =>
        (halfIsolatedDirectedNext T β δ ρ).card) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum_lower_aux
    simpa [hcard_eq] using hsum_lower'
  simpa [halfIsolatedDirectedIteration] using hsum_lower

theorem halfIsolatedDirectedIteration_exponential
    (T β : ℝ) (δ : ℝ) (centers : Finset ℂ)
    (q : ℕ)
    (hq : 1 ≤ q)
    (hdisj :
      ∀ n : ℕ,
        ((↑(halfIsolatedDirectedIteration T β δ n centers) : Set ℂ)).PairwiseDisjoint
          (halfIsolatedDirectedNext T β δ))
    (htwo :
      ∀ n ρ,
        ρ ∈ halfIsolatedDirectedIteration T β δ n centers →
          q ≤ (halfIsolatedDirectedNext T β δ ρ).card) :
    ∀ n : ℕ,
      q ^ n * centers.card ≤ (halfIsolatedDirectedIteration T β δ n centers).card := by
  intro n
  induction n with
  | zero =>
      simpa [halfIsolatedDirectedIteration]
  | succ n ih =>
      have hdisj_succ := hdisj n
      have htwo_succ :
          ∀ ρ ∈ halfIsolatedDirectedIteration T β δ n centers,
            q ≤ (halfIsolatedDirectedNext T β δ ρ).card :=
        htwo n
      have hstep :
          q * (halfIsolatedDirectedIteration T β δ n centers).card ≤
            (halfIsolatedDirectedIteration T β δ (n + 1) centers).card := by
        simpa [halfIsolatedDirectedIteration] using
          (halfIsolatedDirectedIteration_step_lower T β δ
            (halfIsolatedDirectedIteration T β δ n centers) q
            hq hdisj_succ htwo_succ)
      have hmul : q ^ (n + 1) * centers.card = q * (q ^ n * centers.card) := by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      calc
        q ^ (n + 1) * centers.card = q * (q ^ n * centers.card) := hmul
        _ ≤ q * (halfIsolatedDirectedIteration T β δ n centers).card :=
          Nat.mul_le_mul_left _ ih
        _ ≤ (halfIsolatedDirectedIteration T β δ (n + 1) centers).card := hstep

/-- A one-step advancing lemma: under a strict-direction witness and detector
cluster hypothesis, one can extract a higher-imag zero from the same window. -/
theorem halfIsolatedOneStepAdvanceFromEndpoint
    (T β δ : ℝ) (ρ : ℂ) (hδ : 0 < δ)
    (hTop : IsTopLayerZero T β ρ)
    (hcluster : IsInQuantitativeLocalCluster T β δ ρ)
    (hdistinct : ∃ σ, σ ∈ TopLayerWindow T β δ ρ ∧ ρ.im ≠ σ.im)
    (hdrift :
      ∀ σ ∈ TopLayerWindow T β δ ρ, σ.im ≠ ρ.im → ρ.im < σ.im) :
    ∃ σ, σ ∈ halfIsolatedDirectedNext T β δ ρ := by
  rcases hdistinct with ⟨σ, hσ, hσne⟩
  exact ⟨σ, Finset.mem_filter.mpr ⟨hσ, hdrift σ hσ (by simpa [ne_comm] using hσne)⟩⟩

/-- A strict-cycle counterexample under current endpoint-style hypotheses:
if the top layer is exactly two equal-imag zeros, directed ascent is blocked and
the first directed step is empty (hence no q-ary growth with q ≥ 1). -/
theorem halfIsolatedDirectedIteration_stall_under_equal_im_topLayer
    (T β : ℝ) (a b : ℂ) (hδ : 0 < δ) (hab : a ≠ b)
    (hTopOnly : TopLayerFinset T β = ({a, b} : Finset ℂ))
    (hEq : a.im = b.im) :
    let centers : Finset ℂ := ({a, b} : Finset ℂ)
    ((∀ ρ ∈ centers, IsTopLayerZero T β ρ → IsInQuantitativeLocalCluster T β δ ρ) ∧
      (halfIsolatedDirectedIteration T β δ 1 centers = ∅) ) := by
  let centers : Finset ℂ := ({a, b} : Finset ℂ)
  have hNoHalf : ∀ ρ ∈ centers, IsTopLayerZero T β ρ →
      ¬ IsHalfIsolatedZero T β δ ρ := by
    intro ρ hρ htop hhalf
    have hρeq : ρ = a ∨ ρ = b := by
      simpa [centers, Finset.mem_insert, Finset.mem_singleton] using hρ
    have habs : |b.im - a.im| = 0 := by
      simpa [hEq]
    have hδ_lt : ¬ δ ≤ |b.im - a.im| := by
      simpa [habs] using (not_le_of_gt hδ)
    rcases hρeq with hρeq | hρeq
    · subst ρ
      have hb : b ∈ TopLayerFinset T β := by
        simpa [hTopOnly] using (show b ∈ ({a, b} : Finset ℂ) by simp)
      exact hδ_lt (hhalf.2.2 b hb (by simpa [eq_comm] using hab))
    · subst ρ
      have ha : a ∈ TopLayerFinset T β := by
        simpa [hTopOnly] using (show a ∈ ({a, b} : Finset ℂ) by simp)
      have hδ_lt' : ¬ δ ≤ |a.im - b.im| := by
        simpa [hEq] using (not_le_of_gt hδ)
      exact hδ_lt' (hhalf.2.2 a ha (by simpa using hab))
  have hcluster : ∀ ρ ∈ centers, IsTopLayerZero T β ρ →
      IsInQuantitativeLocalCluster T β δ ρ := by
    intro ρ hρ htop
    exact (topLayer_dichotomy_local_window T β δ htop hδ).resolve_left (hNoHalf ρ hρ htop)
  have hnext_eq_empty : ∀ ρ ∈ centers, halfIsolatedDirectedNext T β δ ρ = (∅ : Finset ℂ) := by
    intro ρ hρ
    have hρeq : ρ = a ∨ ρ = b := by
      simpa [centers, Finset.mem_insert, Finset.mem_singleton] using hρ
    have hρim : ρ.im = a.im := by
      rcases hρeq with hρeq | hρeq
      · simpa [hρeq]
      · simpa [hρeq, hEq]
    ext z
    constructor
    · intro hz
      rcases Finset.mem_filter.mp hz with ⟨hzwin, hlt⟩
      have hztop : z ∈ TopLayerFinset T β := (Finset.mem_filter.mp hzwin).1
      have hzmem : z = a ∨ z = b := by
        simpa [hTopOnly, Finset.mem_insert, Finset.mem_singleton] using hztop
      have hzim : z.im = a.im := by
        rcases hzmem with hzmem | hzmem
        · simpa [hzmem]
        · simpa [hzmem, hEq]
      have : ¬ ρ.im < z.im := by simpa [hρim, hzim]
      exact (this hlt).elim
    · intro hz
      cases hz
  refine ⟨?_, ?_⟩
  · exact hcluster
  · have hUnion : centers.biUnion (halfIsolatedDirectedNext T β δ) = (∅ : Finset ℂ) := by
      ext z
      constructor
      · intro hz
        rcases Finset.mem_biUnion.mp hz with ⟨ρ, hρ, hρz⟩
        have hzero : halfIsolatedDirectedNext T β δ ρ = (∅ : Finset ℂ) := hnext_eq_empty ρ hρ
        simpa [hzero] using hρz
      · intro hz
        cases hz
    change centers.biUnion (halfIsolatedDirectedNext T β δ) = (∅ : Finset ℂ)
    exact hUnion

end HalfIsolatedZeroDichotomy
end PrimeNumberTheorem
