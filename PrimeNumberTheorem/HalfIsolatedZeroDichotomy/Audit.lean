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

end HalfIsolatedZeroDichotomy
end PrimeNumberTheorem
