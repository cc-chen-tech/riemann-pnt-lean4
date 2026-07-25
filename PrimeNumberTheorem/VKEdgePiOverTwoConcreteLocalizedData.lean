import PrimeNumberTheorem.VKEdgePiOverTwoFinitePoleContour
import PrimeNumberTheorem.VKEdgePiOverTwoLocalizedAssembly
import PrimeNumberTheorem.VKEdgePiOverTwoOtherEdgeDecay

open Complex Filter Polynomial Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The universal good-height constant supplied by the concrete zeta
horizontal-edge estimate. -/
def localizedContourGoodHeightConstant : ℝ :=
  Classical.choose
    exists_goodHeight_linearScale_localizedPsiGaussianAverage_eq_zeroSum

theorem localizedContourGoodHeightConstant_nonneg :
    0 ≤ localizedContourGoodHeightConstant :=
  (Classical.choose_spec
    exists_goodHeight_linearScale_localizedPsiGaussianAverage_eq_zeroSum).1

/-- One fully concrete finite-height zeta contour slice at Gaussian scale
`m`. -/
structure ConcreteLocalizedContourSlice
    (A : ℂ[X]) (u v m : ℝ) where
  height : ℝ
  height_mem :
    height ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1)
  goodHeight : ExplicitFormulaAux.goodHeight height
  zeros : Finset ℂ
  zeros_spec :
    ∀ rho ∈ zeros,
      riemannZeta rho = 0 ∧
        (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
        -height < rho.im ∧ rho.im < height
  zeros_complete :
    ∀ rho ∈
        ([[(-1 : ℝ), u + 2]] ×ℂ [[-height, height]] : Set ℂ),
      riemannZeta rho = 0 → rho ∈ zeros
  contour_eq :
    localizedPsiGaussianAverage A ((u : ℂ) + I * v) m =
      -(2 * Real.pi : ℂ) *
          localizedZeroResidueSum A
            ((u : ℂ) + I * v) m zeros +
        localizedContourRemainder A
          ((u : ℂ) + I * v) m u height
  remainder_bound :
    ‖localizedContourRemainder A
        ((u : ℂ) + I * v) m u height‖ ≤
      localizedOtherEdgeUpperBound A u v m
          localizedContourGoodHeightConstant
          (12 * m + |v|) height +
        ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
          Real.sqrt (Real.pi / (m / 2))

theorem exists_concreteLocalizedContourSlice
    (A : ℂ[X]) {u v m : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hm : 1 ≤ m)
    (hdegree : (A.natDegree : ℝ) ≤ m) :
    Nonempty (ConcreteLocalizedContourSlice A u v m) := by
  have hspec :=
    (Classical.choose_spec
      exists_goodHeight_linearScale_localizedPsiGaussianAverage_eq_zeroSum).2
  rcases hspec A u v m hu hu1 hm hdegree with
    ⟨T, hT, hgood, zeros, hzeros, hcomplete, heq, hbound⟩
  exact ⟨{
    height := T
    height_mem := hT
    goodHeight := hgood
    zeros := zeros
    zeros_spec := hzeros
    zeros_complete := hcomplete
    contour_eq := heq
    remainder_bound := hbound
  }⟩

/-- Scale validity needed to select a concrete contour slice. -/
def localizedContourScaleValid
    (A : ℂ[X]) (u m : ℝ) : Prop :=
  0 < u ∧ u < 1 ∧ 1 ≤ m ∧ (A.natDegree : ℝ) ≤ m

noncomputable def selectedConcreteLocalizedContourSlice
    (A : ℂ[X]) (u v m : ℝ)
    (hvalid : localizedContourScaleValid A u m) :
    ConcreteLocalizedContourSlice A u v m :=
  Classical.choice
    (exists_concreteLocalizedContourSlice A
      hvalid.1 hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2)

/-- The true-zeta contour remainder selected at every valid scale, extended
by zero before the fixed polynomial reaches its asymptotic regime. -/
noncomputable def selectedLocalizedContourRemainder
    (A : ℂ[X]) (u v m : ℝ) : ℂ := by
  classical
  exact
    if hvalid : localizedContourScaleValid A u m then
      localizedContourRemainder A ((u : ℂ) + I * v) m u
        (selectedConcreteLocalizedContourSlice A u v m hvalid).height
    else 0

/-- The multiplicity-weighted zero sum occurring in the same selected
concrete contour slice. -/
noncomputable def selectedLocalizedZeroResidueSum
    (A : ℂ[X]) (u v m : ℝ) : ℂ := by
  classical
  exact
    if hvalid : localizedContourScaleValid A u m then
      localizedZeroResidueSum A ((u : ℂ) + I * v) m
        (selectedConcreteLocalizedContourSlice A u v m hvalid).zeros
    else 0

/-- At every valid scale, the selected finite zero sum and selected
remainder satisfy the exact true-zeta Gaussian contour identity. -/
theorem selected_localizedPsiGaussianAverage_eq
    (A : ℂ[X]) {u v m : ℝ}
    (hvalid : localizedContourScaleValid A u m) :
    localizedPsiGaussianAverage A ((u : ℂ) + I * v) m =
      -(2 * Real.pi : ℂ) *
          selectedLocalizedZeroResidueSum A u v m +
        selectedLocalizedContourRemainder A u v m := by
  rw [selectedLocalizedZeroResidueSum, dif_pos hvalid]
  rw [selectedLocalizedContourRemainder, dif_pos hvalid]
  exact
    (selectedConcreteLocalizedContourSlice A u v m hvalid).contour_eq

/-- Scalar right-tail envelope used in the concrete remainder squeeze. -/
def localizedRightEdgeGaussianUpperBound
    (A : ℂ[X]) (m : ℝ) : ℝ :=
  ((∑ k ∈ A.support, ‖A.coeff k‖) *
      (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
    Real.sqrt (Real.pi / (m / 2))

theorem tendsto_localizedRightEdgeGaussianUpperBound
    (A : ℂ[X]) :
    Tendsto (localizedRightEdgeGaussianUpperBound A)
      atTop (𝓝 0) := by
  let C : ℝ :=
    (∑ k ∈ A.support, ‖A.coeff k‖) *
      (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)
  have hden :
      Tendsto (fun m : ℝ => m / 2) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      tendsto_id.const_mul_atTop (show 0 < (1 / 2 : ℝ) by norm_num)
  have hquot :
      Tendsto (fun m : ℝ => Real.pi / (m / 2))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hsqrt :
      Tendsto (fun m : ℝ => Real.sqrt (Real.pi / (m / 2)))
        atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hquot
  simpa [localizedRightEdgeGaussianUpperBound, C] using
    hsqrt.const_mul C

/--
The selected true-zeta contour remainder tends to zero for every fixed
polynomial and every fixed center in the critical strip.
-/
theorem tendsto_selectedLocalizedContourRemainder
    (A : ℂ[X]) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : ℝ) :
    Tendsto
      (selectedLocalizedContourRemainder A u v)
      atTop (𝓝 0) := by
  let otherUpper : ℝ → ℝ := fun m =>
    localizedOtherEdgeDecayConstant A u v
        localizedContourGoodHeightConstant *
      m ^ (A.natDegree + 2) * Real.exp (-15 * m)
  let rightUpper : ℝ → ℝ :=
    localizedRightEdgeGaussianUpperBound A
  let upper : ℝ → ℝ := fun m => otherUpper m + rightUpper m
  have hother :
      Tendsto otherUpper atTop (𝓝 0) := by
    simpa [otherUpper] using
      tendsto_localizedOtherEdgeDecayEnvelope A u v
        localizedContourGoodHeightConstant
  have hright :
      Tendsto rightUpper atTop (𝓝 0) := by
    simpa [rightUpper] using
      tendsto_localizedRightEdgeGaussianUpperBound A
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hother.add hright
  have hbound :
      ∀ᶠ m : ℝ in atTop,
        ‖selectedLocalizedContourRemainder A u v m‖ ≤ upper m := by
    filter_upwards [
      eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (A.natDegree : ℝ)] with m hm hdegree
    have hvalid : localizedContourScaleValid A u m :=
      ⟨hu, hu1, hm, hdegree⟩
    let slice :=
      selectedConcreteLocalizedContourSlice A u v m hvalid
    have hotherBound :=
      localizedOtherEdgeUpperBound_le_decayEnvelope
        A hu hu1 localizedContourGoodHeightConstant_nonneg hm
          slice.height_mem
    have hslicebound := slice.remainder_bound
    rw [selectedLocalizedContourRemainder, dif_pos hvalid]
    change
      ‖localizedContourRemainder A
          ((u : ℂ) + I * v) m u slice.height‖ ≤ upper m
    calc
      _ ≤
          localizedOtherEdgeUpperBound A u v m
              localizedContourGoodHeightConstant
              (12 * m + |v|) slice.height +
            localizedRightEdgeGaussianUpperBound A m :=
        hslicebound
      _ ≤ otherUpper m + rightUpper m := by
        gcongr
      _ = upper m := rfl
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    hbound hupper

/--
Constructor installing the actual zeta contour remainder into
`LocalizedContourData`.

The contour equality and all four geometric edge estimates are already
internal.  The remaining hypotheses state precisely the two analytic
bridges not supplied by contour geometry:

* the fixed polynomial filter eventually leaves only the target
  multiplicity in the selected zero sum;
* the concrete Gaussian `ψ` integral is bounded by the logarithmic-window
  supremum with the proposed coefficient.
-/
noncomputable def localizedContourData_of_concreteZetaContour
    (A : ℂ[X]) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : ℝ)
    (multiplicity mean : ℝ) (hmultiplicity : 0 ≤ multiplicity)
    (coefficient : ℝ → ℝ)
    (hcoefficient :
      Tendsto coefficient atTop (𝓝 (2 * mean)))
    (hcoefficientPos :
      ∀ᶠ m : ℝ in atTop, 0 < coefficient m)
    (hwindow :
      ∀ᶠ m : ℝ in atTop,
        BddAbove
          (normalizedWindowValues ((u : ℂ) + I * v) m))
    (hzero :
      ∀ᶠ m : ℝ in atTop,
        selectedLocalizedZeroResidueSum A u v m =
          (multiplicity : ℂ))
    (hpsi :
      ∀ᶠ m : ℝ in atTop,
        ‖localizedPsiGaussianAverage A
            ((u : ℂ) + I * v) m‖ / Real.pi ≤
          normalizedWindowSup ((u : ℂ) + I * v) m *
            coefficient m) :
    LocalizedContourData ((u : ℂ) + I * v)
      multiplicity mean := by
  let remainder : ℝ → ℝ := fun m =>
    ‖selectedLocalizedContourRemainder A u v m‖ / Real.pi
  have hremainder :
      Tendsto remainder atTop (𝓝 0) := by
    have hnorm :
        Tendsto
          (fun m => ‖selectedLocalizedContourRemainder A u v m‖)
          atTop (𝓝 0) := by
      simpa using
        (tendsto_norm.comp
          (tendsto_selectedLocalizedContourRemainder A hu hu1 v))
    simpa [remainder] using hnorm.div_const Real.pi
  refine {
    signal := fun _ => 2 * multiplicity
    coefficient := coefficient
    remainder := remainder
    signal_tendsto := tendsto_const_nhds
    coefficient_tendsto := hcoefficient
    remainder_tendsto := hremainder
    eventually_coefficient_pos := hcoefficientPos
    eventually_window_bddAbove := hwindow
    eventually_upper_bound := ?_
  }
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (A.natDegree : ℝ),
    hzero, hpsi] with m hm hdegree hzeroM hpsiM
  have hvalid : localizedContourScaleValid A u m :=
    ⟨hu, hu1, hm, hdegree⟩
  have hcontour :=
    selected_localizedPsiGaussianAverage_eq A
      (u := u) (v := v) (m := m) hvalid
  rw [hzeroM] at hcontour
  let L : ℂ :=
    localizedPsiGaussianAverage A
      ((u : ℂ) + I * v) m
  let R : ℂ :=
    selectedLocalizedContourRemainder A u v m
  have hmainNorm :
      2 * Real.pi * multiplicity ≤ ‖L‖ + ‖R‖ := by
    have hidentity :
        (-(2 * Real.pi : ℂ)) * (multiplicity : ℂ) =
          L - R := by
      dsimp [L, R]
      linear_combination -hcontour
    have hnormIdentity :=
      congrArg norm hidentity
    have hpiNonneg : 0 ≤ Real.pi := Real.pi_pos.le
    have hmultNorm : ‖(multiplicity : ℂ)‖ = multiplicity := by
      rw [Complex.norm_real, Real.norm_of_nonneg hmultiplicity]
    calc
      2 * Real.pi * multiplicity =
          ‖(-(2 * Real.pi : ℂ)) * (multiplicity : ℂ)‖ := by
        simp [Complex.norm_real,
          Real.norm_of_nonneg hpiNonneg, hmultNorm]
      _ = ‖L - R‖ := hnormIdentity
      _ ≤ ‖L‖ + ‖R‖ := norm_sub_le _ _
  have hpiPos : 0 < Real.pi := Real.pi_pos
  have hscaled :
      2 * multiplicity ≤ ‖L‖ / Real.pi + ‖R‖ / Real.pi := by
    calc
      2 * multiplicity =
          (2 * Real.pi * multiplicity) / Real.pi := by
            field_simp
      _ ≤ (‖L‖ + ‖R‖) / Real.pi :=
        (div_le_div_iff_of_pos_right hpiPos).2 hmainNorm
      _ = ‖L‖ / Real.pi + ‖R‖ / Real.pi := by ring
  change
    2 * multiplicity ≤
      normalizedWindowSup ((u : ℂ) + I * v) m *
          coefficient m +
        remainder m
  dsimp [remainder, L, R] at hscaled
  exact hscaled.trans (add_le_add hpsiM le_rfl)

/--
Limit-form constructor for the concrete zeta contour data.

Unlike `localizedContourData_of_concreteZetaContour`, this version only asks
the selected weighted zero sum to converge to the target multiplicity.  This
is the form produced by a fixed finite-pole filter plus a vanishing far-zero
tail.
-/
noncomputable def localizedContourData_of_concreteZetaContourLimit
    (A : ℂ[X]) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : ℝ)
    (multiplicity mean : ℝ) (hmultiplicity : 0 ≤ multiplicity)
    (coefficient : ℝ → ℝ)
    (hcoefficient :
      Tendsto coefficient atTop (𝓝 (2 * mean)))
    (hcoefficientPos :
      ∀ᶠ m : ℝ in atTop, 0 < coefficient m)
    (hwindow :
      ∀ᶠ m : ℝ in atTop,
        BddAbove
          (normalizedWindowValues ((u : ℂ) + I * v) m))
    (hzero :
      Tendsto
        (selectedLocalizedZeroResidueSum A u v)
        atTop (𝓝 (multiplicity : ℂ)))
    (hpsi :
      ∀ᶠ m : ℝ in atTop,
        ‖localizedPsiGaussianAverage A
            ((u : ℂ) + I * v) m‖ / Real.pi ≤
          normalizedWindowSup ((u : ℂ) + I * v) m *
            coefficient m) :
    LocalizedContourData ((u : ℂ) + I * v)
      multiplicity mean := by
  let zeroSum : ℝ → ℂ := selectedLocalizedZeroResidueSum A u v
  let contourRemainder : ℝ → ℂ :=
    selectedLocalizedContourRemainder A u v
  have hmultNorm :
      ‖(multiplicity : ℂ)‖ = multiplicity := by
    rw [Complex.norm_real, Real.norm_of_nonneg hmultiplicity]
  have hsignal :
      Tendsto (fun m => 2 * ‖zeroSum m‖)
        atTop (𝓝 (2 * multiplicity)) := by
    have hnorm :
        Tendsto (fun m => ‖zeroSum m‖)
          atTop (𝓝 ‖(multiplicity : ℂ)‖) := by
      simpa [zeroSum] using tendsto_norm.comp hzero
    rw [hmultNorm] at hnorm
    exact tendsto_const_nhds.mul hnorm
  have hremainder :
      Tendsto
        (fun m => ‖contourRemainder m‖ / Real.pi)
        atTop (𝓝 0) := by
    have hnorm :
        Tendsto (fun m => ‖contourRemainder m‖)
          atTop (𝓝 0) := by
      simpa [contourRemainder] using
        (tendsto_norm.comp
          (tendsto_selectedLocalizedContourRemainder A hu hu1 v))
    simpa using hnorm.div_const Real.pi
  refine {
    signal := fun m => 2 * ‖zeroSum m‖
    coefficient := coefficient
    remainder := fun m => ‖contourRemainder m‖ / Real.pi
    signal_tendsto := hsignal
    coefficient_tendsto := hcoefficient
    remainder_tendsto := hremainder
    eventually_coefficient_pos := hcoefficientPos
    eventually_window_bddAbove := hwindow
    eventually_upper_bound := ?_
  }
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (A.natDegree : ℝ),
    hpsi] with m hm hdegree hpsiM
  have hvalid : localizedContourScaleValid A u m :=
    ⟨hu, hu1, hm, hdegree⟩
  have hcontour :=
    selected_localizedPsiGaussianAverage_eq A
      (u := u) (v := v) (m := m) hvalid
  let L : ℂ :=
    localizedPsiGaussianAverage A
      ((u : ℂ) + I * v) m
  have hidentity :
      (-(2 * Real.pi : ℂ)) * zeroSum m =
        L - contourRemainder m := by
    dsimp [zeroSum, L, contourRemainder]
    linear_combination -hcontour
  have hmainNorm :
      2 * Real.pi * ‖zeroSum m‖ ≤
        ‖L‖ + ‖contourRemainder m‖ := by
    have hnormIdentity := congrArg norm hidentity
    calc
      2 * Real.pi * ‖zeroSum m‖ =
          ‖(-(2 * Real.pi : ℂ)) * zeroSum m‖ := by
        simp [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      _ = ‖L - contourRemainder m‖ := hnormIdentity
      _ ≤ ‖L‖ + ‖contourRemainder m‖ := norm_sub_le _ _
  have hscaled :
      2 * ‖zeroSum m‖ ≤
        ‖L‖ / Real.pi + ‖contourRemainder m‖ / Real.pi := by
    calc
      2 * ‖zeroSum m‖ =
          (2 * Real.pi * ‖zeroSum m‖) / Real.pi := by
            field_simp
      _ ≤ (‖L‖ + ‖contourRemainder m‖) / Real.pi :=
        (div_le_div_iff_of_pos_right Real.pi_pos).2 hmainNorm
      _ = ‖L‖ / Real.pi +
          ‖contourRemainder m‖ / Real.pi := by ring
  change
    2 * ‖zeroSum m‖ ≤
      normalizedWindowSup ((u : ℂ) + I * v) m *
          coefficient m +
        ‖contourRemainder m‖ / Real.pi
  dsimp [L] at hscaled
  exact hscaled.trans (add_le_add hpsiM le_rfl)

/--
Real-projected limit constructor used by the sharp localized oscillation
argument.

Taking the oriented real part, rather than the complex norm, preserves the
oscillating cosine kernel whose absolute mean is `2 / π`.  The separate
`psiRemainder` records the logarithmic-window tails.
-/
noncomputable def localizedContourData_of_concreteZetaContourProjectedLimit
    (A : ℂ[X]) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : ℝ)
    (multiplicity mean : ℝ)
    (coefficient psiRemainder : ℝ → ℝ)
    (hcoefficient :
      Tendsto coefficient atTop (𝓝 (2 * mean)))
    (hpsiRemainder :
      Tendsto psiRemainder atTop (𝓝 0))
    (hcoefficientPos :
      ∀ᶠ m : ℝ in atTop, 0 < coefficient m)
    (hwindow :
      ∀ᶠ m : ℝ in atTop,
        BddAbove
          (normalizedWindowValues ((u : ℂ) + I * v) m))
    (hzero :
      Tendsto
        (selectedLocalizedZeroResidueSum A u v)
        atTop (𝓝 (multiplicity : ℂ)))
    (hpsi :
      ∀ᶠ m : ℝ in atTop,
        -(localizedPsiGaussianAverage A
            ((u : ℂ) + I * v) m).re / Real.pi ≤
          normalizedWindowSup ((u : ℂ) + I * v) m *
              coefficient m +
            psiRemainder m) :
    LocalizedContourData ((u : ℂ) + I * v)
      multiplicity mean := by
  let zeroSum : ℝ → ℂ := selectedLocalizedZeroResidueSum A u v
  let contourRemainder : ℝ → ℂ :=
    selectedLocalizedContourRemainder A u v
  have hsignalRe :
      Tendsto (fun m => (zeroSum m).re)
        atTop (𝓝 multiplicity) := by
    simpa [zeroSum] using
      Complex.continuous_re.continuousAt.tendsto.comp hzero
  have hsignal :
      Tendsto (fun m => 2 * (zeroSum m).re)
        atTop (𝓝 (2 * multiplicity)) :=
    tendsto_const_nhds.mul hsignalRe
  have hcontourRemainder :
      Tendsto
        (fun m => ‖contourRemainder m‖ / Real.pi)
        atTop (𝓝 0) := by
    have hnorm :
        Tendsto (fun m => ‖contourRemainder m‖)
          atTop (𝓝 0) := by
      simpa [contourRemainder] using
        (tendsto_norm.comp
          (tendsto_selectedLocalizedContourRemainder A hu hu1 v))
    simpa using hnorm.div_const Real.pi
  have hremainder :
      Tendsto
        (fun m =>
          psiRemainder m + ‖contourRemainder m‖ / Real.pi)
        atTop (𝓝 0) := by
    simpa using hpsiRemainder.add hcontourRemainder
  refine {
    signal := fun m => 2 * (zeroSum m).re
    coefficient := coefficient
    remainder := fun m =>
      psiRemainder m + ‖contourRemainder m‖ / Real.pi
    signal_tendsto := hsignal
    coefficient_tendsto := hcoefficient
    remainder_tendsto := hremainder
    eventually_coefficient_pos := hcoefficientPos
    eventually_window_bddAbove := hwindow
    eventually_upper_bound := ?_
  }
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (A.natDegree : ℝ),
    hpsi] with m hm hdegree hpsiM
  have hvalid : localizedContourScaleValid A u m :=
    ⟨hu, hu1, hm, hdegree⟩
  have hcontour :=
    selected_localizedPsiGaussianAverage_eq A
      (u := u) (v := v) (m := m) hvalid
  let L : ℂ :=
    localizedPsiGaussianAverage A
      ((u : ℂ) + I * v) m
  have hreIdentity :
      2 * (zeroSum m).re =
        -L.re / Real.pi + (contourRemainder m).re / Real.pi := by
    have hre := congrArg Complex.re hcontour
    dsimp [zeroSum, contourRemainder, L] at hre ⊢
    norm_num [Complex.mul_re] at hre
    field_simp [Real.pi_ne_zero]
    nlinarith
  have hcontourRe :
      (contourRemainder m).re / Real.pi ≤
        ‖contourRemainder m‖ / Real.pi := by
    exact div_le_div_of_nonneg_right
      (Complex.re_le_norm _) Real.pi_pos.le
  change
    2 * (zeroSum m).re ≤
      normalizedWindowSup ((u : ℂ) + I * v) m *
          coefficient m +
        (psiRemainder m +
          ‖contourRemainder m‖ / Real.pi)
  rw [hreIdentity]
  calc
    -L.re / Real.pi + (contourRemainder m).re / Real.pi ≤
        -L.re / Real.pi +
          ‖contourRemainder m‖ / Real.pi := by
      gcongr
    _ ≤
        (normalizedWindowSup ((u : ℂ) + I * v) m *
            coefficient m + psiRemainder m) +
          ‖contourRemainder m‖ / Real.pi := by
      simpa [L, add_comm, add_left_comm, add_assoc] using
        add_le_add_right hpsiM
          (‖contourRemainder m‖ / Real.pi)
    _ = _ := by ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
