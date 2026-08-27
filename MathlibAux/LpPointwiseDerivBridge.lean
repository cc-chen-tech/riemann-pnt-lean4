import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# From pointwise slopes to an `L²`-valued derivative

This file isolates the functional-analytic bridge used by the Carlson
Gaussian argument.  Its hypothesis is the actual convergence to zero of the
integral of the squared pointwise slope error; proving that convergence by a
dominated convergence argument remains a separate obligation.
-/

open Filter MeasureTheory
open scoped Topology ENNReal MeasureTheory ComplexConjugate

/-- Pointwise complex slope of a family of scalar functions. -/
noncomputable def pointwiseComplexSlope
    {α : Type*} (f : ℂ → α → ℂ) (z u : ℂ) (t : α) : ℂ :=
  (u - z)⁻¹ * (f u t - f z t)

/-- Exact norm-square formula for a complex `L²` element constructed by
`MemLp.toLp`. -/
theorem norm_sq_memLpToLp_eq_integral_norm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  let F : Lp ℂ 2 μ := hf.toLp f
  have hinner :
      inner ℂ F F = Complex.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ x, inner ℂ (F x) (F x) ∂μ) =
          ∫ x, Complex.ofReal (‖f x‖ ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards [hf.coeFn_toLp] with x hx
            dsimp [F] at hx ⊢
            rw [hx]
            simpa using Complex.mul_conj' (f x)
      _ = Complex.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := integral_ofReal
  calc
    ‖hf.toLp f‖ ^ 2 = (inner ℂ F F).re := by
      dsimp [F]
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by rw [hinner]; simp

/-- If the integral of the squared pointwise slope error tends to zero, then
the corresponding `MemLp.toLp` family has the expected complex derivative.

This theorem contains no dominated-convergence assumption implicitly: the
integral limit is an explicit hypothesis. -/
theorem hasDerivAt_memLpToLp_of_tendsto_integral_pointwiseSlope_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℂ → α → ℂ) (hf : ∀ z, MemLp (f z) 2 μ)
    {z : ℂ} {f' : α → ℂ} (hf' : MemLp f' 2 μ)
    (hlim : Tendsto
      (fun u : ℂ => ∫ t,
        ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 ∂μ)
      (𝓝[≠] z) (𝓝 0)) :
    HasDerivAt
      (fun u : ℂ => (hf u).toLp (f u))
      (hf'.toLp f') z := by
  let F : ℂ → Lp ℂ 2 μ := fun u => (hf u).toLp (f u)
  let F' : Lp ℂ 2 μ := hf'.toLp f'
  have hslopeMem (u : ℂ) :
      MemLp (pointwiseComplexSlope f z u) 2 μ := by
    change MemLp ((u - z)⁻¹ • (f u - f z)) 2 μ
    exact ((hf u).sub (hf z)).const_smul ((u - z)⁻¹)
  have herrorMem (u : ℂ) :
      MemLp (pointwiseComplexSlope f z u - f') 2 μ :=
    (hslopeMem u).sub hf'
  have hslopeEq (u : ℂ) :
      slope F z u =
        (hslopeMem u).toLp (pointwiseComplexSlope f z u) := by
    change (u - z)⁻¹ • ((hf u).toLp (f u) - (hf z).toLp (f z)) = _
    rw [← (hf u).toLp_sub (hf z), ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun t => by
      simp [pointwiseComplexSlope, Pi.smul_apply, Pi.sub_apply]
  have hnormSq (u : ℂ) :
      ‖slope F z u - F'‖ ^ 2 =
        ∫ t, ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 ∂μ := by
    rw [hslopeEq]
    change
      ‖(hslopeMem u).toLp (pointwiseComplexSlope f z u) - hf'.toLp f'‖ ^ 2 = _
    rw [← (hslopeMem u).toLp_sub hf']
    exact norm_sq_memLpToLp_eq_integral_norm_sq (herrorMem u)
  have hnormSqTendsto : Tendsto
      (fun u : ℂ => ‖slope F z u - F'‖ ^ 2)
      (𝓝[≠] z) (𝓝 0) := by
    exact hlim.congr' (Filter.Eventually.of_forall fun u => (hnormSq u).symm)
  have hsqrtTendsto :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hnormSqTendsto
  have hnormTendsto : Tendsto
      (fun u : ℂ => ‖slope F z u - F'‖)
      (𝓝[≠] z) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hsqrtTendsto
  change HasDerivAt F F' z
  apply hasDerivAt_iff_tendsto_slope.mpr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnormTendsto

/-- A filter-form dominated convergence criterion for the squared pointwise
slope error.  Together with
`hasDerivAt_memLpToLp_of_tendsto_integral_pointwiseSlope_sq`, this reduces an
`L²`-valued derivative proof to an explicit integrable majorant. -/
theorem tendsto_integral_pointwiseSlope_sq_of_dominated
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℂ → α → ℂ) {z : ℂ} {f' : α → ℂ} {bound : α → ℝ}
    (hMeas : ∀ᶠ u in 𝓝[≠] z,
      AEStronglyMeasurable
        (fun t => ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2) μ)
    (hBound : ∀ᶠ u in 𝓝[≠] z, ∀ᵐ t ∂μ,
      ‖(‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 : ℝ)‖ ≤ bound t)
    (hBoundInt : Integrable bound μ)
    (hDeriv : ∀ᵐ t ∂μ, HasDerivAt (fun u => f u t) (f' t) z) :
    Tendsto
      (fun u : ℂ => ∫ t,
        ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 ∂μ)
      (𝓝[≠] z) (𝓝 0) := by
  have hpointwise : ∀ᵐ t ∂μ, Tendsto
      (fun u : ℂ => ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2)
      (𝓝[≠] z) (𝓝 0) := by
    filter_upwards [hDeriv] with t ht
    have hslope : Tendsto
        (fun u : ℂ => pointwiseComplexSlope f z u t)
        (𝓝[≠] z) (𝓝 (f' t)) := by
      convert ht.tendsto_slope using 1
      funext u
      rw [pointwiseComplexSlope, slope_def_field, div_eq_mul_inv]
      ring
    have hconst : Tendsto (fun _ : ℂ => f' t) (𝓝[≠] z) (𝓝 (f' t)) :=
      tendsto_const_nhds
    simpa using (hslope.sub hconst).norm.pow 2
  have hraw := tendsto_integral_filter_of_dominated_convergence
    (F := fun u : ℂ => fun t : α =>
      ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2)
    (f := fun _ : α => (0 : ℝ)) bound hMeas hBound hBoundInt hpointwise
  simpa using hraw

/-- A closed-ball derivative-square bound controls the squared error between
every nontrivial pointwise slope from the center and the center derivative.
The factor four is the triangle inequality after the mean-value bound. -/
theorem pointwiseSlope_error_sq_le_four_mul_of_deriv_sq_le
    {α : Type*} (f f' : ℂ → α → ℂ) {z : ℂ} {r : ℝ}
    {B : α → ℝ} (hr : 0 ≤ r)
    (hDeriv : ∀ v ∈ Metric.closedBall z r, ∀ t,
      HasDerivAt (fun u => f u t) (f' v t) v)
    (hB : ∀ t, 0 ≤ B t)
    (hDerivSq : ∀ v ∈ Metric.closedBall z r, ∀ t,
      ‖f' v t‖ ^ 2 ≤ B t) :
    ∀ u ∈ Metric.closedBall z r, u ≠ z → ∀ t,
      ‖pointwiseComplexSlope f z u t - f' z t‖ ^ 2 ≤ 4 * B t := by
  intro u hu huz t
  have hz : z ∈ Metric.closedBall z r :=
    Metric.mem_closedBall_self hr
  have hnormDeriv : ∀ v ∈ Metric.closedBall z r,
      ‖f' v t‖ ≤ Real.sqrt (B t) := by
    intro v hv
    exact Real.le_sqrt_of_sq_le (hDerivSq v hv t)
  have hdiff : ‖f u t - f z t‖ ≤
      Real.sqrt (B t) * ‖u - z‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun v : ℂ => f v t) (f' := fun v => f' v t)
      (s := Metric.closedBall z r)
      (fun v hv => (hDeriv v hv t).hasDerivWithinAt)
      hnormDeriv (convex_closedBall z r) hz hu
  have hnormSubPos : 0 < ‖u - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr huz)
  have hslopeNorm : ‖pointwiseComplexSlope f z u t‖ ≤
      Real.sqrt (B t) := by
    rw [pointwiseComplexSlope, norm_mul, norm_inv]
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hnormSubPos).2 hdiff
  have hcenterNorm : ‖f' z t‖ ≤ Real.sqrt (B t) :=
    hnormDeriv z hz
  have herrorNorm :
      ‖pointwiseComplexSlope f z u t - f' z t‖ ≤
        2 * Real.sqrt (B t) := by
    calc
      ‖pointwiseComplexSlope f z u t - f' z t‖
          ≤ ‖pointwiseComplexSlope f z u t‖ + ‖f' z t‖ :=
            norm_sub_le _ _
      _ ≤ Real.sqrt (B t) + Real.sqrt (B t) :=
        add_le_add hslopeNorm hcenterNorm
      _ = 2 * Real.sqrt (B t) := by ring
  calc
    ‖pointwiseComplexSlope f z u t - f' z t‖ ^ 2
        ≤ (2 * Real.sqrt (B t)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) herrorNorm 2
    _ = 4 * B t := by rw [mul_pow, Real.sq_sqrt (hB t)]; norm_num
