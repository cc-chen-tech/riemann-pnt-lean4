import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.L2Space

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
