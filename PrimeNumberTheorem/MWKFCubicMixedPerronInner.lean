import PrimeNumberTheorem.ShiftedFirstOrderPerron

set_option maxHeartbeats 800000

/-!
# The inner principal value in the mixed cubic Perron model

This module evaluates the conditionally convergent inner vertical integral in
the mixed kernel `1 / (s * t * (s + t))`.  The proof keeps the symmetric finite
truncation until after the partial-fraction identity and invokes translation
invariance only for the resulting shifted first-order Perron kernel.
-/

open Complex MeasureTheory Set Filter Topology

namespace PrimeNumberTheorem.MWKFCubic

/-- A Fourier-normalized point on the vertical line of real part `sigma`. -/
noncomputable def cubicPerronVerticalPoint (sigma x : ℝ) : ℂ :=
  (sigma : ℂ) + 2 * Real.pi * x * Complex.I

/-- The inner-variable kernel of the mixed double-Perron main integral. -/
noncomputable def cubicMixedPerronInnerKernel
    (sigma L x y : ℝ) : ℂ :=
  let s := cubicPerronVerticalPoint sigma x
  let t := cubicPerronVerticalPoint sigma y
  Complex.exp ((s + t) * L) / (s * t * (s + t))

/-- The pointwise value left after evaluating the inner principal value. -/
noncomputable def cubicMixedPerronInnerLimit
    (sigma L x : ℝ) : ℂ :=
  let s := cubicPerronVerticalPoint sigma x
  (Complex.exp (s * L) - 1) / s ^ 2

private lemma cubicPerronVerticalPoint_ne_zero
    {sigma x : ℝ} (hsigma : 0 < sigma) :
    cubicPerronVerticalPoint sigma x ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [cubicPerronVerticalPoint] at hre
  linarith

private lemma cubicPerronVerticalPoint_add_ne_zero
    {sigma x y : ℝ} (hsigma : 0 < sigma) :
    cubicPerronVerticalPoint sigma x + cubicPerronVerticalPoint sigma y ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [cubicPerronVerticalPoint] at hre
  linarith

/-- For fixed outer ordinate `x`, the symmetrically truncated inner mixed
Perron integral converges to `(exp(s*L) - 1) / s^2`.  The positivity of `L`
keeps both first-order Perron terms on the open side of the jump. -/
theorem tendsto_cubicMixedPerronInnerKernel_atTop
    (sigma : ℝ) (hsigma : 0 < sigma) (L : ℝ) (hL : 0 < L) (x : ℝ) :
    Tendsto
      (fun W : ℝ => ∫ y : ℝ in (-W)..W,
        cubicMixedPerronInnerKernel sigma L x y)
      atTop (nhds (cubicMixedPerronInnerLimit sigma L x)) := by
  let s : ℂ := cubicPerronVerticalPoint sigma x
  let t : ℝ → ℂ := fun y => cubicPerronVerticalPoint sigma y
  let A : ℝ → ℂ := fun y =>
    Complex.exp (t y * L) / t y
  let F : ℝ → ℂ := fun z =>
    Complex.exp (((((2 * sigma : ℝ) : ℂ) +
      2 * Real.pi * z * Complex.I) * L)) /
      (((2 * sigma : ℝ) : ℂ) + 2 * Real.pi * z * Complex.I)
  let B : ℝ → ℂ := fun y => F (y + x)
  have hs : s ≠ 0 := cubicPerronVerticalPoint_ne_zero hsigma
  have ht : ∀ y : ℝ, t y ≠ 0 :=
    fun y => cubicPerronVerticalPoint_ne_zero hsigma
  have hst : ∀ y : ℝ, s + t y ≠ 0 :=
    fun y => cubicPerronVerticalPoint_add_ne_zero hsigma
  have hAcont : Continuous A := by
    dsimp [A, t, cubicPerronVerticalPoint]
    exact (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp (((sigma : ℂ) + 2 * Real.pi * y * Complex.I) * L)).div₀
        (by fun_prop) ht
  have hFden : ∀ z : ℝ,
      (((2 * sigma : ℝ) : ℂ) + 2 * Real.pi * z * Complex.I) ≠ 0 := by
    intro z h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hFcont : Continuous F := by
    dsimp [F]
    exact (by fun_prop : Continuous fun z : ℝ =>
      Complex.exp ((((2 * sigma : ℝ) : ℂ) +
        2 * Real.pi * z * Complex.I) * L)).div₀ (by fun_prop) hFden
  have hBcont : Continuous B := hFcont.comp (by fun_prop)
  have hB_eq (y : ℝ) :
      B y = Complex.exp ((s + t y) * L) / (s + t y) := by
    have hsum :
        (((2 * sigma : ℝ) : ℂ) +
            2 * Real.pi * ((y + x : ℝ) : ℂ) * Complex.I) =
          s + t y := by
      dsimp [s, t, cubicPerronVerticalPoint]
      push_cast
      ring
    dsimp [B, F]
    rw [hsum]
  have hfinite (W : ℝ) :
      (∫ y : ℝ in (-W)..W, cubicMixedPerronInnerKernel sigma L x y) =
        Complex.exp (s * L) / s ^ 2 * (∫ y : ℝ in (-W)..W, A y) -
          (1 / s ^ 2) * (∫ y : ℝ in (-W)..W, B y) := by
    calc
      (∫ y : ℝ in (-W)..W, cubicMixedPerronInnerKernel sigma L x y) =
          ∫ y : ℝ in (-W)..W,
            Complex.exp (s * L) / s ^ 2 * A y - (1 / s ^ 2) * B y := by
        apply intervalIntegral.integral_congr
        intro y _hy
        have ht' := ht y
        have hst' := hst y
        change cubicMixedPerronInnerKernel sigma L x y =
          Complex.exp (s * L) / s ^ 2 * A y - (1 / s ^ 2) * B y
        rw [hB_eq]
        change Complex.exp ((s + t y) * L) / (s * t y * (s + t y)) =
          Complex.exp (s * L) / s ^ 2 *
              (Complex.exp (t y * L) / t y) -
            1 / s ^ 2 * (Complex.exp ((s + t y) * L) / (s + t y))
        rw [show (s + t y) * L = s * L + t y * L by ring,
          Complex.exp_add]
        field_simp [hs, ht', hst']
        ring
      _ = (∫ y : ℝ in (-W)..W,
            Complex.exp (s * L) / s ^ 2 * A y) -
          (∫ y : ℝ in (-W)..W, (1 / s ^ 2) * B y) := by
        rw [intervalIntegral.integral_sub]
        · exact (continuous_const.mul hAcont).intervalIntegrable _ _
        · exact (continuous_const.mul hBcont).intervalIntegrable _ _
      _ = Complex.exp (s * L) / s ^ 2 * (∫ y : ℝ in (-W)..W, A y) -
          (1 / s ^ 2) * (∫ y : ℝ in (-W)..W, B y) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hA : Tendsto
      (fun W : ℝ => ∫ y : ℝ in (-W)..W, A y) atTop (nhds 1) := by
    have h := tendsto_truncated_firstOrderPerronKernel_atTop sigma hsigma L
    simpa [A, t, cubicPerronVerticalPoint, perronHalfStep, hL] using h
  have hB : Tendsto
      (fun W : ℝ => ∫ y : ℝ in (-W)..W, B y) atTop (nhds 1) := by
    have h2sigma : 0 < 2 * sigma := by positivity
    have h := tendsto_translated_truncated_firstOrderPerronKernel_atTop
      (2 * sigma) h2sigma L x
    have hchange (W : ℝ) :
        (∫ y : ℝ in (-W)..W, B y) =
          ∫ z : ℝ in (-W + x)..(W + x), F z := by
      change (∫ y : ℝ in (-W)..W, F (y + x)) =
        ∫ z : ℝ in (-W + x)..(W + x), F z
      exact intervalIntegral.integral_comp_add_right
        (a := -W) (b := W) F x
    convert h using 1
    · funext W
      exact hchange W
    · simp [perronHalfStep, hL]
  have hcombined :=
    (hA.const_mul (Complex.exp (s * L) / s ^ 2)).sub
      (hB.const_mul (1 / s ^ 2))
  convert hcombined using 1
  · funext W
    exact hfinite W
  · dsimp [cubicMixedPerronInnerLimit, s]
    ring_nf

/-- The pointwise inner principal value is absolutely integrable in the outer
ordinate.  This is the difference of two second-order Perron kernels. -/
theorem integrable_cubicMixedPerronInnerLimit
    (sigma : ℝ) (hsigma : 0 < sigma) (L : ℝ) :
    Integrable (cubicMixedPerronInnerLimit sigma L) := by
  let K : ℝ → ℝ → ℂ := fun u x =>
    Complex.exp (cubicPerronVerticalPoint sigma x * u) /
      cubicPerronVerticalPoint sigma x ^ 2
  have hK (u : ℝ) : Integrable (K u) := by
    simpa [K, cubicPerronVerticalPoint] using
      integrable_secondOrderPerronKernel sigma hsigma u
  have hrewrite : cubicMixedPerronInnerLimit sigma L = fun x => K L x - K 0 x := by
    funext x
    dsimp [cubicMixedPerronInnerLimit, K]
    simp
    ring
  rw [hrewrite]
  exact (hK L).sub (hK 0)

/-- The outer full-height integral of the evaluated inner principal value is
exactly `L`.  Together with `tendsto_cubicMixedPerronInnerKernel_atTop`, this
is the Fourier-normalized iterated-principal-value form of the exponential
mixed double-Perron identity. -/
theorem integral_cubicMixedPerronInnerLimit_eq
    (sigma : ℝ) (hsigma : 0 < sigma) (L : ℝ) (hL : 0 < L) :
    (∫ x : ℝ, cubicMixedPerronInnerLimit sigma L x) = (L : ℂ) := by
  let K : ℝ → ℝ → ℂ := fun u x =>
    Complex.exp (cubicPerronVerticalPoint sigma x * u) /
      cubicPerronVerticalPoint sigma x ^ 2
  have hK (u : ℝ) : Integrable (K u) := by
    simpa [K, cubicPerronVerticalPoint] using
      integrable_secondOrderPerronKernel sigma hsigma u
  have hrewrite : cubicMixedPerronInnerLimit sigma L = fun x => K L x - K 0 x := by
    funext x
    dsimp [cubicMixedPerronInnerLimit, K]
    simp
    ring
  rw [hrewrite, integral_sub (hK L) (hK 0)]
  have hLkernel : (∫ x : ℝ, K L x) = (L : ℂ) := by
    simpa [K, cubicPerronVerticalPoint, max_eq_left hL.le] using
      secondOrderPerron_eq_max sigma hsigma L
  have hzeroKernel : (∫ x : ℝ, K 0 x) = 0 := by
    simpa [K, cubicPerronVerticalPoint] using
      secondOrderPerron_eq_max sigma hsigma 0
  rw [hLkernel, hzeroKernel, sub_zero]

end PrimeNumberTheorem.MWKFCubic
