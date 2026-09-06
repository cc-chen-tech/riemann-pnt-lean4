import HardyTheorem.ConreyExplicitCertificate
import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory

namespace HardyTheorem

/-!
# The explicit Conrey double integral

This file connects the independently certified closed-form constant to the
actual double integral in Conrey's mollified mean-square theorem.  Everything
here is elementary real calculus; the analytic mean-square theorem itself is
not assumed or stated in this module.
-/

private abbrev conreyHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule _ _ f f' x

/-- The explicit polynomial mollifier profile used in the certificate. -/
noncomputable def conreyExplicitP (x : ℝ) : ℝ :=
  (84 * x + 15 * x ^ 3 + x ^ 5) / 100

/-- The degree-one differential polynomial used for simple zeros. -/
noncomputable def conreyExplicitQ : ℝ → ℝ :=
  (fun _y : ℝ => 1) - fun y => 51 * y / 50

private theorem hasDerivAt_const_mul_pow (c x : ℝ) (n : ℕ) :
    conreyHasDerivAt (fun z : ℝ => c * z ^ n)
      (c * (n * x ^ (n - 1))) x := by
  have hid : conreyHasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
  have hp : conreyHasDerivAt (fun z : ℝ => z ^ n)
      (n * x ^ (n - 1) * 1) x := HasDerivAt.pow hid n
  have h := @HasDerivAt.const_mul ℝ _ x ℝ _ _
    (fun z : ℝ => z ^ n) (n * x ^ (n - 1) * 1) c hp
  simpa only [mul_one] using h

private theorem hasDerivAt_div_const_real
    {f : ℝ → ℝ} {f' x d : ℝ} (h : conreyHasDerivAt f f' x) :
    conreyHasDerivAt (fun z => f z / d) (f' / d) x :=
  @HasDerivAt.div_const ℝ _ x ℝ _ _ f f' h d

private theorem hasDerivAt_exp_real
    {f : ℝ → ℝ} {f' x : ℝ} (h : conreyHasDerivAt f f' x) :
    conreyHasDerivAt (fun z => Real.exp (f z)) (Real.exp (f x) * f') x :=
  @HasDerivAt.exp f f' x h

private theorem hasDerivAt_conreyExplicitP (x : ℝ) :
    conreyHasDerivAt conreyExplicitP
      ((84 + 45 * x ^ 2 + 5 * x ^ 4) / 100) x := by
  change conreyHasDerivAt
    (fun z : ℝ => (84 * z + 15 * z ^ 3 + z ^ 5) / 100)
      ((84 + 45 * x ^ 2 + 5 * x ^ 4) / 100) x
  have h84 := hasDerivAt_const_mul_pow (84 : ℝ) x 1
  have h15 := hasDerivAt_const_mul_pow (15 : ℝ) x 3
  have h5 := hasDerivAt_const_mul_pow (1 : ℝ) x 5
  have hnum :=
    HasDerivAt.add (HasDerivAt.add h84 h15) h5
  have h := hasDerivAt_div_const_real (d := 100) hnum
  have h' := HasDerivAt.congr_deriv h (g' :=
      ((84 + 45 * x ^ 2 + 5 * x ^ 4) / 100)) (by norm_num; ring)
  simpa only [Pi.add_apply, pow_one, one_mul] using h'

private theorem hasDerivAt_conreyExplicitQ (y : ℝ) :
    conreyHasDerivAt conreyExplicitQ (-(51 / 50 : ℝ)) y := by
  change conreyHasDerivAt
    ((fun _z : ℝ => 1) - fun z => 51 * z / 50) (-(51 / 50 : ℝ)) y
  have hone : conreyHasDerivAt (fun _z : ℝ => (1 : ℝ)) 0 y :=
    hasDerivAt_const y 1
  have h51 := hasDerivAt_const_mul_pow (51 : ℝ) y 1
  have h := HasDerivAt.sub hone
    (hasDerivAt_div_const_real (d := 50) h51)
  have h' := HasDerivAt.congr_deriv h (g' := -(51 / 50 : ℝ)) (by
    norm_num)
  simpa only [pow_one, one_mul] using h'

/-- The real polynomial inside the absolute square in Conrey's constant. -/
noncomputable def conreyExplicitKernel (x y : ℝ) : ℝ :=
  conreyExplicitQ y * deriv conreyExplicitP x +
    conreyExplicitTheta * deriv conreyExplicitQ y * conreyExplicitP x +
    conreyExplicitTheta * conreyExplicitR *
      conreyExplicitQ y * conreyExplicitP x

private noncomputable def conreyExplicitA0 (y : ℝ) : ℝ :=
  21 / 25 - 1071 / 1250 * y

private noncomputable def conreyExplicitA1 (y : ℝ) : ℝ :=
  107919 / 1250000 - 1834623 / 3125000 * y

private noncomputable def conreyExplicitA2 (y : ℝ) : ℝ :=
  9 / 20 - 459 / 1000 * y

private noncomputable def conreyExplicitA3 (y : ℝ) : ℝ :=
  15417 / 1000000 - 262089 / 2500000 * y

private noncomputable def conreyExplicitA4 (y : ℝ) : ℝ :=
  1 / 20 - 51 / 1000 * y

private noncomputable def conreyExplicitA5 (y : ℝ) : ℝ :=
  5139 / 5000000 - 87363 / 12500000 * y

private noncomputable def conreyExplicitKernelExpanded (x y : ℝ) : ℝ :=
  conreyExplicitA0 y + conreyExplicitA1 y * x +
    conreyExplicitA2 y * x ^ 2 + conreyExplicitA3 y * x ^ 3 +
    conreyExplicitA4 y * x ^ 4 + conreyExplicitA5 y * x ^ 5

private theorem conreyExplicitKernel_eq_expanded (x y : ℝ) :
    conreyExplicitKernel x y = conreyExplicitKernelExpanded x y := by
  rw [conreyExplicitKernel, (hasDerivAt_conreyExplicitP x).deriv,
    (hasDerivAt_conreyExplicitQ y).deriv]
  norm_num [conreyExplicitKernelExpanded, conreyExplicitA0,
    conreyExplicitA1, conreyExplicitA2, conreyExplicitA3,
    conreyExplicitA4, conreyExplicitA5, conreyExplicitP, conreyExplicitQ,
    conreyExplicitTheta, conreyExplicitR]
  ring

private noncomputable def conreyExplicitInnerPrimitive (y : ℝ) : ℝ → ℝ :=
  let a0 := conreyExplicitA0 y
  let a1 := conreyExplicitA1 y
  let a2 := conreyExplicitA2 y
  let a3 := conreyExplicitA3 y
  let a4 := conreyExplicitA4 y
  let a5 := conreyExplicitA5 y
  (((((((((((fun x : ℝ => a0 ^ 2 * x) +
    fun x => a0 * a1 * x ^ 2) +
    fun x => (2 * a0 * a2 + a1 ^ 2) / 3 * x ^ 3) +
    fun x => (a0 * a3 + a1 * a2) / 2 * x ^ 4) +
    fun x => (2 * a0 * a4 + 2 * a1 * a3 + a2 ^ 2) / 5 * x ^ 5) +
    fun x => (a0 * a5 + a1 * a4 + a2 * a3) / 3 * x ^ 6) +
    fun x => (2 * a1 * a5 + 2 * a2 * a4 + a3 ^ 2) / 7 * x ^ 7) +
    fun x => (a2 * a5 + a3 * a4) / 4 * x ^ 8) +
    fun x => (2 * a3 * a5 + a4 ^ 2) / 9 * x ^ 9) +
    fun x => a4 * a5 / 5 * x ^ 10) +
    fun x => a5 ^ 2 / 11 * x ^ 11)

private theorem hasDerivAt_degreeFiveSquarePrimitive
    (a0 a1 a2 a3 a4 a5 x : ℝ) :
    conreyHasDerivAt
      (((((((((((fun z : ℝ => a0 ^ 2 * z) +
        fun z => a0 * a1 * z ^ 2) +
        fun z => (2 * a0 * a2 + a1 ^ 2) / 3 * z ^ 3) +
        fun z => (a0 * a3 + a1 * a2) / 2 * z ^ 4) +
        fun z => (2 * a0 * a4 + 2 * a1 * a3 + a2 ^ 2) / 5 * z ^ 5) +
        fun z => (a0 * a5 + a1 * a4 + a2 * a3) / 3 * z ^ 6) +
        fun z => (2 * a1 * a5 + 2 * a2 * a4 + a3 ^ 2) / 7 * z ^ 7) +
        fun z => (a2 * a5 + a3 * a4) / 4 * z ^ 8) +
        fun z => (2 * a3 * a5 + a4 ^ 2) / 9 * z ^ 9) +
        fun z => a4 * a5 / 5 * z ^ 10) +
        fun z => a5 ^ 2 / 11 * z ^ 11)
      ((a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 +
        a4 * x ^ 4 + a5 * x ^ 5) ^ 2) x := by
  let h0 := hasDerivAt_const_mul_pow (a0 ^ 2) x 1
  let h1 := hasDerivAt_const_mul_pow (a0 * a1) x 2
  let h2 := hasDerivAt_const_mul_pow ((2 * a0 * a2 + a1 ^ 2) / 3) x 3
  let h3 := hasDerivAt_const_mul_pow ((a0 * a3 + a1 * a2) / 2) x 4
  let h4 := hasDerivAt_const_mul_pow
    ((2 * a0 * a4 + 2 * a1 * a3 + a2 ^ 2) / 5) x 5
  let h5 := hasDerivAt_const_mul_pow
    ((a0 * a5 + a1 * a4 + a2 * a3) / 3) x 6
  let h6 := hasDerivAt_const_mul_pow
    ((2 * a1 * a5 + 2 * a2 * a4 + a3 ^ 2) / 7) x 7
  let h7 := hasDerivAt_const_mul_pow ((a2 * a5 + a3 * a4) / 4) x 8
  let h8 := hasDerivAt_const_mul_pow ((2 * a3 * a5 + a4 ^ 2) / 9) x 9
  let h9 := hasDerivAt_const_mul_pow (a4 * a5 / 5) x 10
  let h10 := hasDerivAt_const_mul_pow (a5 ^ 2 / 11) x 11
  have hsum := HasDerivAt.add
    (HasDerivAt.add
      (HasDerivAt.add
        (HasDerivAt.add
          (HasDerivAt.add
            (HasDerivAt.add
              (HasDerivAt.add
                (HasDerivAt.add
                  (HasDerivAt.add
                    (HasDerivAt.add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10
  have hsum' := HasDerivAt.congr_deriv hsum
    (g' := (a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 +
      a4 * x ^ 4 + a5 * x ^ 5) ^ 2) (by norm_num; ring)
  simpa only [Pi.add_apply, pow_one] using hsum'

private theorem hasDerivAt_conreyExplicitInnerPrimitive (x y : ℝ) :
    conreyHasDerivAt (conreyExplicitInnerPrimitive y)
      (conreyExplicitKernelExpanded x y ^ 2) x := by
  simpa [conreyExplicitInnerPrimitive, conreyExplicitKernelExpanded] using
    hasDerivAt_degreeFiveSquarePrimitive
      (conreyExplicitA0 y) (conreyExplicitA1 y) (conreyExplicitA2 y)
      (conreyExplicitA3 y) (conreyExplicitA4 y) (conreyExplicitA5 y) x

/-- The hand-derived inner polynomial in the exponential variable. -/
noncomputable def conreyExplicitInnerPolynomial (y : ℝ) : ℝ :=
  (103851307011369636 * y ^ 2 -
      158615980968417540 * y + 61041728800527025) /
    54140625000000000

/-- Exact evaluation of the inner `x` integral in Conrey's constant. -/
theorem conreyExplicitInnerIntegral_eq (y : ℝ) :
    (∫ x in (0 : ℝ)..1, conreyExplicitKernel x y ^ 2) =
      conreyExplicitInnerPolynomial y := by
  have hint : IntervalIntegrable
      (fun x : ℝ => conreyExplicitKernelExpanded x y ^ 2) volume 0 1 :=
    (by
      unfold conreyExplicitKernelExpanded
      fun_prop : Continuous
        (fun x : ℝ => conreyExplicitKernelExpanded x y ^ 2)).intervalIntegrable _ _
  simp_rw [conreyExplicitKernel_eq_expanded]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx => hasDerivAt_conreyExplicitInnerPrimitive x y) hint]
  norm_num [conreyExplicitInnerPrimitive, conreyExplicitInnerPolynomial,
    conreyExplicitA0, conreyExplicitA1, conreyExplicitA2,
    conreyExplicitA3, conreyExplicitA4, conreyExplicitA5]
  ring

private noncomputable def conreyExplicitOuterPrimitive : ℝ → ℝ :=
  (fun y : ℝ => Real.exp ((12 / 5 : ℝ) * y)) *
    (((fun _y : ℝ => 13055296197749681 / 10395000000000000) -
      fun y => 2723985964569173 / 1443750000000000 * y) +
      fun y => 2884758528093601 / 3609375000000000 * y ^ 2)

private theorem hasDerivAt_conreyExplicitOuterPrimitive (y : ℝ) :
    conreyHasDerivAt conreyExplicitOuterPrimitive
      (Real.exp (2 * conreyExplicitR * y) *
        conreyExplicitInnerPolynomial y) y := by
  change conreyHasDerivAt
    ((fun z : ℝ => Real.exp ((12 / 5 : ℝ) * z)) *
      (((fun _z : ℝ => 13055296197749681 / 10395000000000000) -
        fun z => 2723985964569173 / 1443750000000000 * z) +
        fun z => 2884758528093601 / 3609375000000000 * z ^ 2))
    (Real.exp (2 * conreyExplicitR * y) *
      conreyExplicitInnerPolynomial y) y
  have hlinear := hasDerivAt_const_mul_pow (12 / 5 : ℝ) y 1
  have hexp := hasDerivAt_exp_real hlinear
  have hconst : conreyHasDerivAt
      (fun _z : ℝ =>
        (13055296197749681 / 10395000000000000 : ℝ)) 0 y :=
    hasDerivAt_const y _
  have hpoly :=
    HasDerivAt.add
      (HasDerivAt.sub hconst
        (hasDerivAt_const_mul_pow
          (2723985964569173 / 1443750000000000 : ℝ) y 1))
      (hasDerivAt_const_mul_pow
        (2884758528093601 / 3609375000000000 : ℝ)
        y 2)
  have hmul := HasDerivAt.mul hexp hpoly
  have hmul' := HasDerivAt.congr_deriv hmul
    (g' := Real.exp (2 * conreyExplicitR * y) *
      conreyExplicitInnerPolynomial y) (by
      norm_num [conreyExplicitR, conreyExplicitInnerPolynomial]
      ring)
  simpa only [pow_one] using hmul'

/-- Conrey's double-integral constant at the explicit rational parameters. -/
noncomputable def conreyExplicitMeanSquareIntegral : ℝ :=
  (conreyExplicitP 1 * conreyExplicitQ 0) ^ 2 +
    1 / conreyExplicitTheta *
      ∫ y in (0 : ℝ)..1, Real.exp (2 * conreyExplicitR * y) *
        ∫ x in (0 : ℝ)..1, conreyExplicitKernel x y ^ 2

/-- The explicit double integral is exactly the previously certified
closed-form mean-square constant. -/
theorem conreyExplicitMeanSquareIntegral_eq_constant :
    conreyExplicitMeanSquareIntegral =
      conreyExplicitMeanSquareConstant := by
  have hint : IntervalIntegrable
      (fun y : ℝ => Real.exp (2 * conreyExplicitR * y) *
        conreyExplicitInnerPolynomial y) volume 0 1 :=
    (by
      unfold conreyExplicitInnerPolynomial
      fun_prop : Continuous
        (fun y : ℝ => Real.exp (2 * conreyExplicitR * y) *
          conreyExplicitInnerPolynomial y)).intervalIntegrable _ _
  rw [conreyExplicitMeanSquareIntegral]
  simp_rw [conreyExplicitInnerIntegral_eq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _hy => hasDerivAt_conreyExplicitOuterPrimitive y) hint]
  norm_num [conreyExplicitP, conreyExplicitQ, conreyExplicitTheta,
    conreyExplicitR, conreyExplicitOuterPrimitive,
    conreyExplicitMeanSquareConstant]
  ring

/-- The actual double integral, rather than merely its closed-form alias,
lies below the exponential threshold used in the two-fifths certificate. -/
theorem conreyExplicitMeanSquareIntegral_lt_exp :
    conreyExplicitMeanSquareIntegral < Real.exp (18 / 25 : ℝ) := by
  rw [conreyExplicitMeanSquareIntegral_eq_constant]
  exact conreyExplicitMeanSquareConstant_lt_exp

/-- The explicit value of Conrey's mean-square integral gives a strict
simple-zero proportion greater than two fifths once the analytic
Levinson--Conrey inequality is available. -/
theorem conreyExplicitIntegralProportion_gt_two_fifths :
    (2 : ℝ) / 5 <
      1 - Real.log conreyExplicitMeanSquareIntegral / conreyExplicitR := by
  rw [conreyExplicitMeanSquareIntegral_eq_constant]
  exact conreyExplicitProportion_gt_two_fifths

end HardyTheorem
