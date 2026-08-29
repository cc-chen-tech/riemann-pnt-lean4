import PrimeNumberTheorem.MWKFCubicActualMoment

open Complex MeasureTheory Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Exact finite expansion of the cubic mollified moment

This module expands only the two finite mollifier factors.  It performs no
approximate-functional-equation or asymptotic step.  The output is an exact
finite sum of genuine twisted zeta moments, with all integrability needed for
the finite sum--integral interchange proved from the compact support of `W`.
-/

/-- The exact finite support of the cubic mollifier. -/
noncomputable def cubicMollifierSupport (T : ℝ) : Finset ℕ :=
  Finset.Icc 1 (cubicMollifierLength T)

/-- The exact linearly tapered Möbius coefficient at cubic length. -/
noncomputable def cubicMollifierCoefficient (T : ℝ) (n : ℕ) : ℝ :=
  HardyTheorem.selbergMoebiusCoeff (cubicMollifierLength T) n

/-- The existing concrete Selberg mollifier is literally the finite sum with
the cubic coefficient and support introduced above. -/
theorem cubicMollifier_eq_sum (T : ℝ) (s : ℂ) :
    HardyTheorem.selbergMoebiusMollifier (cubicMollifierLength T) s =
      ∑ n ∈ cubicMollifierSupport T,
        (cubicMollifierCoefficient T n : ℂ) * (1 / (n : ℂ) ^ s) := by
  rfl

/-- The noncompact oscillatory factor in an ordered twisted moment. -/
noncomputable def cubicTwistOscillator
    (d e : ℕ) (t : ℝ) : ℂ :=
  (Complex.normSq (riemannZeta ((1 / 2 : ℂ) + I * t)) : ℂ) *
    (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
    (starRingEnd ℂ) (1 / (e : ℂ) ^ ((1 / 2 : ℂ) + I * t))

/-- The complex twisted integrand belonging to the ordered pair `(d,e)`.
The first monomial is the ordinary mollifier factor and the second is its
complex conjugate, so its critical-line phase is `exp(it log(e/d))`. -/
noncomputable def cubicTwistedIntegrand
    (W : CubicTestWeight) (T : ℝ) (d e : ℕ) (t : ℝ) : ℂ :=
  W (t / T) • cubicTwistOscillator d e t

/-- The genuine whole-line twisted moment for the ordered mollifier pair. -/
noncomputable def cubicTwistedMoment
    (W : CubicTestWeight) (T : ℝ) (d e : ℕ) : ℂ :=
  ∫ t : ℝ, cubicTwistedIntegrand W T d e t

/-- The standard arithmetic twist with phase `exp(it(log e-log d))`, before
the mollifier amplitude `1/sqrt(de)` is attached. -/
noncomputable def cubicStandardTwistedIntegrand
    (W : CubicTestWeight) (T : ℝ) (d e : ℕ) (t : ℝ) : ℂ :=
  W (t / T) •
    ((Complex.normSq (riemannZeta ((1 / 2 : ℂ) + I * t)) : ℂ) *
      Complex.exp
        ((I * ((Real.log e - Real.log d : ℝ) : ℂ)) * t))

/-- The genuine standard twisted second moment attached to `(d,e)`. -/
noncomputable def cubicStandardTwistedMoment
    (W : CubicTestWeight) (T : ℝ) (d e : ℕ) : ℂ :=
  ∫ t : ℝ, cubicStandardTwistedIntegrand W T d e t

/-- The actual cubic moment, viewed as a complex integral. -/
noncomputable def cubicComplexMollifiedSecondMoment
    (W : CubicTestWeight) (T : ℝ) : ℂ :=
  ∫ t : ℝ, (cubicMomentIntegrand W T t : ℂ)

/-- Exact Hermitian double expansion of the squared norm of the finite
mollifier. -/
theorem cubicMollifierNormSq_eq_doubleSum (T t : ℝ) :
    (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
      (cubicMollifierLength T) ((1 / 2 : ℂ) + I * t)) : ℂ) =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        (cubicMollifierCoefficient T d : ℂ) *
          (cubicMollifierCoefficient T e : ℂ) *
          ((1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            (starRingEnd ℂ)
              (1 / (e : ℂ) ^ ((1 / 2 : ℂ) + I * t))) := by
  rw [Complex.normSq_eq_conj_mul_self, mul_comm, cubicMollifier_eq_sum]
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

private theorem cubic_inv_nat_cpow_half_eq_inv_sqrt (n : ℕ) :
    ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ = ((Real.sqrt n : ℝ) : ℂ)⁻¹ := by
  congr 1
  calc
    (n : ℂ) ^ (1 / 2 : ℂ) =
        (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      exact (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ n) (1 / 2)).symm
    _ = ((Real.sqrt n : ℝ) : ℂ) := by rw [Real.sqrt_eq_rpow]

private theorem cubic_conj_inv_nat_cpow_criticalLine_eq_exp
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (starRingEnd ℂ)
        (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
        Complex.exp ((I * (Real.log n : ℂ)) * t) := by
  rw [HardyTheorem.inv_nat_cpow_criticalLine_eq_exp hn t, map_mul,
    cubic_inv_nat_cpow_half_eq_inv_sqrt, map_inv₀,
    Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_neg, conj_I, Complex.conj_ofReal]
  ring

/-- Exact critical-line normalization of one ordered mollifier pair.  This is
the phase `exp(it log(e/d))` with the complete `1/sqrt(de)` amplitude. -/
theorem cubicCriticalPair_eq_exp
    {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) (t : ℝ) :
    (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        (starRingEnd ℂ) (1 / (e : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹) *
        Complex.exp
          ((I * ((Real.log e - Real.log d : ℝ) : ℂ)) * t) := by
  rw [HardyTheorem.inv_nat_cpow_criticalLine_eq_exp hd t,
    cubic_inv_nat_cpow_half_eq_inv_sqrt,
    cubic_conj_inv_nat_cpow_criticalLine_eq_exp he t]
  have hsqrt :
      ((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt e : ℝ) : ℂ)⁻¹ =
        ((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ d)]
    norm_cast
  have hexp :
      Complex.exp ((-I * (Real.log d : ℂ)) * t) *
          Complex.exp ((I * (Real.log e : ℂ)) * t) =
        Complex.exp
          ((I * ((Real.log e - Real.log d : ℝ) : ℂ)) * t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    ((Real.sqrt d : ℝ) : ℂ)⁻¹ *
          Complex.exp ((-I * (Real.log d : ℂ)) * t) *
        (((Real.sqrt e : ℝ) : ℂ)⁻¹ *
          Complex.exp ((I * (Real.log e : ℂ)) * t)) =
        (((Real.sqrt d : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt e : ℝ) : ℂ)⁻¹) *
          (Complex.exp ((-I * (Real.log d : ℂ)) * t) *
            Complex.exp ((I * (Real.log e : ℂ)) * t)) := by ring
    _ = (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹) *
        Complex.exp
          ((I * ((Real.log e - Real.log d : ℝ) : ℂ)) * t) := by
      rw [hsqrt, hexp]

/-- The monomial-normalized twisted integrand is exactly `1/sqrt(de)` times
the standard arithmetic twist. -/
theorem cubicTwistedIntegrand_eq_invSqrt_mul_standard
    (W : CubicTestWeight) (T : ℝ) {d e : ℕ}
    (hd : d ≠ 0) (he : e ≠ 0) (t : ℝ) :
    cubicTwistedIntegrand W T d e t =
      (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹) *
        cubicStandardTwistedIntegrand W T d e t := by
  unfold cubicTwistedIntegrand cubicTwistOscillator
    cubicStandardTwistedIntegrand
  rw [mul_assoc, cubicCriticalPair_eq_exp hd he t]
  simp only [Complex.real_smul]
  ring

/-- The same exact normalization after integration over the full real line. -/
theorem cubicTwistedMoment_eq_invSqrt_mul_standard
    (W : CubicTestWeight) (T : ℝ) {d e : ℕ}
    (hd : d ≠ 0) (he : e ≠ 0) :
    cubicTwistedMoment W T d e =
      (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹) *
        cubicStandardTwistedMoment W T d e := by
  unfold cubicTwistedMoment cubicStandardTwistedMoment
  rw [show (fun t : ℝ ↦ cubicTwistedIntegrand W T d e t) =
      fun t : ℝ ↦ (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹) *
        cubicStandardTwistedIntegrand W T d e t by
    funext t
    exact cubicTwistedIntegrand_eq_invSqrt_mul_standard W T hd he t]
  rw [integral_const_mul]

private theorem continuous_cubicCriticalMonomial
    {n : ℕ} (hn : n ≠ 0) :
    Continuous (fun t : ℝ ↦
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) := by
  rw [show (fun t : ℝ ↦
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      fun t : ℝ ↦ ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t) by
    funext t
    exact HardyTheorem.inv_nat_cpow_criticalLine_eq_exp hn t]
  fun_prop

/-- Each twisted integrand is continuous on the positive mollifier support. -/
theorem continuous_cubicTwistedIntegrand
    (W : CubicTestWeight) (T : ℝ)
    {d e : ℕ} (hd : d ∈ cubicMollifierSupport T)
    (he : e ∈ cubicMollifierSupport T) :
    Continuous (cubicTwistedIntegrand W T d e) := by
  have hd0 : d ≠ 0 := by
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    omega
  have he0 : e ≠ 0 := by
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    omega
  rw [show cubicTwistedIntegrand W T d e = fun t ↦
      W (t / T) • (((HardyTheorem.hardyZ t ^ 2 : ℝ) : ℂ) *
        (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        (starRingEnd ℂ) (1 / (e : ℂ) ^ ((1 / 2 : ℂ) + I * t))) by
    funext t
    unfold cubicTwistedIntegrand cubicTwistOscillator
    have hzeta : HardyTheorem.hardyZ t ^ 2 =
        Complex.normSq (riemannZeta ((1 / 2 : ℂ) + I * t)) := by
      rw [← sq_abs, HardyTheorem.abs_hardyZ_eq_norm_riemannZeta,
        Complex.normSq_eq_norm_sq]
    rw [hzeta]]
  exact (W.continuous.comp (continuous_id.div_const T)).smul
    (((Complex.continuous_ofReal.comp
    (HardyTheorem.hardyZ_continuous.pow 2)).mul
      (continuous_cubicCriticalMonomial hd0)).mul
        (continuous_star.comp (continuous_cubicCriticalMonomial he0)))

/-- The compact support of `W(t/T)` makes every twisted integrand compactly
supported when `T` is nonzero. -/
theorem hasCompactSupport_cubicTwistedIntegrand
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) (d e : ℕ) :
    HasCompactSupport (cubicTwistedIntegrand W T d e) := by
  change HasCompactSupport
    ((fun t : ℝ ↦ W (t / T)) • cubicTwistOscillator d e)
  exact (W.hasCompactSupport_dilate hT).smul_right

/-- Every pair in the finite mollifier support gives an integrable twisted
integrand. -/
theorem integrable_cubicTwistedIntegrand
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0)
    {d e : ℕ} (hd : d ∈ cubicMollifierSupport T)
    (he : e ∈ cubicMollifierSupport T) :
    Integrable (cubicTwistedIntegrand W T d e) :=
  (continuous_cubicTwistedIntegrand W T hd he).integrable_of_hasCompactSupport
    (hasCompactSupport_cubicTwistedIntegrand W hT d e)

/-- Complexifying the real integral does not change the actual moment. -/
theorem cubicComplexMollifiedSecondMoment_eq_ofReal
    (W : CubicTestWeight) {T : ℝ} (_hT : T ≠ 0) :
    cubicComplexMollifiedSecondMoment W T =
      (cubicMollifiedSecondMoment W T : ℂ) := by
  unfold cubicComplexMollifiedSecondMoment cubicMollifiedSecondMoment
  exact integral_complex_ofReal

/-- Exact finite sum--integral interchange for the actual cubic moment. -/
theorem cubicComplexMollifiedSecondMoment_eq_twisted_sum
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) :
    cubicComplexMollifiedSecondMoment W T =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        (cubicMollifierCoefficient T d : ℂ) *
          (cubicMollifierCoefficient T e : ℂ) *
          cubicTwistedMoment W T d e := by
  unfold cubicComplexMollifiedSecondMoment
  rw [show (fun t : ℝ ↦ (cubicMomentIntegrand W T t : ℂ)) =
      fun t : ℝ ↦ ∑ d ∈ cubicMollifierSupport T,
        ∑ e ∈ cubicMollifierSupport T,
          (cubicMollifierCoefficient T d : ℂ) *
            (cubicMollifierCoefficient T e : ℂ) *
            cubicTwistedIntegrand W T d e t by
    funext t
    unfold cubicMomentIntegrand cubicTwistedIntegrand cubicTwistOscillator
    push_cast
    rw [cubicMollifierNormSq_eq_doubleSum]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.real_smul]
    ring]
  rw [integral_finsetSum (cubicMollifierSupport T)
    (fun d hd ↦ integrable_finsetSum _ fun e he ↦
      (integrable_cubicTwistedIntegrand W hT hd he).const_mul _)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [integral_finsetSum (cubicMollifierSupport T)
    (fun e he ↦ (integrable_cubicTwistedIntegrand W hT hd he).const_mul _)]
  apply Finset.sum_congr rfl
  intro e he
  unfold cubicTwistedMoment
  rw [integral_const_mul]

end MWKFCubic
end PrimeNumberTheorem
