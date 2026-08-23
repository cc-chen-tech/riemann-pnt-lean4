import PrimeNumberTheorem.VKEdgePiOverTwoConcreteContourAssembly

open Complex Filter MeasureTheory Polynomial Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The pole-subtraction factor is uniformly bounded on every right edge
`Re(z) = u + 2` with `u > 0`. -/
theorem norm_div_sub_one_right_vertical_le_two
    {u : ℝ} (hu : 0 < u) (t : ℝ) :
    ‖(((u + 2 : ℝ) : ℂ) + I * t) /
        ((((u + 2 : ℝ) : ℂ) + I * t) - 1)‖ ≤ 2 := by
  let z : ℂ := ((u + 2 : ℝ) : ℂ) + I * t
  have hzsub : z - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.sub_re, Complex.add_re, Complex.mul_re] at hre
    linarith
  have hsq : ‖z‖ ^ 2 ≤ (2 * ‖z - 1‖) ^ 2 := by
    rw [Complex.sq_norm]
    rw [mul_pow, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num [z, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im]
    nlinarith [sq_nonneg u]
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hzsub)).2
  exact
    (sq_le_sq₀ (norm_nonneg z)
      (mul_nonneg (by norm_num) (norm_nonneg (z - 1)))).mp hsq

/-- The regularized logarithmic derivative is uniformly bounded on the
right edge used by the localized contour. -/
theorem norm_regularizedLogDeriv_right_vertical_le
    {u : ℝ} (hu : 0 < u) (t : ℝ) :
    ‖-logDeriv riemannZeta
          (((u + 2 : ℝ) : ℂ) + I * t) -
        ((((u + 2 : ℝ) : ℂ) + I * t) /
          ((((u + 2 : ℝ) : ℂ) + I * t) - 1))‖ ≤
      ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2 := by
  let z : ℂ := ((u + 2 : ℝ) : ℂ) + I * t
  have hzre : 1 + 1 ≤ z.re := by
    norm_num [z, Complex.add_re, Complex.mul_re]
    linarith
  have hlog :
      ‖-logDeriv riemannZeta z‖ ≤
        ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 := by
    simpa [z, mul_comm] using
      (ExplicitFormulaResidues.norm_neg_logDeriv_riemannZeta_le_vonMangoldtLSeriesNorm
        (ε := 1) (σ := u + 2) (t := t) (by norm_num) (by linarith))
  calc
    ‖-logDeriv riemannZeta z - z / (z - 1)‖ ≤
        ‖-logDeriv riemannZeta z‖ + ‖z / (z - 1)‖ :=
      norm_sub_le _ _
    _ ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2 := by
      gcongr
      simpa [z] using norm_div_sub_one_right_vertical_le_two hu t

/--
Outside distance `12m` from the center frequency, every fixed polynomial
factor can be absorbed into half of the concentrated Gaussian exponent.
-/
theorem norm_localizedRegularizedLogDerivIntegrand_right_le_gaussian
    (A : ℂ[X]) {u v m t : ℝ}
    (hu : 0 < u) (hm : 1 ≤ m)
    (hdegree : (A.natDegree : ℝ) ≤ m)
    (htail : 12 * m ≤ |t - v|) :
    ‖localizedRegularizedLogDerivIntegrand A
        ((u : ℂ) + I * v) m
        (((u + 2 : ℝ) : ℂ) + I * t)‖ ≤
      ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
        Real.exp (-(m / 2) * (t - v) ^ 2) := by
  let y : ℝ := t - v
  let d : ℂ :=
    (((u + 2 : ℝ) : ℂ) + I * t) -
      ((u : ℂ) + I * v)
  have hy : 12 ≤ |y| := by
    dsimp [y] at htail ⊢
    nlinarith
  have hdNorm : ‖d‖ ≤ |y| + 2 := by
    calc
      ‖d‖ ≤ |d.re| + |d.im| :=
        Complex.norm_le_abs_re_add_abs_im d
      _ = |y| + 2 := by
        simp only [d, y, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        norm_num
        ring
  have hbase : max 1 ‖d‖ ≤ |y| + 2 := by
    rw [max_le_iff]
    exact ⟨by linarith [abs_nonneg y], hdNorm⟩
  have hbaseExp : |y| + 2 ≤ Real.exp (|y| + 2) := by
    calc
      |y| + 2 ≤ |y| + 2 + 1 := by linarith
      _ ≤ Real.exp (|y| + 2) := Real.add_one_le_exp _
  have hpow :
      max 1 ‖d‖ ^ A.natDegree ≤
        Real.exp ((A.natDegree : ℝ) * (|y| + 2)) := by
    calc
      max 1 ‖d‖ ^ A.natDegree ≤
          (Real.exp (|y| + 2)) ^ A.natDegree := by
        gcongr
        exact hbase.trans hbaseExp
      _ = Real.exp ((A.natDegree : ℝ) * (|y| + 2)) := by
        rw [← Real.exp_nat_mul]
  have hexponent :
      m * (36 - y ^ 2) +
          (A.natDegree : ℝ) * (|y| + 2) ≤
        -(m / 2) * y ^ 2 := by
    have hm0 : 0 ≤ m := zero_le_one.trans hm
    have hy0 : 0 ≤ |y| + 2 := by positivity
    have hdegreeMul :
        (A.natDegree : ℝ) * (|y| + 2) ≤
          m * (|y| + 2) :=
      mul_le_mul_of_nonneg_right hdegree hy0
    have hySq : y ^ 2 = |y| ^ 2 := by rw [sq_abs]
    rw [hySq]
    nlinarith [sq_nonneg (|y| - 12)]
  have hweight :
      ‖localizedGaussianWeight A
          ((u : ℂ) + I * v) m
          (((u + 2 : ℝ) : ℂ) + I * t)‖ ≤
        (∑ k ∈ A.support, ‖A.coeff k‖) *
          Real.exp (-(m / 2) * y ^ 2) := by
    rw [norm_localizedGaussianWeight]
    have hpoly :=
      norm_polynomial_eval_le_coeffL1_mul_max_pow A d
    have hcoord :
        ((((u + 2 : ℝ) : ℂ) + I * t) -
            ((u : ℂ) + I * v)).re ^ 2 -
          ((((u + 2 : ℝ) : ℂ) + I * t) -
            ((u : ℂ) + I * v)).im ^ 2 +
          16 *
            ((((u + 2 : ℝ) : ℂ) + I * t) -
              ((u : ℂ) + I * v)).re =
          36 - y ^ 2 := by
      simp only [y, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
      ring
    rw [hcoord]
    calc
      ‖A.eval d‖ * Real.exp (m * (36 - y ^ 2)) ≤
          ((∑ k ∈ A.support, ‖A.coeff k‖) *
            max 1 ‖d‖ ^ A.natDegree) *
              Real.exp (m * (36 - y ^ 2)) := by
        gcongr
      _ ≤
          ((∑ k ∈ A.support, ‖A.coeff k‖) *
            Real.exp ((A.natDegree : ℝ) * (|y| + 2))) *
              Real.exp (m * (36 - y ^ 2)) := by
        gcongr
      _ =
          (∑ k ∈ A.support, ‖A.coeff k‖) *
            Real.exp
              (m * (36 - y ^ 2) +
                (A.natDegree : ℝ) * (|y| + 2)) := by
        rw [Real.exp_add]
        ring
      _ ≤
          (∑ k ∈ A.support, ‖A.coeff k‖) *
            Real.exp (-(m / 2) * y ^ 2) := by
        gcongr
  rw [localizedRegularizedLogDerivIntegrand, norm_mul]
  calc
    _ ≤
        ((∑ k ∈ A.support, ‖A.coeff k‖) *
          Real.exp (-(m / 2) * y ^ 2)) *
        (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2) := by
      gcongr
      simpa using norm_regularizedLogDeriv_right_vertical_le hu t
    _ = _ := by
      dsimp [y]
      ring

/-- The symmetric truncation error of an integrable function is the sum of
its two exterior set integrals. -/
theorem integral_sub_symmetric_intervalIntegral
    {f : ℝ → ℂ} (hf : Integrable f) (T : ℝ) :
    (∫ t : ℝ, f t) - (∫ t : ℝ in (-T)..T, f t) =
      (∫ t : ℝ in Set.Iic (-T), f t) +
        ∫ t : ℝ in Set.Ioi T, f t := by
  have hleft :
      (∫ t : ℝ in Set.Iic (-T), f t) +
          ∫ t : ℝ in Set.Ioi (-T), f t =
        ∫ t : ℝ, f t :=
    intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn
  have hright :
      (∫ t : ℝ in (-T)..T, f t) +
          ∫ t : ℝ in Set.Ioi T, f t =
        ∫ t : ℝ in Set.Ioi (-T), f t :=
    intervalIntegral.integral_interval_add_Ioi
      hf.integrableOn
      hf.integrableOn
  calc
    (∫ t : ℝ, f t) - (∫ t : ℝ in (-T)..T, f t) =
        ((∫ t : ℝ in Set.Iic (-T), f t) +
          ∫ t : ℝ in Set.Ioi (-T), f t) -
            (∫ t : ℝ in (-T)..T, f t) := by rw [hleft]
    _ =
        (∫ t : ℝ in Set.Iic (-T), f t) +
          ∫ t : ℝ in Set.Ioi T, f t := by
      rw [← hright]
      ring

/-- The concentrated Gaussian majorant for the two discarded right-edge
tails. -/
def localizedRightEdgeGaussianMajorant
    (A : ℂ[X]) (m v t : ℝ) : ℝ :=
  ((∑ k ∈ A.support, ‖A.coeff k‖) *
      (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
    Real.exp (-(m / 2) * (t - v) ^ 2)

theorem integrable_localizedRightEdgeGaussianMajorant
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m) (v : ℝ) :
    Integrable (localizedRightEdgeGaussianMajorant A m v) := by
  have hbase :
      Integrable (fun t : ℝ => Real.exp (-(m / 2) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hshift :
      Integrable (fun t : ℝ => Real.exp (-(m / 2) * (t - v) ^ 2)) :=
    hbase.comp_sub_right v
  exact hshift.const_mul _

theorem integral_localizedRightEdgeGaussianMajorant
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m) (v : ℝ) :
    (∫ t : ℝ, localizedRightEdgeGaussianMajorant A m v t) =
      ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
        Real.sqrt (Real.pi / (m / 2)) := by
  unfold localizedRightEdgeGaussianMajorant
  rw [integral_const_mul]
  have hbase :
      Integrable (fun t : ℝ => Real.exp (-(m / 2) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  rw [show
      (∫ t : ℝ, Real.exp (-(m / 2) * (t - v) ^ 2)) =
        ∫ t : ℝ, Real.exp (-(m / 2) * t ^ 2) by
      convert integral_sub_right_eq_self
        (μ := volume)
        (f := fun t : ℝ => Real.exp (-(m / 2) * t ^ 2)) v using 1]
  rw [integral_gaussian]

set_option maxHeartbeats 800000 in
/--
Once the contour height is at least `12m + |v|`, the true-zeta right-edge
tail is uniformly controlled by one complete concentrated Gaussian.
-/
theorem norm_localizedRightEdgeTail_le_gaussian_of_linearHeight
    (A : ℂ[X]) {u v m T : ℝ}
    (hu : 0 < u) (hm : 1 ≤ m)
    (hdegree : (A.natDegree : ℝ) ≤ m)
    (hTlower : 12 * m + |v| ≤ T) :
    ‖localizedRightEdgeTail A ((u : ℂ) + I * v) m u
        T‖ ≤
      ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
        Real.sqrt (Real.pi / (m / 2)) := by
  let f : ℝ → ℂ := fun t =>
    localizedRegularizedLogDerivIntegrand A
      ((u : ℂ) + I * v) m
      (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := localizedRightEdgeGaussianMajorant A m v
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  have hbaseHeight : 0 ≤ 12 * m + |v| := by positivity
  have hT : 0 ≤ T := hbaseHeight.trans hTlower
  have hf : Integrable f := by
    exact integrable_localizedRegularizedLogDerivIntegrand_verticalLine
      A hu hmPos
  have hg : Integrable g := by
    simpa [g] using
      integrable_localizedRightEdgeGaussianMajorant A hmPos v
  have htailDom :
      ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ g t := by
    intro t ht
    have hgap : 12 * m ≤ |t - v| := by
      have hreverse : |t| - |v| ≤ |t - v| :=
        abs_sub_abs_le_abs_sub t v
      linarith [hTlower]
    simpa [f, g, localizedRightEdgeGaussianMajorant, mul_comm] using
      norm_localizedRegularizedLogDerivIntegrand_right_le_gaussian
        A hu hm hdegree hgap
  have hleftDom :
      ∀ t ∈ Set.Iic (-T), ‖f t‖ ≤ g t := by
    intro t ht
    change t ≤ -T at ht
    apply htailDom t
    have ht0 : t ≤ 0 := ht.trans (neg_nonpos.mpr hT)
    rw [abs_of_nonpos ht0]
    linarith [ht]
  have hrightDom :
      ∀ t ∈ Set.Ioi T, ‖f t‖ ≤ g t := by
    intro t ht
    apply htailDom t
    rw [abs_of_pos (hT.trans_lt ht)]
    exact ht.le
  have hleft :
      ‖∫ t : ℝ in Set.Iic (-T), f t‖ ≤
        ∫ t : ℝ in Set.Iic (-T), g t := by
    exact MeasureTheory.norm_integral_le_of_norm_le
      hg.integrableOn
        (ae_restrict_of_forall_mem measurableSet_Iic hleftDom)
  have hright :
      ‖∫ t : ℝ in Set.Ioi T, f t‖ ≤
        ∫ t : ℝ in Set.Ioi T, g t := by
    exact MeasureTheory.norm_integral_le_of_norm_le
      hg.integrableOn
        (ae_restrict_of_forall_mem measurableSet_Ioi hrightDom)
  have hsplitG :
      (∫ t : ℝ in Set.Iic (-T), g t) +
          ∫ t : ℝ in Set.Ioi T, g t ≤
        ∫ t : ℝ, g t := by
    have hseries :
        0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hnonneg : ∀ t : ℝ, 0 ≤ g t := by
      intro t
      unfold g localizedRightEdgeGaussianMajorant
      exact mul_nonneg
        (mul_nonneg
          (Finset.sum_nonneg fun k _ => norm_nonneg _)
          (by linarith))
        (Real.exp_pos _).le
    have hmiddle :
        0 ≤ ∫ t : ℝ in (-T)..T, g t := by
      exact intervalIntegral.integral_nonneg
        (by linarith [hT]) (fun t _ => hnonneg t)
    have hleftAll :=
      intervalIntegral.integral_Iic_add_Ioi
        (f := g) (b := -T)
        hg.integrableOn hg.integrableOn
    have hmiddleRight :
        (∫ t : ℝ in (-T)..T, g t) +
            ∫ t : ℝ in Set.Ioi T, g t =
          ∫ t : ℝ in Set.Ioi (-T), g t :=
      intervalIntegral.integral_interval_add_Ioi
        hg.integrableOn
        hg.integrableOn
    linarith
  rw [localizedRightEdgeTail]
  have hsplitF :=
    integral_sub_symmetric_intervalIntegral hf T
  change ‖(∫ t : ℝ, f t) -
      ∫ t : ℝ in (-T)..T, f t‖ ≤ _
  rw [hsplitF]
  calc
    ‖(∫ t : ℝ in Set.Iic (-T), f t) +
        ∫ t : ℝ in Set.Ioi T, f t‖ ≤
        ‖∫ t : ℝ in Set.Iic (-T), f t‖ +
          ‖∫ t : ℝ in Set.Ioi T, f t‖ :=
      norm_add_le _ _
    _ ≤
        (∫ t : ℝ in Set.Iic (-T), g t) +
          ∫ t : ℝ in Set.Ioi T, g t := by
      gcongr
    _ ≤ ∫ t : ℝ, g t := hsplitG
    _ = _ := by
      simpa [g] using
        integral_localizedRightEdgeGaussianMajorant A hmPos v

/-- Exact linear-height specialization of the monotone tail bound. -/
theorem norm_localizedRightEdgeTail_le_gaussian
    (A : ℂ[X]) {u v m : ℝ}
    (hu : 0 < u) (hm : 1 ≤ m)
    (hdegree : (A.natDegree : ℝ) ≤ m) :
    ‖localizedRightEdgeTail A ((u : ℂ) + I * v) m u
        (12 * m + |v|)‖ ≤
      ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
        Real.sqrt (Real.pi / (m / 2)) :=
  norm_localizedRightEdgeTail_le_gaussian_of_linearHeight
    A hu hm hdegree le_rfl

/--
The true-zeta right-edge truncation error tends to zero when the contour
height grows linearly as `12m + |v|`.  Unlike the earlier fixed-`m`
statement, this has the quantifier order needed by the localized contour
assembly.
-/
theorem tendsto_localizedRightEdgeTail_linearHeight
    (A : ℂ[X]) {u : ℝ} (hu : 0 < u) (v : ℝ) :
    Tendsto
      (fun m : ℝ =>
        localizedRightEdgeTail A ((u : ℂ) + I * v) m u
          (12 * m + |v|))
      atTop (𝓝 0) := by
  let C : ℝ :=
    (∑ k ∈ A.support, ‖A.coeff k‖) *
      (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)
  let upper : ℝ → ℝ := fun m =>
    C * Real.sqrt (Real.pi / (m / 2))
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
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hquot
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hsqrt.const_mul C
  have hbound :
      ∀ᶠ m : ℝ in atTop,
        ‖localizedRightEdgeTail A ((u : ℂ) + I * v) m u
            (12 * m + |v|)‖ ≤ upper m := by
    filter_upwards [
      eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (A.natDegree : ℝ)] with m hm hdegree
    simpa [upper, C] using
      norm_localizedRightEdgeTail_le_gaussian A hu hm hdegree
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    hbound hupper

/--
At every sufficiently wide Gaussian scale, one may choose a single
Révész good height in `[12m + |v|, 12m + |v| + 1]` for which the complete
true-zeta contour remainder is bounded by the three non-right edge bounds
plus the uniform right-tail Gaussian bound.
-/
theorem
    exists_goodHeight_linearScale_norm_localizedContourRemainder_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : ℂ[X]) (u v m : ℝ),
        0 < u → u < 1 → 1 ≤ m →
          (A.natDegree : ℝ) ≤ m →
          ∃ T ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1),
            ExplicitFormulaAux.goodHeight T ∧
              ‖localizedContourRemainder A
                  ((u : ℂ) + I * v) m u T‖ ≤
                localizedOtherEdgeUpperBound A u v m C
                    (12 * m + |v|) T +
                  ((∑ k ∈ A.support, ‖A.coeff k‖) *
                    (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
                    Real.sqrt (Real.pi / (m / 2)) := by
  rcases
      exists_goodHeight_Icc_norm_localizedOtherEdgeContribution_le with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A u v m hu hu1 hm hdegree
  have hH : 4 ≤ 12 * m + |v| := by
    nlinarith [abs_nonneg v]
  have hgap : 9 + |v| ≤ 12 * m + |v| := by
    nlinarith
  rcases hchoose (12 * m + |v|) hH with
    ⟨T, hT, hgood, hother⟩
  refine ⟨T, hT, hgood, ?_⟩
  have hotherBound :
      ‖localizedOtherEdgeContribution A
          ((u : ℂ) + I * v) m u T‖ ≤
        localizedOtherEdgeUpperBound A u v m C
          (12 * m + |v|) T :=
    hother A u v m hu hu1 (zero_le_one.trans hm) hgap
  have htailBound :
      ‖localizedRightEdgeTail A
          ((u : ℂ) + I * v) m u T‖ ≤
        ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
          Real.sqrt (Real.pi / (m / 2)) :=
    norm_localizedRightEdgeTail_le_gaussian_of_linearHeight
      A hu hm hdegree hT.1
  rw [localizedContourRemainder]
  exact (norm_add_le _ _).trans (add_le_add hotherBound htailBound)

/--
Concrete dynamic contour package: at the same linearly growing good height,
the Gaussian average has the exact multiplicity-weighted zeta-zero
decomposition and its named contour remainder satisfies the uniform bound.
-/
theorem
    exists_goodHeight_linearScale_localizedPsiGaussianAverage_eq_zeroSum :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : ℂ[X]) (u v m : ℝ),
        0 < u → u < 1 → 1 ≤ m →
          (A.natDegree : ℝ) ≤ m →
          ∃ T ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1),
            ExplicitFormulaAux.goodHeight T ∧
              ∃ zeros : Finset ℂ,
                (∀ rho ∈ zeros,
                  riemannZeta rho = 0 ∧
                    (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
                    -T < rho.im ∧ rho.im < T) ∧
                (∀ rho ∈
                    ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
                  riemannZeta rho = 0 → rho ∈ zeros) ∧
                localizedPsiGaussianAverage A
                    ((u : ℂ) + I * v) m =
                  -(2 * Real.pi : ℂ) *
                      localizedZeroResidueSum A
                        ((u : ℂ) + I * v) m zeros +
                    localizedContourRemainder A
                      ((u : ℂ) + I * v) m u T ∧
                ‖localizedContourRemainder A
                    ((u : ℂ) + I * v) m u T‖ ≤
                  localizedOtherEdgeUpperBound A u v m C
                      (12 * m + |v|) T +
                    ((∑ k ∈ A.support, ‖A.coeff k‖) *
                      (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
                      Real.sqrt (Real.pi / (m / 2)) := by
  rcases
      exists_goodHeight_linearScale_norm_localizedContourRemainder_le with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A u v m hu hu1 hm hdegree
  rcases hchoose A u v m hu hu1 hm hdegree with
    ⟨T, hT, hgood, hremainder⟩
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  have hTPos : 0 < T := by
    have hbase : 0 < 12 * m + |v| := by positivity
    exact hbase.trans_le hT.1
  rcases
      exists_localizedPsiGaussianAverage_eq_zeroSum_add_contourRemainder_of_goodHeight
        A hu hmPos hTPos hgood with
    ⟨zeros, hzeros, hcomplete, heq⟩
  exact
    ⟨T, hT, hgood, zeros, hzeros, hcomplete, heq, hremainder⟩

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
