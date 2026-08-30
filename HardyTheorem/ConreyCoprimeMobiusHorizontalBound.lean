import HardyTheorem.ConreyCoprimeEulerBound
import HardyTheorem.ConreyReciprocalZetaStrip

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace HardyTheorem

/-! Quantitative estimates for both actual horizontal Perron connectors.
All modulus dependence, the interval length and the squared kernel remain
explicit. Continuity and integrability are proved before the integral bound. -/

theorem exists_conrey_coprime_mobius_horizontal_bound :
    ∃ c T : ℝ, 0 < c ∧ c ≤ 1 ∧ 2 ≤ T ∧
      ∀ (m : ℕ) (δ : ℝ) (α : ℂ) (X b u K y : ℝ),
        0 ≤ δ → δ ≤ 1 / 16 → 1 ≤ X → 0 ≤ b → 0 ≤ u →
        T + 1 ≤ K → |y| = K →
        b + ‖α‖ ≤ 2 * δ → b + ‖α‖ ≤ c / Real.log (K + 1) →
        u + ‖α‖ ≤ 1 →
        let f : ℝ → ℂ := fun x => (X : ℂ) ^ ((x : ℂ) + y * I) *
          (riemannZeta (1 + α + ((x : ℂ) + y * I)) *
            ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + ((x : ℂ) + y * I)))))⁻¹ *
          (1 / ((x : ℂ) + y * I) ^ 2)
        IntervalIntegrable f volume (-b) u ∧
          ‖∫ x in (-b)..u, f x‖ ≤
            (b + u) * X ^ u * conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ *
              (1 + Real.log (K + 1) / c) * Real.exp (Real.log (K + 1) / 4) / K ^ 2 := by
  obtain ⟨c, T, hc, hc1, hT, hstrip⟩ := exists_conrey_reciprocal_zeta_quarterPower_strip
  refine ⟨c, T, hc, hc1, hT, ?_⟩
  intro m δ α X b u K y hδ hδ16 hX hb hu hK hy hδwidth hwidth hupper
  dsimp only
  let w : ℝ → ℂ := fun x => (x : ℂ) + y * I
  let s : ℝ → ℂ := fun x => 1 + α + w x
  let f : ℝ → ℂ := fun x => (X : ℂ) ^ w x *
    (riemannZeta (s x) * ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-s x)))⁻¹ * (1 / (w x) ^ 2)
  let τ := α.im + y
  let Z := (1 + Real.log (K + 1) / c) * Real.exp (Real.log (K + 1) / 4)
  let M := X ^ u * conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ * Z / K ^ 2
  change IntervalIntegrable f volume (-b) u ∧ _
  have hab : -b ≤ u := by linarith
  have hKpos : 0 < K := by linarith
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hXne : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hXpos.ne'
  have hα1 : ‖α‖ ≤ 1 := by linarith
  have hαre := abs_le.mp (Complex.abs_re_le_norm α)
  have hαim := Complex.abs_im_le_norm α
  have hτupper : |τ| ≤ K + 1 := by
    calc
      |τ| ≤ |α.im| + |y| := abs_add_le _ _
      _ ≤ K + 1 := by rw [hy]; linarith
  have hτhigh : T ≤ |τ| := by
    have h := abs_sub (α.im + y) α.im
    have hybound : |y| ≤ |τ| + |α.im| := by simpa [τ] using h
    rw [hy] at hybound
    linarith
  have hτpos : 0 < |τ| := by linarith
  have hlogτ : 0 < Real.log |τ| := Real.log_pos (by linarith)
  have hlogK : 0 < Real.log (K + 1) := Real.log_pos (by linarith)
  have hlogs : Real.log |τ| ≤ Real.log (K + 1) := Real.log_le_log hτpos hτupper
  have hwidthτ : c / Real.log (K + 1) ≤ c / Real.log |τ| :=
    div_le_div_of_nonneg_left hc.le hlogτ hlogs
  have hreal (x : ℝ) (hx : x ∈ Icc (-b) u) : -2 * δ ≤ (α + w x).re := by
    simp only [w, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_self, add_zero]
    linarith [hx.1]
  have hZ (x : ℝ) (hx : x ∈ Icc (-b) u) :
      riemannZeta (s x) ≠ 0 ∧ ‖(riemannZeta (s x))⁻¹‖ ≤ Z := by
    have heq : (((1 + α.re + x : ℝ) : ℂ) + I * τ) = s x := by
      apply Complex.ext <;> simp [s, w, τ]
    have hs := hstrip (1 + α.re + x) τ hτhigh (by linarith [hx.1]) (by linarith [hx.2])
    rw [heq] at hs
    refine ⟨hs.1, hs.2.trans ?_⟩
    dsimp [Z]
    apply mul_le_mul
    · exact add_le_add le_rfl (div_le_div_of_nonneg_right hlogs hc.le)
    · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hlogs (by norm_num))
    · positivity
    · positivity
  have hwK (x : ℝ) : K ≤ ‖w x‖ := by
    simpa [w, hy] using Complex.abs_im_le_norm (w x)
  have hwne (x : ℝ) : w x ≠ 0 := norm_pos_iff.mp (hKpos.trans_le (hwK x))
  have hfeq : f = fun x => (X : ℂ) ^ w x * (riemannZeta (s x))⁻¹ *
      conreyCoprimeEulerInverse m (α + w x) * (1 / (w x) ^ 2) := by
    funext x
    simp only [f, conreyCoprimeEulerInverse, s, mul_inv_rev, ← add_assoc]
    ring
  have hcont : ContinuousOn f [[-b, u]] := by
    rw [hfeq]
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hs1 : s x ≠ 1 := by
      intro heq
      have hτzero : τ = 0 := by simpa [s, w, τ] using congrArg Complex.im heq
      rw [hτzero, abs_zero] at hτpos
      exact lt_irrefl 0 hτpos
    have hwcont : ContinuousAt w x := by dsimp [w]; fun_prop
    have hscont : ContinuousAt s x := by dsimp [s, w]; fun_prop
    have hshift : ContinuousAt (fun v => α + w v) x := continuousAt_const.add hwcont
    have hP : ContinuousAt (fun v => (X : ℂ) ^ w v) x :=
      (differentiable_id.const_cpow (Or.inl hXne)).continuous.continuousAt.comp hwcont
    have hZi : ContinuousAt (fun v => (riemannZeta (s v))⁻¹) x :=
      ((differentiableAt_riemannZeta hs1).continuousAt.inv₀ (hZ x hx).1).comp hscont
    have hE : ContinuousAt (fun v => conreyCoprimeEulerInverse m (α + w v)) x :=
      (analyticAt_conreyCoprimeEulerInverse m (by linarith [hreal x hx])).continuousAt.comp hshift
    have hkernel : ContinuousAt (fun v => (1 : ℂ) / (w v) ^ 2) x :=
      continuousAt_const.div (hwcont.pow 2) (pow_ne_zero 2 (hwne x))
    exact (((hP.mul hZi).mul hE).mul hkernel).continuousWithinAt
  have hC0 : 0 ≤ conreyEulerCorrectionConstant := zero_le_one.trans one_le_conreyEulerCorrectionConstant
  have hB0 := conreyCoprimeEulerMajorant_nonneg m δ
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hnorm (x : ℝ) (hx : x ∈ Icc (-b) u) : ‖f x‖ ≤ M := by
    have hP : ‖(X : ℂ) ^ w x‖ ≤ X ^ u := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
      exact Real.rpow_le_rpow_of_exponent_le hX (by simpa [w] using hx.2)
    have hE := norm_conreyCoprimeEulerInverse_le m hδ hδ16 (hreal x hx)
    have hkernel : ‖(1 : ℂ) / (w x) ^ 2‖ ≤ 1 / K ^ 2 := by
      simp only [norm_div, norm_one, norm_pow]
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hKpos)
      nlinarith [hwK x, norm_nonneg (w x)]
    calc
      ‖f x‖ = ‖(X : ℂ) ^ w x‖ * ‖(riemannZeta (s x))⁻¹‖ *
          ‖conreyCoprimeEulerInverse m (α + w x)‖ * ‖(1 : ℂ) / (w x) ^ 2‖ := by
        rw [hfeq]; simp only [norm_mul]
      _ ≤ X ^ u * Z * (conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ) *
          (1 / K ^ 2) := by
        gcongr
        exact (hZ x hx).2
      _ = M := by dsimp [M]; ring
  refine ⟨hcont.intervalIntegrable, ?_⟩
  change ‖∫ x in (-b)..u, f x‖ ≤ _
  calc
    _ ≤ M * |u - (-b)| := intervalIntegral.norm_integral_le_of_norm_le_const (by
      intro x hx
      have hx' := uIoc_subset_uIcc hx
      rw [uIcc_of_le hab] at hx'
      exact hnorm x hx')
    _ = _ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ u - (-b))]
      dsimp [M, Z]
      ring

end HardyTheorem
