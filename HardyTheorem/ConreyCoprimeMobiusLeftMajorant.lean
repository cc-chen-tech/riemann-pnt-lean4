import HardyTheorem.ConreyCoprimeMobiusHighRectangle
import HardyTheorem.ConreyCoprimeEulerBound

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace HardyTheorem

/-! Actual left-edge continuity and majorants. The low-height compact set
is fixed before the height, modulus and shift; the high estimate retains
an integrable power instead of taking a height-dependent supremum. -/

private theorem conrey_log_quarter_le_half {c v : ℝ} (hc : 0 < c) (hv : 1 ≤ v) :
    (1 + Real.log (v + 1) / c) * Real.exp (Real.log (v + 1) / 4) ≤
      2 * (1 + 4 / c) * v ^ (1 / 2 : ℝ) := by
  have hx : 0 < v + 1 := by linarith
  have hq : 1 ≤ (v + 1) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hl := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hlog : Real.log (v + 1) ≤ 4 * (v + 1) ^ (1 / 4 : ℝ) := by
    convert hl using 1
    ring
  have hhalf : (v + 1) ^ (1 / 2 : ℝ) ≤ 2 * v ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (4 * v) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hx.le (by linarith) (by norm_num)
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith), ← Real.sqrt_eq_rpow]; norm_num
  rw [show Real.exp (Real.log (v + 1) / 4) = (v + 1) ^ (1 / 4 : ℝ) by
    rw [Real.rpow_def_of_pos hx]; congr 1; ring]
  calc
    _ ≤ ((v + 1) ^ (1 / 4 : ℝ) + 4 * (v + 1) ^ (1 / 4 : ℝ) / c) *
        (v + 1) ^ (1 / 4 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
      exact add_le_add hq (div_le_div_of_nonneg_right hlog hc.le)
    _ = (1 + 4 / c) * (v + 1) ^ (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = 1 / 4 + 1 / 4 by norm_num, Real.rpow_add hx]
      ring
    _ ≤ (1 + 4 / c) * (2 * v ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = _ := by ring

/-- The literal Euler integrand has a logarithmic core and integrable
power tails. All four constants precede every varying parameter. -/
theorem exists_conrey_coprime_mobius_left_majorants :
    ∃ κ C D M : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ 0 < C ∧ 0 < D ∧ 3 ≤ M ∧
      ∀ (K : ℝ) (m : ℕ) (δ : ℝ) (α : ℂ) (X b : ℝ),
        M ≤ K → 0 ≤ δ → δ ≤ 1 / 16 → 0 < X → 0 < b → ‖α‖ < b →
        b + ‖α‖ ≤ 2 * δ → b + ‖α‖ ≤ κ / (1 + Real.log (K + 3)) →
        let f : ℝ → ℂ := fun t => (X : ℂ) ^ ((-b : ℂ) + t * I) *
          (riemannZeta (1 + α + ((-b : ℂ) + t * I)) *
            ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + ((-b : ℂ) + t * I)))))⁻¹ *
          (1 / ((-b : ℂ) + t * I) ^ 2)
        ContinuousOn f (Icc (-K) K) ∧
          (∀ t ∈ Icc (-M) M, ‖f t‖ ≤
            C * conreyCoprimeEulerMajorant m δ * X ^ (-b) / (b + |t|)) ∧
          (∀ t ∈ Icc (-K) K, M ≤ |t| → ‖f t‖ ≤
            D * conreyCoprimeEulerMajorant m δ * X ^ (-b) * |t| ^ (-3 / 2 : ℝ)) := by
  obtain ⟨κ₀, hκ₀, hκ₀4, hband⟩ := exists_conrey_coprime_mobius_analytic_rectangles
  obtain ⟨c, T, hc, hc1, hT, hstrip⟩ := exists_conrey_reciprocal_zeta_quarterPower_strip
  let M := max (T + 2) 3
  have hM3 : 3 ≤ M := le_max_right _ _
  have hMT : T + 2 ≤ M := le_max_left _ _
  let r := κ₀ / (1 + Real.log (M + 3))
  have hlogM : 0 < Real.log (M + 3) := Real.log_pos (by linarith)
  have hr4 : r ≤ 1 / 4 := (div_le_self hκ₀.le (by linarith)).trans hκ₀4
  let compactCore : Set ℂ := Icc (-r) 1 ×ℂ Icc (-(M + 1)) (M + 1)
  have hcompact : IsCompact compactCore := isCompact_Icc.reProdIm isCompact_Icc
  have hU : ContinuousOn conreyMobiusPoleUnit compactCore := by
    intro z hz
    change z ∈ Icc (-r) 1 ×ℂ Icc (-(M + 1)) (M + 1) at hz
    rw [mem_reProdIm] at hz
    have hQne := (hband (M + 1) 1 z (by linarith)
      (by simpa only [show M + 1 + 2 = M + 3 by ring] using hz.1.1)
      hz.1.2 (abs_le.mpr hz.2)).1
    have hQ := ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
      (θ := 0) le_rfl (1 + z) (by change 0 < (1 + z).re; simp only [add_re, one_re]; linarith [hz.1.1])
    exact ((hQ.comp (analyticAt_const.add analyticAt_id)).inv hQne).continuousAt.continuousWithinAt
  obtain ⟨U, hUbound⟩ := hcompact.exists_bound_of_continuousOn hU
  let C_U := max U 1
  have hCU : 0 < C_U := zero_lt_one.trans_le (le_max_right _ _)
  have hCUbound (z : ℂ) (hz : z ∈ compactCore) : ‖conreyMobiusPoleUnit z‖ ≤ C_U :=
    (hUbound z hz).trans (le_max_left _ _)
  let κ := min κ₀ c
  have hκ : 0 < κ := lt_min hκ₀ hc
  have hκ₀le : κ ≤ κ₀ := min_le_left _ _
  have hκc : κ ≤ c := min_le_right _ _
  have hC0 : 0 < conreyEulerCorrectionConstant :=
    zero_lt_one.trans_le one_le_conreyEulerCorrectionConstant
  refine ⟨κ, 4 * C_U * conreyEulerCorrectionConstant,
    2 * conreyEulerCorrectionConstant * (1 + 4 / c), M,
    hκ, hκ₀le.trans hκ₀4, by positivity, by positivity, hM3, ?_⟩
  intro K m δ α X b hK hδ hδ16 hX hb hαb hδwidth hwidth
  dsimp only
  let w : ℝ → ℂ := fun t => (-b : ℂ) + t * I
  let z : ℝ → ℂ := fun t => α + w t
  let f : ℝ → ℂ := fun t => (X : ℂ) ^ w t *
    (riemannZeta (1 + z t) *
      ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + z t))))⁻¹ * (1 / (w t) ^ 2)
  simp only [add_assoc]
  change ContinuousOn f (Icc (-K) K) ∧ _
  have hα1 : ‖α‖ ≤ 1 := by linarith [norm_nonneg α]
  have hαre := abs_le.mp (Complex.abs_re_le_norm α)
  have hαim := abs_le.mp (Complex.abs_im_le_norm α)
  have hre (t : ℝ) : (z t).re = α.re - b := by simp [z, w, sub_eq_add_neg]
  have him (t : ℝ) : (z t).im = α.im + t := by simp [z, w]
  have hzreal (t : ℝ) : -2 * δ ≤ (z t).re := by rw [hre]; linarith
  have hzneg (t : ℝ) : (z t).re < 0 := by rw [hre]; linarith
  have hzne (t : ℝ) : z t ≠ 0 := by intro he; simpa [he] using hzneg t
  have hzone (t : ℝ) : 1 + z t ≠ 0 :=
    Complex.ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith [hzreal t])
  have hwb (t : ℝ) : b ≤ ‖w t‖ := by
    simpa [w, abs_of_pos hb] using Complex.abs_re_le_norm (w t)
  have hwt (t : ℝ) : |t| ≤ ‖w t‖ := by simpa [w] using Complex.abs_im_le_norm (w t)
  have hwnorm (t : ℝ) : 0 < ‖w t‖ := hb.trans_le (hwb t)
  have hwne (t : ℝ) : w t ≠ 0 := norm_pos_iff.mp (hwnorm t)
  have hzsize (t : ℝ) : ‖z t‖ ≤ 2 * ‖w t‖ :=
    (norm_add_le α (w t)).trans (by linarith [hwb t])
  have hlogK : 0 < Real.log (K + 3) := Real.log_pos (by linarith)
  have hlogs : Real.log (M + 3) ≤ Real.log (K + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hwidth₀ : b + ‖α‖ ≤ κ₀ / (1 + Real.log (K + 3)) :=
    hwidth.trans (div_le_div_of_nonneg_right hκ₀le (by linarith))
  have hwidthr : b + ‖α‖ ≤ r := hwidth₀.trans
    (div_le_div_of_nonneg_left hκ₀.le (by linarith) (by linarith))
  have hgeom (t : ℝ) (ht : t ∈ Icc (-K) K) :
      -(κ₀ / (1 + Real.log (K + 3))) ≤ (z t).re ∧
        (z t).re ≤ 1 ∧ |(z t).im| ≤ K + 1 := by
    rw [hre, him]
    exact ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hregular : f = fun t => (X : ℂ) ^ w t *
      conreyCoprimeMobiusRegularized m (z t) * (1 / (w t) ^ 2) := by
    funext t
    rw [conreyCoprimeMobiusRegularized_eq_euler m (hzne t) (hzone t)]
  have hcont : ContinuousOn f (Icc (-K) K) := by
    rw [hregular]
    intro t ht
    have hg := hgeom t ht
    have hWa := (hband (K + 1) m (z t) (by linarith)
      (by simpa only [show K + 1 + 2 = K + 3 by ring] using hg.1) hg.2.1 hg.2.2).2
    have hwcont : ContinuousAt w t := by dsimp [w]; fun_prop
    have hzcont : ContinuousAt z t := continuousAt_const.add hwcont
    have hP : ContinuousAt (fun v => (X : ℂ) ^ w v) t :=
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).continuous.continuousAt.comp hwcont
    exact ((hP.mul (hWa.continuousAt.comp hzcont)).mul
      (continuousAt_const.div (hwcont.pow 2) (pow_ne_zero 2 (hwne t)))).continuousWithinAt
  have hB0 := conreyCoprimeEulerMajorant_nonneg m δ
  have hXP : 0 < X ^ (-b) := Real.rpow_pos_of_pos hX _
  have hP (t : ℝ) : ‖(X : ℂ) ^ w t‖ = X ^ (-b) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]; simp [w]
  have hE (t : ℝ) := norm_conreyCoprimeEulerInverse_le m hδ hδ16 (hzreal t)
  refine ⟨hcont, ?_, ?_⟩
  · intro t ht
    have hcore : z t ∈ compactCore := by
      change z t ∈ Icc (-r) 1 ×ℂ Icc (-(M + 1)) (M + 1)
      rw [mem_reProdIm, hre, him]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    have hWnorm : ‖conreyCoprimeMobiusRegularized m (z t)‖ ≤
        (2 * ‖w t‖) * C_U * (conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ) := by
      simp only [conreyCoprimeMobiusRegularized, norm_mul]
      gcongr
      · exact hzsize t
      · exact hCUbound (z t) hcore
      · exact hE t
    have hweight : 2 / ‖w t‖ ≤ 4 / (b + |t|) := by
      apply (div_le_div_iff₀ (hwnorm t) (by positivity)).mpr
      linarith [hwb t, hwt t]
    calc
      ‖f t‖ = X ^ (-b) * ‖conreyCoprimeMobiusRegularized m (z t)‖ / ‖w t‖ ^ 2 := by
        rw [hregular]; simp only [norm_mul, hP, norm_div, norm_one, norm_pow]; ring
      _ ≤ X ^ (-b) * ((2 * ‖w t‖) * C_U *
          (conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ)) / ‖w t‖ ^ 2 := by
        gcongr
      _ = (C_U * conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ * X ^ (-b)) *
          (2 / ‖w t‖) := by field_simp
      _ ≤ (C_U * conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ * X ^ (-b)) *
          (4 / (b + |t|)) := mul_le_mul_of_nonneg_left hweight (by positivity)
      _ = _ := by ring
  · intro t ht hhigh
    let v := |t|
    let τ := α.im + t
    have hv : 1 ≤ v := by change 1 ≤ |t|; linarith
    have hvpos : 0 < v := by linarith
    have hvK : v ≤ K := abs_le.mpr ht
    have hτupper : |τ| ≤ v + 1 := (abs_add_le α.im t).trans
      (by dsimp [v]; linarith [Complex.abs_im_le_norm α])
    have hτhigh : T ≤ |τ| := by
      have htbound : |t| ≤ |τ| + |α.im| := by simpa [τ] using abs_sub (α.im + t) α.im
      linarith [Complex.abs_im_le_norm α]
    have hτpos : 0 < |τ| := by linarith
    have hlogτ : 0 < Real.log |τ| := Real.log_pos (by linarith)
    have hlogv : 0 < Real.log (v + 1) := Real.log_pos (by linarith)
    have hlogτv : Real.log |τ| ≤ Real.log (v + 1) := Real.log_le_log hτpos hτupper
    have hlogτK : Real.log |τ| ≤ 1 + Real.log (K + 3) := by
      have hh := Real.log_le_log hτpos (by linarith : |τ| ≤ K + 3)
      linarith
    have hwidthτ : b + ‖α‖ ≤ c / Real.log |τ| := hwidth.trans
      ((div_le_div_of_nonneg_left hκ.le hlogτ hlogτK).trans
        (div_le_div_of_nonneg_right hκc hlogτ.le))
    have hZ : ‖(riemannZeta (1 + z t))⁻¹‖ ≤ 2 * (1 + 4 / c) * v ^ (1 / 2 : ℝ) := by
      have heq : (((1 + α.re - b : ℝ) : ℂ) + I * τ) = 1 + z t := by
        apply Complex.ext <;> simp [z, w, τ, sub_eq_add_neg, add_assoc]
      have hh := (hstrip (1 + α.re - b) τ hτhigh (by linarith) (by linarith)).2
      rw [heq] at hh
      apply hh.trans
      apply le_trans _ (conrey_log_quarter_le_half hc hv)
      apply mul_le_mul
      · exact add_le_add le_rfl (div_le_div_of_nonneg_right hlogτv hc.le)
      · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hlogτv (by norm_num))
      · positivity
      · positivity
    have hsplit : f t = (X : ℂ) ^ w t * (riemannZeta (1 + z t))⁻¹ *
        conreyCoprimeEulerInverse m (z t) * (1 / (w t) ^ 2) := by
      simp only [f, conreyCoprimeEulerInverse, mul_inv_rev]; ring
    have hkernel : ‖(1 : ℂ) / (w t) ^ 2‖ ≤ 1 / v ^ 2 := by
      simp only [norm_div, norm_one, norm_pow]
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hvpos)
      nlinarith [hwt t, norm_nonneg (w t)]
    calc
      ‖f t‖ = X ^ (-b) * ‖(riemannZeta (1 + z t))⁻¹‖ *
          ‖conreyCoprimeEulerInverse m (z t)‖ * ‖(1 : ℂ) / (w t) ^ 2‖ := by
        rw [hsplit]; simp only [norm_mul, hP]
      _ ≤ X ^ (-b) * (2 * (1 + 4 / c) * v ^ (1 / 2 : ℝ)) *
          (conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ) * (1 / v ^ 2) := by
        gcongr
        exact hE t
      _ = (2 * conreyEulerCorrectionConstant * (1 + 4 / c)) *
          conreyCoprimeEulerMajorant m δ * X ^ (-b) * (v ^ (1 / 2 : ℝ) / v ^ 2) := by ring
      _ = _ := by
        rw [← Real.rpow_sub_natCast hvpos.ne', show (1 / 2 : ℝ) - (2 : ℕ) = -3 / 2 by norm_num]

end HardyTheorem
