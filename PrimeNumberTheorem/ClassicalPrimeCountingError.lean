import PrimeNumberTheorem.ClassicalPNTError

open Filter Topology

namespace PrimeNumberTheorem

/-- The prime-power correction is absorbed into the de la Vallee Poussin
scale, transferring the proved `psi` remainder to Chebyshev's `theta`. -/
theorem exists_eventually_abs_chebyshevTheta_sub_id_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  rcases exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log with
    ⟨c, C, X, hc, hC, hpsi⟩
  let a : ℝ := c / 2
  have ha : 0 < a := div_pos hc (by norm_num)
  have hsqrtLogTop :
      Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hu : ∀ᶠ x : ℝ in atTop, 4 * a ≤ Real.sqrt (Real.log x) :=
    tendsto_atTop.1 hsqrtLogTop (4 * a)
  refine ⟨a, C + 8, ha, add_nonneg hC (by norm_num), ?_⟩
  filter_upwards [eventually_ge_atTop X,
      eventually_ge_atTop (Real.exp 1), hu] with x hxX hxexp hux
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxexp
  have hx0 : 0 ≤ x := hxpos.le
  have hx1 : 1 ≤ x := by
    have hone_exp : (1 : ℝ) ≤ Real.exp 1 := by
      rw [Real.one_le_exp_iff]
      norm_num
    exact hone_exp.trans hxexp
  have hlog1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).2 hxexp
  have hlog0 : 0 ≤ Real.log x := hlog1.trans' zero_le_one
  have hu0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have huSq : (Real.sqrt (Real.log x)) ^ 2 = Real.log x :=
    Real.sq_sqrt hlog0
  let scale : ℝ := x * Real.exp (-a * Real.sqrt (Real.log x))
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hexpWeak :
      Real.exp (-c * Real.sqrt (Real.log x)) ≤
        Real.exp (-a * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    nlinarith [mul_nonneg hc.le hu0]
  have hpsiWeak : |chebyshevPsi x - x| ≤ C * scale := by
    calc
      |chebyshevPsi x - x| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := hpsi x hxX
      _ ≤ C * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
        exact mul_le_mul_of_nonneg_left hexpWeak (mul_nonneg hC hx0)
      _ = C * scale := by simp [scale, mul_assoc]
  have hlogPow :
      Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
    Real.log_le_rpow_div hx0 (by norm_num)
  have hdiffPow :
      2 * Real.sqrt x * Real.log x ≤ 8 * x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      2 * x ^ (1 / 2 : ℝ) * Real.log x ≤
          2 * x ^ (1 / 2 : ℝ) *
            (x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogPow (by positivity)
      _ = 8 * x ^ (3 / 4 : ℝ) := by
        rw [show (3 / 4 : ℝ) = (1 / 2 : ℝ) + 1 / 4 by ring,
          Real.rpow_add hxpos]
        ring
  have hrpowScale : x ^ (3 / 4 : ℝ) ≤ scale := by
    have hmul := mul_le_mul_of_nonneg_right hux hu0
    have hexponent :
        Real.log x * (3 / 4 : ℝ) ≤
          Real.log x + (-a * Real.sqrt (Real.log x)) := by
      nlinarith [huSq]
    calc
      x ^ (3 / 4 : ℝ) =
          Real.exp (Real.log x * (3 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos hxpos]
      _ ≤ Real.exp (Real.log x + (-a * Real.sqrt (Real.log x))) :=
        Real.exp_le_exp.mpr hexponent
      _ = scale := by
        dsimp [scale]
        rw [Real.exp_add, Real.exp_log hxpos]
  have hdiffScale :
      |chebyshevPsi x - Chebyshev.theta x| ≤ 8 * scale := by
    have hdiff := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
    have hdiff' :
        |chebyshevPsi x - Chebyshev.theta x| ≤
          2 * Real.sqrt x * Real.log x := by
      simpa [chebyshevPsi_eq_mathlib] using hdiff
    exact hdiff'.trans (hdiffPow.trans
      (mul_le_mul_of_nonneg_left hrpowScale (by norm_num)))
  have hdecomp :
      Chebyshev.theta x - x =
        (chebyshevPsi x - x) + -(chebyshevPsi x - Chebyshev.theta x) := by
    ring
  calc
    |Chebyshev.theta x - x| =
        |(chebyshevPsi x - x) +
          -(chebyshevPsi x - Chebyshev.theta x)| := by rw [hdecomp]
    _ ≤ |chebyshevPsi x - x| +
        |-(chebyshevPsi x - Chebyshev.theta x)| := abs_add_le _ _
    _ ≤ C * scale + 8 * scale := by
      simpa only [abs_neg] using add_le_add hpsiWeak hdiffScale
    _ = (C + 8) * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
      dsimp [scale]
      ring

set_option maxHeartbeats 800000 in
/-- The Abel error integral preserves the de la Vallee Poussin decay shape.
The proof splits the variable interval at `sqrt x`; no asymptotic integration
interface is assumed. -/
theorem exists_eventually_abs_theta_error_integral_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  rcases exists_eventually_abs_chebyshevTheta_sub_id_le_exp_neg_sqrt_log with
    ⟨a, D, ha, hD, htheta⟩
  rcases eventually_atTop.1 htheta with ⟨A0, hthetaA0⟩
  let A : ℝ := max (max A0 (Real.exp 1)) 2
  let K : ℝ → ℝ := fun t =>
    (Chebyshev.theta t - t) / (t * Real.log t ^ 2)
  let I0 : ℝ := ∫ t in (2)..A, K t
  let b : ℝ := a / 4
  have hb : 0 < b := div_pos ha (by norm_num)
  have hA0 : A0 ≤ A :=
    (le_max_left A0 (Real.exp 1)).trans
      (le_max_left (max A0 (Real.exp 1)) 2)
  have hAexp : Real.exp 1 ≤ A :=
    (le_max_right A0 (Real.exp 1)).trans
      (le_max_left (max A0 (Real.exp 1)) 2)
  have hA2 : 2 ≤ A := le_max_right (max A0 (Real.exp 1)) 2
  have hApos : 0 < A := by linarith
  have hsqrtLogTop :
      Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hu : ∀ᶠ x : ℝ in atTop, 2 * b ≤ Real.sqrt (Real.log x) :=
    tendsto_atTop.1 hsqrtLogTop (2 * b)
  refine ⟨b, |I0| + 2 * D, hb,
    add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hD), ?_⟩
  filter_upwards [eventually_ge_atTop (A ^ 2),
      eventually_ge_atTop (4 : ℝ), hu] with x hxA2 hx4 hux
  have hxpos : 0 < x := by linarith
  have hx0 : 0 ≤ x := hxpos.le
  have hx1 : 1 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hu0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have huSq : (Real.sqrt (Real.log x)) ^ 2 = Real.log x :=
    Real.sq_sqrt hlog0
  have hsqrtx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrtxSq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
  have hsqrtx2 : 2 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0]
    nlinarith
  have hAsqrt : A ≤ Real.sqrt x := by
    rw [Real.le_sqrt hApos.le hx0]
    exact hxA2
  have hsqrtx_le_x : Real.sqrt x ≤ x := by
    nlinarith
  have hK_2A : IntervalIntegrable K MeasureTheory.volume 2 A := by
    dsimp [K]
    exact intervalIntegrable_theta_error_div_id_log_sq_of_le
      (a := 2) (b := A) (by norm_num) hA2
  have hK_Asqrt : IntervalIntegrable K MeasureTheory.volume A (Real.sqrt x) := by
    dsimp [K]
    exact intervalIntegrable_theta_error_div_id_log_sq_of_le hA2 hAsqrt
  have hK_sqrtx : IntervalIntegrable K MeasureTheory.volume (Real.sqrt x) x := by
    dsimp [K]
    exact intervalIntegrable_theta_error_div_id_log_sq_of_le hsqrtx2 hsqrtx_le_x
  have hsplitLeft :
      (∫ t in (2)..Real.sqrt x, K t) =
        I0 + ∫ t in A..Real.sqrt x, K t := by
    dsimp [I0]
    exact (intervalIntegral.integral_add_adjacent_intervals hK_2A hK_Asqrt).symm
  have hsplit :
      (∫ t in (2)..x, K t) =
        I0 + (∫ t in A..Real.sqrt x, K t) +
          ∫ t in Real.sqrt x..x, K t := by
    calc
      (∫ t in (2)..x, K t) =
          (∫ t in (2)..Real.sqrt x, K t) +
            ∫ t in Real.sqrt x..x, K t :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hK_2A.trans hK_Asqrt) hK_sqrtx).symm
      _ = I0 + (∫ t in A..Real.sqrt x, K t) +
          ∫ t in Real.sqrt x..x, K t := by rw [hsplitLeft]
  have hshort :
      |∫ t in A..Real.sqrt x, K t| ≤ D * Real.sqrt x := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := K) (a := A) (b := Real.sqrt x) (C := D) (fun t ht => by
        rw [Set.uIoc_of_le hAsqrt] at ht
        have htA : A ≤ t := ht.1.le
        have ht0 : 0 < t := lt_of_lt_of_le hApos htA
        have ht1 : 1 ≤ t := by linarith
        have hlogt1 : 1 ≤ Real.log t :=
          (Real.le_log_iff_exp_le ht0).2 (hAexp.trans htA)
        have hlogt0 : 0 ≤ Real.log t := by linarith
        have hlogtSq : 1 ≤ Real.log t ^ 2 := by nlinarith
        have hut0 : 0 ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
        have hexp1 : Real.exp (-a * Real.sqrt (Real.log t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hut0
        have hthetaT := hthetaA0 t (hA0.trans htA)
        have hdenPos : 0 < t * Real.log t ^ 2 :=
          mul_pos ht0 (sq_pos_of_pos (by linarith : 0 < Real.log t))
        have hcancel :
            (D * t * Real.exp (-a * Real.sqrt (Real.log t))) /
                (t * Real.log t ^ 2) =
              (D * Real.exp (-a * Real.sqrt (Real.log t))) /
                Real.log t ^ 2 := by
          field_simp [ht0.ne']
        rw [Real.norm_eq_abs]
        calc
          |K t| = |Chebyshev.theta t - t| /
              (t * Real.log t ^ 2) := by
            simp [K, abs_div, abs_of_pos hdenPos]
          _ ≤ (D * t * Real.exp (-a * Real.sqrt (Real.log t))) /
              (t * Real.log t ^ 2) :=
            div_le_div_of_nonneg_right hthetaT hdenPos.le
          _ = (D * Real.exp (-a * Real.sqrt (Real.log t))) /
              Real.log t ^ 2 := hcancel
          _ ≤ D / Real.log t ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_of_le_one_right hD hexp1) (sq_nonneg _)
          _ ≤ D / 1 :=
            div_le_div_of_nonneg_left hD zero_lt_one hlogtSq
          _ = D := div_one D)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hAsqrt)] at hbound
    calc
      |∫ t in A..Real.sqrt x, K t| ≤ D * (Real.sqrt x - A) := hbound
      _ ≤ D * Real.sqrt x := by nlinarith
  have htail :
      |∫ t in Real.sqrt x..x, K t| ≤
        D * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
    let tailBound : ℝ :=
      D * Real.exp (-(a / 2) * Real.sqrt (Real.log x))
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := K) (a := Real.sqrt x) (b := x) (C := tailBound) (fun t ht => by
        rw [Set.uIoc_of_le hsqrtx_le_x] at ht
        have htsqrt : Real.sqrt x ≤ t := ht.1.le
        have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 hxpos) htsqrt
        have htA : A ≤ t := hAsqrt.trans htsqrt
        have hlogt1 : 1 ≤ Real.log t :=
          (Real.le_log_iff_exp_le ht0).2 (hAexp.trans htA)
        have hlogtSq : 1 ≤ Real.log t ^ 2 := by nlinarith
        have hlogLower : Real.log x / 2 ≤ Real.log t := by
          rw [← Real.log_sqrt hx0]
          exact Real.log_le_log (Real.sqrt_pos.2 hxpos) htsqrt
        have hlogt0 : 0 ≤ Real.log t := by linarith
        have hsqrtLogLower :
            Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log t) := by
          have htSq := Real.sq_sqrt hlogt0
          have htSqrt0 := Real.sqrt_nonneg (Real.log t)
          nlinarith
        have hexpTail :
            Real.exp (-a * Real.sqrt (Real.log t)) ≤
              Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
          apply Real.exp_le_exp.mpr
          have hmul := mul_le_mul_of_nonneg_left hsqrtLogLower ha.le
          nlinarith
        have hthetaT := hthetaA0 t (hA0.trans htA)
        have hdenPos : 0 < t * Real.log t ^ 2 :=
          mul_pos ht0 (sq_pos_of_pos (by linarith : 0 < Real.log t))
        have hcancel :
            (D * t * Real.exp (-a * Real.sqrt (Real.log t))) /
                (t * Real.log t ^ 2) =
              (D * Real.exp (-a * Real.sqrt (Real.log t))) /
                Real.log t ^ 2 := by
          field_simp [ht0.ne']
        rw [Real.norm_eq_abs]
        calc
          |K t| = |Chebyshev.theta t - t| /
              (t * Real.log t ^ 2) := by
            simp [K, abs_div, abs_of_pos hdenPos]
          _ ≤ (D * t * Real.exp (-a * Real.sqrt (Real.log t))) /
              (t * Real.log t ^ 2) :=
            div_le_div_of_nonneg_right hthetaT hdenPos.le
          _ = (D * Real.exp (-a * Real.sqrt (Real.log t))) /
              Real.log t ^ 2 := hcancel
          _ ≤ D * Real.exp (-a * Real.sqrt (Real.log t)) := by
            have hnum0 :
                0 ≤ D * Real.exp (-a * Real.sqrt (Real.log t)) := by
              positivity
            simpa using div_le_self hnum0 hlogtSq
          _ ≤ tailBound := by
            dsimp [tailBound]
            exact mul_le_mul_of_nonneg_left hexpTail hD)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsqrtx_le_x)] at hbound
    calc
      |∫ t in Real.sqrt x..x, K t| ≤ tailBound * (x - Real.sqrt x) := hbound
      _ ≤ tailBound * x := by
        have htail0 : 0 ≤ tailBound := by
          dsimp [tailBound]
          positivity
        exact mul_le_mul_of_nonneg_left (by linarith) htail0
      _ = D * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
        dsimp [tailBound]
        ring
  let scale : ℝ := x * Real.exp (-b * Real.sqrt (Real.log x))
  have hscaleSqrt : Real.sqrt x ≤ scale := by
    have hmul := mul_le_mul_of_nonneg_right hux hu0
    have hexponent :
        Real.log x / 2 ≤ Real.log x + (-b * Real.sqrt (Real.log x)) := by
      nlinarith [huSq]
    calc
      Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
      _ = Real.exp (Real.log x * (1 / 2 : ℝ)) := by
        rw [Real.rpow_def_of_pos hxpos]
      _ ≤ Real.exp (Real.log x + (-b * Real.sqrt (Real.log x))) := by
        apply Real.exp_le_exp.mpr
        simpa [div_eq_mul_inv] using hexponent
      _ = scale := by
        dsimp [scale]
        rw [Real.exp_add, Real.exp_log hxpos]
  have hscaleOne : 1 ≤ scale := le_trans (by nlinarith : 1 ≤ Real.sqrt x) hscaleSqrt
  have hexpFinal :
      Real.exp (-(a / 2) * Real.sqrt (Real.log x)) ≤
        Real.exp (-b * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    dsimp [b]
    nlinarith [mul_nonneg ha.le hu0]
  have hinitScale : |I0| ≤ |I0| * scale := by
    nlinarith [abs_nonneg I0]
  have hshortScale :
      |∫ t in A..Real.sqrt x, K t| ≤ D * scale :=
    hshort.trans (mul_le_mul_of_nonneg_left hscaleSqrt hD)
  have htailScale :
      |∫ t in Real.sqrt x..x, K t| ≤ D * scale := by
    calc
      |∫ t in Real.sqrt x..x, K t| ≤
          D * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := htail
      _ ≤ D * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
        exact mul_le_mul_of_nonneg_left hexpFinal (mul_nonneg hD hx0)
      _ = D * scale := by simp [scale, mul_assoc]
  calc
    |∫ t in (2)..x,
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| =
        |I0 + (∫ t in A..Real.sqrt x, K t) +
          ∫ t in Real.sqrt x..x, K t| := by
      simpa only [K] using congrArg abs hsplit
    _ ≤ |I0| + |∫ t in A..Real.sqrt x, K t| +
        |∫ t in Real.sqrt x..x, K t| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |I0| * scale + D * scale + D * scale :=
      add_le_add (add_le_add hinitScale hshortScale) htailScale
    _ = (|I0| + 2 * D) * x *
        Real.exp (-b * Real.sqrt (Real.log x)) := by
      dsimp [scale]
      ring

/-- The exact Abel decomposition transfers the theta and integral estimates to
the classical de la Vallee Poussin-form remainder for `primeCounting - Li`. -/
theorem exists_eventually_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  rcases exists_eventually_abs_chebyshevTheta_sub_id_le_exp_neg_sqrt_log with
    ⟨a, A, ha, hA, htheta⟩
  rcases exists_eventually_abs_theta_error_integral_le_exp_neg_sqrt_log with
    ⟨b, B, hb, hB, hintegral⟩
  let c : ℝ := min a b
  let K0 : ℝ := 2 / Real.log 2
  have hc : 0 < c := lt_min ha hb
  have hca : c ≤ a := min_le_left a b
  have hcb : c ≤ b := min_le_right a b
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    positivity
  have hsqrtLogTop :
      Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hu : ∀ᶠ x : ℝ in atTop, c ≤ Real.sqrt (Real.log x) :=
    tendsto_atTop.1 hsqrtLogTop c
  refine ⟨c, A + B + K0, hc, add_nonneg (add_nonneg hA hB) hK0, ?_⟩
  filter_upwards [htheta, hintegral, eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (3 : ℝ), hu] with x hthetaX hintegralX hxexp hx3 hux
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxexp
  have hx0 : 0 ≤ x := hxpos.le
  have hx2 : 2 ≤ x := by linarith
  have hlog1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).2 hxexp
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hlogPos : 0 < Real.log x := by linarith
  have hu0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have huSq : (Real.sqrt (Real.log x)) ^ 2 = Real.log x :=
    Real.sq_sqrt hlog0
  let scale : ℝ := x * Real.exp (-c * Real.sqrt (Real.log x))
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hscaleOne : 1 ≤ scale := by
    have hmul := mul_le_mul_of_nonneg_right hux hu0
    have hexponent :
        0 ≤ Real.log x + (-c * Real.sqrt (Real.log x)) := by
      nlinarith [huSq]
    calc
      1 = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (Real.log x + (-c * Real.sqrt (Real.log x))) :=
        Real.exp_le_exp.mpr hexponent
      _ = scale := by
        dsimp [scale]
        rw [Real.exp_add, Real.exp_log hxpos]
  have hexpTheta :
      Real.exp (-a * Real.sqrt (Real.log x)) ≤
        Real.exp (-c * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hca hu0
    nlinarith
  have hexpIntegral :
      Real.exp (-b * Real.sqrt (Real.log x)) ≤
        Real.exp (-c * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hcb hu0
    nlinarith
  have hthetaWeak : |Chebyshev.theta x - x| ≤ A * scale := by
    calc
      |Chebyshev.theta x - x| ≤
          A * x * Real.exp (-a * Real.sqrt (Real.log x)) := hthetaX
      _ ≤ A * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        exact mul_le_mul_of_nonneg_left hexpTheta (mul_nonneg hA hx0)
      _ = A * scale := by simp [scale, mul_assoc]
  have hintegralWeak :
      |∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤ B * scale := by
    calc
      |∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
          B * x * Real.exp (-b * Real.sqrt (Real.log x)) := hintegralX
      _ ≤ B * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
        exact mul_le_mul_of_nonneg_left hexpIntegral (mul_nonneg hB hx0)
      _ = B * scale := by simp [scale, mul_assoc]
  have hendpoint :
      |(Chebyshev.theta x - x) / Real.log x| ≤ A * scale := by
    rw [abs_div, abs_of_pos hlogPos]
    calc
      |Chebyshev.theta x - x| / Real.log x ≤
          (A * scale) / Real.log x :=
        div_le_div_of_nonneg_right hthetaWeak hlog0
      _ ≤ A * scale := div_le_self (mul_nonneg hA hscale0) hlog1
  have hconst : |K0| ≤ K0 * scale := by
    rw [abs_of_nonneg hK0]
    nlinarith
  have hdecomp := primeCounting_sub_logIntegral_eq_theta_error_integral hx2
  calc
    |(primeCounting x : ℝ) - logIntegral x| =
        |(Chebyshev.theta x - x) / Real.log x +
          (∫ t in (2)..x,
            (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) + K0| := by
      rw [hdecomp]
    _ ≤ |(Chebyshev.theta x - x) / Real.log x| +
        |∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| + |K0| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ A * scale + B * scale + K0 * scale :=
      add_le_add (add_le_add hendpoint hintegralWeak) hconst
    _ = (A + B + K0) * x *
        Real.exp (-c * Real.sqrt (Real.log x)) := by
      dsimp [scale]
      ring

/-- Pointwise existential form of the unconditional classical prime-counting
remainder.  The constants are not asserted to be numerically explicit. -/
theorem exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  rcases exists_eventually_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log with
    ⟨c, C, hc, hC, hbound⟩
  rcases eventually_atTop.1 hbound with ⟨X, hX⟩
  exact ⟨c, C, X, hc, hC, hX⟩

end PrimeNumberTheorem
