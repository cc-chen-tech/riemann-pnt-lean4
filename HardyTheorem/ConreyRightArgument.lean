import HardyTheorem.ConreyHorizontalJensenAsymptotic
import PrimeNumberTheorem.LittlewoodRectangle

/-!
# The far-right argument variation in Conrey's equation (37)

The actual explicit product stays in the open right half-plane on the entire
moving vertical edge.  The principal logarithm therefore supplies one global
argument branch, reducing the real logarithmic-derivative integral to two
endpoint arguments.
-/

open Complex Set MeasureTheory
open scoped Interval

namespace HardyTheorem

/-- Low on the moving edge, the complete product remains close to the
positive constant `49/100`, not merely close in norm. -/
theorem norm_conreyExplicitRightVerticalProduct_sub_const_low_le_one_twentieth
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ht : 1 ≤ t)
    (htop : t ≤ 2 * Real.log L) :
    ‖conreyExplicitRightVerticalProduct Y sigma0 L t - (49 / 100 : ℂ)‖ ≤
      1 / 20 := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hLexp1 : Real.exp 1 ≤ L :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hLexp2
  let s : ℂ := ((2 * Real.log L : ℝ) : ℂ) + I * t
  let V : ℂ := conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L s
  let B : ℂ := conreyMollifier Y sigma0 conreyExplicitP s
  have hV : ‖V - (49 / 100 : ℂ)‖ ≤ 1 / 50 := by
    simpa only [V, s] using norm_conreyExplicitV1_sub_const_low_le hL ht htop
  have hB : ‖B - 1‖ ≤ 3 / L := by
    dsimp [B, s]
    convert norm_conreyExplicitMollifier_movingRight_sub_one_le
      hY hsigma0 hLexp1 t using 1
    push_cast
    rfl
  have hBnorm : ‖B‖ ≤ 2 := by
    calc
      ‖B‖ = ‖(B - 1) + 1‖ := by ring_nf
      _ ≤ ‖B - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 / L + 1 := by simpa using add_le_add_right hB 1
      _ ≤ 2 := by
        have : 3 / L ≤ 1 := (div_le_one hLpos).mpr (by linarith)
        linarith
  change ‖V * B - (49 / 100 : ℂ)‖ ≤ 1 / 20
  rw [show V * B - (49 / 100 : ℂ) =
      (V - (49 / 100 : ℂ)) * B + (49 / 100 : ℂ) * (B - 1) by ring]
  calc
    _ ≤ ‖V - (49 / 100 : ℂ)‖ * ‖B‖ +
        ‖(49 / 100 : ℂ)‖ * ‖B - 1‖ := by
      simpa only [norm_mul] using
        norm_add_le ((V - (49 / 100 : ℂ)) * B)
          ((49 / 100 : ℂ) * (B - 1))
    _ ≤ (1 / 50 : ℝ) * 2 + (49 / 100 : ℝ) * (3 / L) := by
      have hleft := mul_le_mul hV hBnorm (norm_nonneg B)
        (by norm_num : (0 : ℝ) ≤ 1 / 50)
      have hright := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 49 / 100)
      have hconst : ‖(49 / 100 : ℂ)‖ = (49 / 100 : ℝ) := by norm_num
      rw [hconst]
      exact add_le_add hleft hright
    _ ≤ 1 / 20 := by
      field_simp [hLpos.ne']
      nlinarith

/-- The complete product lies well inside the right half-plane on the low
part of the moving edge. -/
theorem two_fifths_le_conreyExplicitRightVerticalProduct_low_re
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ht : 1 ≤ t)
    (htop : t ≤ 2 * Real.log L) :
    (2 / 5 : ℝ) ≤ (conreyExplicitRightVerticalProduct Y sigma0 L t).re := by
  have hnorm :=
    norm_conreyExplicitRightVerticalProduct_sub_const_low_le_one_twentieth
      hY hsigma0 hL ht htop
  have hre := Complex.abs_re_le_norm
    (conreyExplicitRightVerticalProduct Y sigma0 L t - (49 / 100 : ℂ))
  have habs :
      |(conreyExplicitRightVerticalProduct Y sigma0 L t).re - 49 / 100| ≤
        1 / 20 := by
    norm_num at hre ⊢
    exact hre.trans hnorm
  nlinarith [neg_le_of_abs_le habs]

/-- The height-dependent main term gives a uniform right-half-plane margin
on the high part. -/
theorem three_tenths_le_conreyExplicitRightVerticalProduct_high_re
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ht : 2 * Real.log L ≤ t)
    (htop : t ≤ Real.exp L) :
    (3 / 10 : ℝ) ≤ (conreyExplicitRightVerticalProduct Y sigma0 L t).re := by
  have hLpos : 0 < L := by linarith
  have hLexp2 : Real.exp 2 ≤ L := by
    have h := Real.exp_le_exp.mpr (two_le_log_of_forty_thousand_le hL)
    simpa [Real.exp_log hLpos] using h
  have hmain := one_third_le_conreyExplicitDegreeOneHeightMain_re
    hLexp2 (by
      have := two_le_log_of_forty_thousand_le hL
      linarith : 1 ≤ t)
  have herr := norm_conreyExplicitRightVerticalProduct_sub_heightMain_le
    hY hsigma0 (by linarith) ht htop
  have hre := Complex.abs_re_le_norm
    (conreyExplicitRightVerticalProduct Y sigma0 L t -
      conreyExplicitDegreeOneHeightMain L t)
  simp only [Complex.sub_re] at hre
  have hsmall : (79 / L : ℝ) ≤ 1 / 30 := by
    apply (div_le_iff₀ (by linarith : 0 < L)).2
    nlinarith
  nlinarith [neg_le_of_abs_le hre]

/-- Uniform positivity on the whole global moving right edge. -/
theorem three_tenths_le_conreyExplicitRightVerticalProduct_global_re
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ht : 1 ≤ t)
    (htop : t ≤ Real.exp L) :
    (3 / 10 : ℝ) ≤ (conreyExplicitRightVerticalProduct Y sigma0 L t).re := by
  rcases le_total t (2 * Real.log L) with hlow | hhigh
  · exact (by
      have := two_fifths_le_conreyExplicitRightVerticalProduct_low_re
        hY hsigma0 hL ht hlow
      linarith)
  · exact three_tenths_le_conreyExplicitRightVerticalProduct_high_re
      hY hsigma0 hL hhigh htop

/-- The analytic function whose restriction to the moving line is the
explicit right-vertical product. -/
noncomputable def conreyExplicitRightVerticalFunction
    (Y : ℕ) (sigma0 L : ℝ) : ℂ → ℂ :=
  conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma0
    conreyExplicitP

@[simp] theorem conreyExplicitRightVerticalFunction_apply
    (Y : ℕ) (sigma0 L t : ℝ) :
    conreyExplicitRightVerticalFunction Y sigma0 L
        (((2 * Real.log L : ℝ) : ℂ) + I * t) =
      conreyExplicitRightVerticalProduct Y sigma0 L t := by
  rfl

/-- Analyticity of the actual product at every point of the moving right
line; no nonvanishing assumption is used here. -/
theorem analyticAt_conreyExplicitRightVerticalFunction
    {Y : ℕ} {sigma0 L t : ℝ} (hL : 40000 ≤ L) :
    AnalyticAt ℂ (conreyExplicitRightVerticalFunction Y sigma0 L)
      (((2 * Real.log L : ℝ) : ℂ) + I * t) := by
  have hlog := two_le_log_of_forty_thousand_le hL
  have hsre : 0 < ((((2 * Real.log L : ℝ) : ℂ) + I * t)).re := by
    simp
    linarith
  have hsne : (((2 * Real.log L : ℝ) : ℂ) + I * t) ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have hV := analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
    (g := (49 / 100 : ℝ)) (g0 := 0) (g1 := (51 / 50 : ℝ))
    (L := L) hsre hsne
  have hB := analyticOnNhd_conreyMollifier Y sigma0 conreyExplicitP
    (((2 * Real.log L : ℝ) : ℂ) + I * t) (by simp)
  unfold conreyExplicitRightVerticalFunction conreyMollifiedDegreeOneV1
  exact hV.mul hB

/-- Exact endpoint formula for the far-right argument variation. -/
theorem intervalIntegral_re_logDeriv_conreyExplicitRightVertical_eq_arg_sub
    {Y : ℕ} {sigma0 L a b : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ Real.exp L) :
    (∫ t in a..b,
        (logDeriv (conreyExplicitRightVerticalFunction Y sigma0 L)
          (((2 * Real.log L : ℝ) : ℂ) + I * t)).re) =
      (conreyExplicitRightVerticalProduct Y sigma0 L b).arg -
        (conreyExplicitRightVerticalProduct Y sigma0 L a).arg := by
  let f := conreyExplicitRightVerticalFunction Y sigma0 L
  let A := 2 * Real.log L
  have hpoint : ∀ t ∈ Set.uIcc a b,
      1 ≤ t ∧ t ≤ Real.exp L := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hanalytic : ∀ t ∈ Set.uIcc a b,
      AnalyticAt ℂ f (((A : ℝ) : ℂ) + I * t) := by
    intro t _ht
    simpa [f, A] using
      (analyticAt_conreyExplicitRightVerticalFunction
        (Y := Y) (sigma0 := sigma0) (t := t) hL)
  have hslit : ∀ t ∈ Set.uIcc a b,
      f (((A : ℝ) : ℂ) + I * t) ∈ Complex.slitPlane := by
    intro t ht
    have htBounds := hpoint t ht
    rw [Complex.mem_slitPlane_iff]
    left
    have hre := three_tenths_le_conreyExplicitRightVerticalProduct_global_re
      hY hsigma0 hL htBounds.1 htBounds.2
    change 0 < (conreyExplicitRightVerticalProduct Y sigma0 L t).re
    linarith
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt
        (fun u : ℝ =>
          (Complex.log (f (((A : ℝ) : ℂ) + I * u))).im)
        (logDeriv f (((A : ℝ) : ℂ) + I * t)).re t := by
    intro t ht
    exact PrimeNumberTheorem.CarlsonZeroDensity.hasDerivAt_im_log_vertical_of_analyticAt
      (hanalytic t ht) (hslit t ht)
  have hcont : ContinuousOn
      (fun t : ℝ =>
        (logDeriv f (((A : ℝ) : ℂ) + I * t)).re)
      (Set.uIcc a b) := by
    intro t ht
    have hmap : ContinuousAt
        (fun u : ℝ => ((A : ℝ) : ℂ) + I * u) t := by fun_prop
    have hne : f (((A : ℝ) : ℂ) + I * t) ≠ 0 :=
      Complex.slitPlane_ne_zero (hslit t ht)
    have hlog : ContinuousAt
        (fun u : ℝ => logDeriv f (((A : ℝ) : ℂ) + I * u)) t := by
      simpa [Function.comp_def] using
        ((ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
          (hanalytic t ht) hne).continuousAt.comp_of_eq hmap rfl)
    exact (Complex.continuous_re.continuousAt.comp hlog).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hcont.intervalIntegrable
  simpa only [f, A, Complex.log_im,
    conreyExplicitRightVerticalFunction_apply] using hFTC

/-- The whole far-right argument variation costs at most one `pi`, uniformly
in the height interval. -/
theorem abs_intervalIntegral_re_logDeriv_conreyExplicitRightVertical_le_pi
    {Y : ℕ} {sigma0 L a b : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ Real.exp L) :
    |∫ t in a..b,
        (logDeriv (conreyExplicitRightVerticalFunction Y sigma0 L)
          (((2 * Real.log L : ℝ) : ℂ) + I * t)).re| ≤ Real.pi := by
  rw [intervalIntegral_re_logDeriv_conreyExplicitRightVertical_eq_arg_sub
    hY hsigma0 hL ha hab hb]
  have hrea := three_tenths_le_conreyExplicitRightVerticalProduct_global_re
    hY hsigma0 hL ha (hab.trans hb)
  have hreb := three_tenths_le_conreyExplicitRightVerticalProduct_global_re
    hY hsigma0 hL (ha.trans hab) hb
  have harga : |(conreyExplicitRightVerticalProduct Y sigma0 L a).arg| ≤
      Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr (by linarith)
  have hargb : |(conreyExplicitRightVerticalProduct Y sigma0 L b).arg| ≤
      Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr (by linarith)
  exact (abs_sub _ _).trans (by linarith)

end HardyTheorem
