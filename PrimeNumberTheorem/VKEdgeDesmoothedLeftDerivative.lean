import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicDynamicLeftHighPolylog

/-!
# Dynamic-left analytic disk for the desmoothed cubic contour

The center-line logarithmic-derivative estimate is not enough for oscillatory
integration by parts: a Cauchy estimate also needs a zero-free neighborhood.
This file supplies that neighborhood for the actual Riemann zeta function.
-/

namespace PrimeNumberTheorem

open Complex Metric
open ExplicitFormulaResidues

/-- At high height, a closed disk whose radius is half the dynamic positive
left boundary contains no zeta zero.  The extra factor in the chosen boundary
keeps the entire disk strictly to the left of the previously proved finite-
height zero barrier, while its real part remains in `(0, 1)`. -/
theorem exists_dynamicCubicLeftBoundary_zeroFree_closedBall :
    ∃ b T0 : ℝ, 0 < b ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 2 ∧
          ∀ t : ℝ, T0 + 1 ≤ |t| → |t| + 1 ≤ H →
            ∀ z ∈ closedBall ((a : ℂ) + I * t) (a / 2),
              riemannZeta z ≠ 0 := by
  rcases exists_dynamicCubicLeftBoundary_nontrivialZero_re_gt with
    ⟨b0, hb0, hleft⟩
  let b : ℝ := min (b0 / 2) (Real.log 10)
  let T0 : ℝ := 4
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hb : 0 < b := by
    dsimp [b]
    exact lt_min (by positivity) hlog10
  have hb_half : b ≤ b0 / 2 := by
    exact min_le_left _ _
  have hb_log10 : b ≤ Real.log 10 := by
    exact min_le_right _ _
  refine ⟨b, T0, hb, by norm_num, ?_⟩
  intro H hH
  have hH4 : 4 ≤ H := by simpa [T0] using hH
  have hlog : 0 < Real.log (H + 6) :=
    Real.log_pos (by linarith : (1 : ℝ) < H + 6)
  have hlog10H : Real.log 10 ≤ Real.log (H + 6) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  rcases hleft H hH4 with ⟨hboundaryPos, hzeroLeft⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  have ha : 0 < a := by
    dsimp [a, dynamicCubicLeftBoundary]
    positivity
  have haHalf : a ≤ 1 / 2 := by
    rw [show a = b / (2 * Real.log (H + 6)) by rfl,
      div_le_iff₀ (mul_pos (by norm_num) hlog)]
    nlinarith [hb_log10.trans hlog10H]
  have ha_le_boundary_half :
      a ≤ dynamicCubicLeftBoundary b0 H / 2 := by
    have hraw : b / (2 * Real.log (H + 6)) ≤
        (b0 / 2) / (2 * Real.log (H + 6)) := by
      gcongr
    dsimp [a, dynamicCubicLeftBoundary]
    calc
      b / (2 * Real.log (H + 6)) ≤
          (b0 / 2) / (2 * Real.log (H + 6)) := hraw
      _ = (b0 / (2 * Real.log (H + 6))) / 2 := by ring
  refine ⟨ha, haHalf, ?_⟩
  intro t _ht hHt z hz
  have hre := ZeroFreeRegion.closedBall_sigma_it_re_bounds
    (z := z) (σ := a) (t := t) (R := a / 2) hz
  have hzRePos : 0 < z.re := by linarith
  have hzReLtOne : z.re < 1 := by linarith
  have hdist : ‖z - ((a : ℂ) + I * t)‖ ≤ a / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have himDiff : |z.im - t| ≤ a / 2 := by
    have h := (ZeroFreeRegion.abs_im_sub_le_norm_sub
      z ((a : ℂ) + I * t)).trans hdist
    simpa using h
  have him : |z.im| ≤ H := by
    calc
      |z.im| = |t + (z.im - t)| := by ring_nf
      _ ≤ |t| + |z.im - t| := abs_add_le _ _
      _ ≤ |t| + a / 2 := by linarith
      _ ≤ H := by linarith
  intro hzeta
  have hzero : RiemannHypothesis.IsNontrivialZero z :=
    ⟨hzeta, hzRePos, hzReLtOne⟩
  have hzRight := hzeroLeft z hzero him
  have hzUpper : z.re ≤ 3 * a / 2 := by linarith
  have hgap : 3 * a / 2 < dynamicCubicLeftBoundary b0 H := by
    nlinarith
  exact (not_lt_of_ge hzUpper) (hgap.trans hzRight)

private theorem norm_logDeriv_riemannZeta_left_disk_point_le_outer_log_sq
    {C0 H : ℝ} {z : ℂ}
    (hC0 : 0 ≤ C0) (hH : 4 ≤ H)
    (hzRePos : 0 < z.re) (hzReHalf : z.re ≤ 1 / 2)
    (hzTwo : 2 ≤ |z.im|) (himUpper : |z.im| ≤ H)
    (hzeta : riemannZeta z ≠ 0)
    (hrightNonzero : riemannZeta (1 - z) ≠ 0)
    (hrightBound : ‖logDeriv riemannZeta (1 - z)‖ ≤
      C0 * (Real.log |z.im|) ^ 2) :
    ‖logDeriv riemannZeta z‖ ≤
      (C0 + (‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4) + Real.pi) + 2) *
          (1 + Real.log (H + 6)) ^ 2 := by
  have hzdecomp : ((z.re : ℂ) + I * z.im) = z :=
    ZeroFreeRegion.re_im_decomp z
  have hleftBound := norm_logDeriv_riemannZeta_central_left_le
    (K := C0 * (Real.log |z.im|) ^ 2) hzReHalf hzTwo
    (by rw [hzdecomp]; exact hzeta)
    (by rw [hzdecomp]; exact hrightNonzero)
    (by rw [hzdecomp]; exact hrightBound)
  rw [hzdecomp] at hleftBound
  let A : ℝ := ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4) + Real.pi
  let LH : ℝ := Real.log (H + 6)
  let L : ℝ := 1 + LH
  have hLH : 0 ≤ LH := by
    dsimp [LH]
    exact Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLnonneg : 0 ≤ L := zero_le_one.trans hL
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hlogzPos : 0 < Real.log |z.im| :=
    ZeroFreeRegion.log_abs_pos_of_two_le hzTwo
  have hlogzH : Real.log |z.im| ≤ LH := by
    dsimp [LH]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlogzSq : (Real.log |z.im|) ^ 2 ≤ L ^ 2 := by
    have hle : Real.log |z.im| ≤ L := by dsimp [L]; linarith
    exact (sq_le_sq₀ hlogzPos.le hLnonneg).2 hle
  have hsNorm : ‖z‖ ≤ 1 / 2 + H := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ = z.re + |z.im| := by rw [abs_of_pos hzRePos]
      _ ≤ 1 / 2 + H := add_le_add hzReHalf himUpper
  have harg1 : ‖(1 - z) / 2 + 1‖ + 1 ≤ H + 6 := by
    calc
      ‖(1 - z) / 2 + 1‖ + 1 ≤
          (‖(1 - z) / 2‖ + ‖(1 : ℂ)‖) + 1 :=
        by gcongr; exact norm_add_le _ _
      _ = ‖1 - z‖ / 2 + 2 := by rw [norm_div]; norm_num; ring
      _ ≤ (1 + ‖z‖) / 2 + 2 := by
        have hsub : ‖1 - z‖ ≤ 1 + ‖z‖ := by
          simpa using (norm_sub_le (1 : ℂ) z)
        nlinarith
      _ ≤ H + 6 := by nlinarith [hsNorm]
  have harg2 : ‖1 - z / 2 + 1‖ + 1 ≤ H + 6 := by
    calc
      ‖1 - z / 2 + 1‖ + 1 = ‖(2 : ℂ) - z / 2‖ + 1 := by ring_nf
      _ ≤ (‖(2 : ℂ)‖ + ‖z / 2‖) + 1 :=
        by gcongr; exact norm_sub_le _ _
      _ = 3 + ‖z‖ / 2 := by rw [norm_div]; norm_num; ring
      _ ≤ H + 6 := by nlinarith [hsNorm]
  have hlog1 : Real.log (‖(1 - z) / 2 + 1‖ + 1) ≤ L := by
    have hpos : 0 < ‖(1 - z) / 2 + 1‖ + 1 := by positivity
    have := Real.log_le_log hpos harg1
    dsimp [L, LH]
    linarith
  have hlog2 : Real.log (‖1 - z / 2 + 1‖ + 1) ≤ L := by
    have hpos : 0 < ‖1 - z / 2 + 1‖ + 1 := by positivity
    have := Real.log_le_log hpos harg2
    dsimp [L, LH]
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmain : C0 * (Real.log |z.im|) ^ 2 ≤ C0 * L ^ 2 :=
    mul_le_mul_of_nonneg_left hlogzSq hC0
  have hAL : A ≤ A * L ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left hLsq hA
  have htwoL : 2 * L ≤ 2 * L ^ 2 := by nlinarith
  refine hleftBound.trans ?_
  change
    C0 * (Real.log |z.im|) ^ 2 + ‖Complex.log Real.pi‖ +
          (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
            Real.log (‖(1 - z) / 2 + 1‖ + 1)) +
        (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖1 - z / 2 + 1‖ + 1)) + Real.pi
      ≤ (C0 + A + 2) * L ^ 2
  dsimp [A]
  nlinarith

/-- The actual logarithmic derivative is uniformly square-logarithmic on the
same dynamic-left disk.  The disk is chosen slightly narrower so every point
has real part at most `1/2`; reflection then puts the whole disk inside the
proved inner zero-free region on the right. -/
theorem exists_dynamicCubicLeftBoundary_closedBall_logDeriv_le_log_sq :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 3 ∧
          ∀ t : ℝ, T0 + 1 ≤ |t| → |t| + 1 ≤ H →
            ∀ z ∈ closedBall ((a : ℂ) + I * t) (a / 2),
              z ≠ 1 ∧ riemannZeta z ≠ 0 ∧
                ‖logDeriv riemannZeta z‖ ≤
                  C * (1 + Real.log (H + 6)) ^ 2 := by
  rcases exists_dynamicCubicLeftBoundary_nontrivialZero_re_gt with
    ⟨b0, hb0, hleft⟩
  rcases
      ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion
    with ⟨c, C0, T1, hc, hC0, hT1, hright⟩
  let b : ℝ := min (b0 / 2) (min (2 * c / 3) (2 * Real.log 10 / 3))
  let T0 : ℝ := max 4 T1
  let A : ℝ := ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4) + Real.pi
  let C : ℝ := C0 + A + 2
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hb : 0 < b := by
    dsimp [b]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hb_half : b ≤ b0 / 2 := min_le_left _ _
  have hb_c : b ≤ 2 * c / 3 :=
    (min_le_right (b0 / 2) _).trans (min_le_left _ _)
  have hb_log10 : b ≤ 2 * Real.log 10 / 3 :=
    (min_le_right (b0 / 2) _).trans (min_le_right _ _)
  have hT0 : 4 ≤ T0 := le_max_left _ _
  have hT1T0 : T1 ≤ T0 := le_max_right _ _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨b, C, T0, hb, hC, hT0, ?_⟩
  intro H hH
  have hH4 : 4 ≤ H := hT0.trans hH
  have hlog : 0 < Real.log (H + 6) :=
    Real.log_pos (by linarith : (1 : ℝ) < H + 6)
  have hlog10H : Real.log 10 ≤ Real.log (H + 6) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  rcases hleft H hH4 with ⟨hboundaryPos, hzeroLeft⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  have ha : 0 < a := by
    dsimp [a, dynamicCubicLeftBoundary]
    positivity
  have haThird : a ≤ 1 / 3 := by
    rw [show a = b / (2 * Real.log (H + 6)) by rfl,
      div_le_iff₀ (mul_pos (by norm_num) hlog)]
    nlinarith [hb_log10, hlog10H]
  have ha_le_boundary_half :
      a ≤ dynamicCubicLeftBoundary b0 H / 2 := by
    have hraw : b / (2 * Real.log (H + 6)) ≤
        (b0 / 2) / (2 * Real.log (H + 6)) := by
      gcongr
    dsimp [a, dynamicCubicLeftBoundary]
    calc
      b / (2 * Real.log (H + 6)) ≤
          (b0 / 2) / (2 * Real.log (H + 6)) := hraw
      _ = (b0 / (2 * Real.log (H + 6))) / 2 := by ring
  have ha_le_c_third : a ≤ c / (3 * Real.log (H + 6)) := by
    rw [show a = b / (2 * Real.log (H + 6)) by rfl]
    have hraw : b / (2 * Real.log (H + 6)) ≤
        (2 * c / 3) / (2 * Real.log (H + 6)) := by
      gcongr
    calc
      b / (2 * Real.log (H + 6)) ≤
          (2 * c / 3) / (2 * Real.log (H + 6)) := hraw
      _ = c / (3 * Real.log (H + 6)) := by ring
  refine ⟨ha, haThird, ?_⟩
  intro t ht hHt z hz
  have hre := ZeroFreeRegion.closedBall_sigma_it_re_bounds
    (z := z) (σ := a) (t := t) (R := a / 2) hz
  have hzRePos : 0 < z.re := by linarith
  have hzReHalf : z.re ≤ 1 / 2 := by linarith
  have hdist : ‖z - ((a : ℂ) + I * t)‖ ≤ a / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have himDiff : |z.im - t| ≤ a / 2 := by
    have h := (ZeroFreeRegion.abs_im_sub_le_norm_sub
      z ((a : ℂ) + I * t)).trans hdist
    simpa using h
  have himUpper : |z.im| ≤ H := by
    calc
      |z.im| = |t + (z.im - t)| := by ring_nf
      _ ≤ |t| + |z.im - t| := abs_add_le _ _
      _ ≤ |t| + a / 2 := by linarith
      _ ≤ H := by linarith
  have himLower0 := ZeroFreeRegion.closedBall_abs_im_lower
    (z := z) (c := ((a : ℂ) + I * t)) (R := a / 2) hz
  have himLower : T0 ≤ |z.im| := by
    have : |t| - a / 2 ≤ |z.im| := by simpa using himLower0
    linarith
  have hT1z : T1 ≤ |z.im| := hT1T0.trans himLower
  have hzTwo : 2 ≤ |z.im| := hT1.trans hT1z
  have hzNeOne : z ≠ 1 := by
    intro hz1
    subst z
    norm_num at hzTwo
  have hzeta : riemannZeta z ≠ 0 := by
    intro hzeta0
    have hzero : RiemannHypothesis.IsNontrivialZero z := by
      refine ⟨hzeta0, hzRePos, ?_⟩
      linarith
    have hzRight := hzeroLeft z hzero himUpper
    have hzUpper : z.re ≤ 3 * a / 2 := by linarith
    have hgap : 3 * a / 2 < dynamicCubicLeftBoundary b0 H := by
      nlinarith
    exact (not_lt_of_ge hzUpper) (hgap.trans hzRight)
  have hlogzPos : 0 < Real.log |z.im| :=
    ZeroFreeRegion.log_abs_pos_of_two_le hzTwo
  have hlogzH : Real.log |z.im| ≤ Real.log (H + 6) := by
    exact Real.log_le_log (by positivity) (by linarith)
  have hzReInner : z.re ≤ c / (2 * Real.log |z.im|) := by
    have hfirst : z.re ≤ c / (2 * Real.log (H + 6)) := by
      calc
        z.re ≤ 3 * a / 2 := by linarith
        _ ≤ 3 * (c / (3 * Real.log (H + 6))) / 2 := by gcongr
        _ = c / (2 * Real.log (H + 6)) := by ring
    exact hfirst.trans (div_le_div_of_nonneg_left hc.le
      (mul_pos (by norm_num) hlogzPos) (by nlinarith))
  have hright0 := hright (1 - z.re) (-z.im) (by simpa using hT1z)
    (by
      have : 1 - c / (2 * Real.log |z.im|) ≤ 1 - z.re := by linarith
      simpa [abs_neg] using this)
    (by linarith)
  have hreflect : (((1 - z.re : ℝ) : ℂ) + I * (-z.im)) = 1 - z := by
    apply Complex.ext <;> simp
  have hrightNonzero : riemannZeta (1 - z) ≠ 0 := by
    rw [← hreflect]
    simpa using hright0.1
  have hrightBound : ‖logDeriv riemannZeta (1 - z)‖ ≤
      C0 * (Real.log |z.im|) ^ 2 := by
    rw [← hreflect]
    simpa using hright0.2
  refine ⟨hzNeOne, hzeta, ?_⟩
  simpa [C, A] using
    norm_logDeriv_riemannZeta_left_disk_point_le_outer_log_sq
      hC0 hH4 hzRePos hzReHalf hzTwo himUpper hzeta
      hrightNonzero hrightBound

/-- Cauchy's estimate on the dynamic zero-free disk gives the derivative of
the actual zeta logarithmic derivative one additional logarithmic loss. -/
theorem exists_dynamicCubicLeftBoundary_deriv_logDeriv_le_log_cube :
    ∃ b D T0 : ℝ, 0 < b ∧ 0 ≤ D ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 3 ∧
          ∀ t : ℝ, T0 + 1 ≤ |t| → |t| + 1 ≤ H →
            ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤
              D * (1 + Real.log (H + 6)) ^ 3 := by
  rcases exists_dynamicCubicLeftBoundary_closedBall_logDeriv_le_log_sq with
    ⟨b, C, T0, hb, hC, hT0, hbase⟩
  let D : ℝ := 4 * C / b
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨b, D, T0, hb, hD, hT0, ?_⟩
  intro H hH
  rcases hbase H hH with ⟨ha, haThird, hpoint⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  refine ⟨ha, haThird, ?_⟩
  intro t ht hHt
  let center : ℂ := (a : ℂ) + I * t
  let R : ℝ := a / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have han : ∀ z ∈ closedBall center R,
      AnalyticAt ℂ (logDeriv riemannZeta) z := by
    intro z hz
    rcases hpoint t ht hHt z (by simpa [center, R] using hz) with
      ⟨hz1, hzeta, _⟩
    exact ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
      z hz1 hzeta
  have hdiffClosed : DifferentiableOn ℂ (logDeriv riemannZeta)
      (closedBall center R) := by
    intro z hz
    exact (han z hz).differentiableAt.differentiableWithinAt
  have hdiff : DiffContOnCl ℂ (logDeriv riemannZeta) (ball center R) :=
    hdiffClosed.diffContOnCl_ball subset_rfl
  have hnorm : ∀ z ∈ sphere center R,
      ‖logDeriv riemannZeta z‖ ≤
        C * (1 + Real.log (H + 6)) ^ 2 := by
    intro z hz
    exact (hpoint t ht hHt z (by
      simpa [center, R] using Metric.sphere_subset_closedBall hz)).2.2
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hR hdiff hnorm
  have hlog : 0 < Real.log (H + 6) :=
    Real.log_pos (by linarith [hT0.trans hH] : (1 : ℝ) < H + 6)
  let LH : ℝ := Real.log (H + 6)
  let L : ℝ := 1 + LH
  have hLH : 0 ≤ LH := by dsimp [LH]; exact hlog.le
  have hL : LH ≤ L := by dsimp [L]; linarith
  calc
    ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖
        = ‖deriv (logDeriv riemannZeta) center‖ := by rfl
    _ ≤ C * L ^ 2 / R := by simpa [L, LH] using hcauchy
    _ = D * LH * L ^ 2 := by
      dsimp [R, a, dynamicCubicLeftBoundary, D, LH]
      field_simp [hb.ne', hlog.ne']
      ring
    _ ≤ D * L * L ^ 2 := by gcongr
    _ = D * L ^ 3 := by ring
    _ = D * (1 + Real.log (H + 6)) ^ 3 := by rfl

end PrimeNumberTheorem
