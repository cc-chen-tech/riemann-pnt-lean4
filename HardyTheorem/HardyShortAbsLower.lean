import HardyTheorem.CriticalLineShortDirichlet
import HardyTheorem.ShortIntervalMeanValue

open Complex Filter MeasureTheory Set

namespace HardyTheorem

/-- The constant term in the first zeta approximation gives a pointwise lower
bound for the absolute Hardy mass of a short interval.  The only oscillatory
loss is the integrated nonconstant Dirichlet polynomial; the analytic
remainder is uniformly `O(delta / sqrt T)`. -/
theorem exists_hardyShortAbsIntegral_ge_sub_shortDirichlet :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ T delta t : ℝ, T0 ≤ T → 0 ≤ delta →
        t ∈ Icc T (2 * T - delta) →
          delta -
              ‖criticalLineShortDirichletPolynomial delta
                (firstZetaApproximationCutoff T) t‖ -
              C * delta / Real.sqrt T ≤
            hardyShortAbsIntegral delta t := by
  obtain ⟨C, T0, hC, hT0, happ⟩ := criticalLineZetaFirstApprox
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T delta t hT hdelta ht
  have hT1 : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have htt : t ≤ t + delta := by linarith
  let N : ℕ := firstZetaApproximationCutoff T
  let F : ℝ → ℂ := fun u => riemannZeta ((1 / 2 : ℂ) + I * u)
  let Q : ℝ → ℂ := fun u =>
    ∑ n ∈ Finset.Icc 2 N,
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)
  let H : ℝ → ℂ := fun u => F u - (1 + Q u)
  have hcutoff : 1 ≤ N := by
    dsimp only [N, firstZetaApproximationCutoff]
    apply Nat.le_floor
    norm_num
    linarith
  have hsum_split (u : ℝ) :
      (∑ n ∈ Finset.Icc 1 N,
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) = 1 + Q u := by
    have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp only [Q, Nat.cast_one, one_cpow, one_div]
    norm_num
  have hHpoint : ∀ u ∈ Icc t (t + delta),
      ‖H u‖ ≤ C / Real.sqrt T := by
    intro u hu
    have huT : u ∈ Icc T (2 * T) := by
      constructor
      · exact ht.1.trans hu.1
      · linarith [hu.2, ht.2]
    obtain ⟨R, hzeta, hR⟩ := happ T u hT huT
    have hHR : H u = R := by
      dsimp only [H, F]
      rw [hzeta]
      change
        (∑ n ∈ Finset.Icc 1 N,
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) + R -
            (1 + Q u) = R
      rw [hsum_split]
      ring
    rw [hHR]
    exact hR
  have hQcont : Continuous Q := by
    dsimp only [Q]
    apply continuous_finset_sum
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    rw [show (fun u : ℝ =>
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) =
      (fun u : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * u)) by
          funext u
          exact inv_nat_cpow_criticalLine_eq_exp hn0 u]
    fun_prop
  have hQint : IntervalIntegrable Q volume t (t + delta) :=
    hQcont.intervalIntegrable _ _
  have hFcont : ContinuousOn F (Icc t (t + delta)) := by
    intro u hu
    have huT : T ≤ u := ht.1.trans hu.1
    have hupos : 0 < u := hTpos.trans_le huT
    have hs1 : ((1 / 2 : ℂ) + I * u) ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      norm_num at him
      linarith
    have hpath : ContinuousAt (fun v : ℝ => (1 / 2 : ℂ) + I * v) u := by
      fun_prop
    have hzbase : ContinuousAt riemannZeta ((1 / 2 : ℂ) + I * u) :=
      (differentiableAt_riemannZeta hs1).continuousAt
    have hzcont : ContinuousAt
        (riemannZeta ∘ fun v : ℝ => (1 / 2 : ℂ) + I * v) u :=
      (show Tendsto riemannZeta
          (nhds ((1 / 2 : ℂ) + I * u))
          (nhds (riemannZeta ((1 / 2 : ℂ) + I * u))) from hzbase).comp
        (show Tendsto (fun v : ℝ => (1 / 2 : ℂ) + I * v)
          (nhds u) (nhds ((1 / 2 : ℂ) + I * u)) from hpath)
    simpa only [F, Function.comp_apply] using hzcont.continuousWithinAt
  have hFint : IntervalIntegrable F volume t (t + delta) :=
    ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le htt] using hFcont)
  have hUint : IntervalIntegrable (fun u => (1 : ℂ) + Q u)
      volume t (t + delta) :=
    continuous_const.intervalIntegrable _ _ |>.add hQint
  have hHint : IntervalIntegrable H volume t (t + delta) := by
    dsimp only [H]
    exact hFint.sub hUint
  have hHintegral :
      (∫ u in t..t + delta, H u) =
        (∫ u in t..t + delta, F u) -
          ((∫ _u in t..t + delta, (1 : ℂ)) +
            ∫ u in t..t + delta, Q u) := by
    dsimp only [H]
    rw [intervalIntegral.integral_sub hFint hUint,
      intervalIntegral.integral_add
        (continuous_const.intervalIntegrable _ _) hQint]
  have hone :
      (∫ _u in t..t + delta, (1 : ℂ)) = (delta : ℂ) := by
    have h := intervalIntegral.integral_ofReal
      (μ := volume) (a := t) (b := t + delta)
        (f := fun _u : ℝ => (1 : ℝ))
    have hreal : (∫ _u in t..t + delta, (1 : ℝ)) = delta := by
      simp
    rw [show (fun _u : ℝ => (1 : ℂ)) =
        fun _u : ℝ => ((1 : ℝ) : ℂ) by rfl]
    rw [h, hreal]
  have hOneEq :
      (delta : ℂ) =
        (∫ u in t..t + delta, F u) -
          (∫ u in t..t + delta, Q u) -
            ∫ u in t..t + delta, H u := by
    rw [hHintegral, hone]
    ring
  have hQeq :
      (∫ u in t..t + delta, Q u) =
        criticalLineShortDirichletPolynomial delta N t := by
    dsimp only [Q]
    exact integral_criticalLineDirichletPolynomial_eq_shortPolynomial
      delta t N
  have herror :
      ‖∫ u in t..t + delta, H u‖ ≤
        C * delta / Real.sqrt T := by
    have hmajor := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t + delta) (C := C / Real.sqrt T) (f := H)
      (fun u hu => by
        rw [uIoc_of_le htt] at hu
        exact hHpoint u ⟨hu.1.le, hu.2⟩)
    calc
      ‖∫ u in t..t + delta, H u‖ ≤
          (C / Real.sqrt T) * |t + delta - t| := hmajor
      _ = C * delta / Real.sqrt T := by
        rw [abs_of_nonneg (by linarith : 0 ≤ t + delta - t)]
        ring
  have htriangle :
      delta ≤ ‖∫ u in t..t + delta, F u‖ +
          ‖criticalLineShortDirichletPolynomial delta N t‖ +
            ‖∫ u in t..t + delta, H u‖ := by
    calc
      delta = ‖(delta : ℂ)‖ := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hdelta]
      _ = ‖(∫ u in t..t + delta, F u) -
          (∫ u in t..t + delta, Q u) -
            ∫ u in t..t + delta, H u‖ := congrArg norm hOneEq
      _ ≤ ‖(∫ u in t..t + delta, F u) -
          (∫ u in t..t + delta, Q u)‖ +
            ‖∫ u in t..t + delta, H u‖ := norm_sub_le _ _
      _ ≤ (‖∫ u in t..t + delta, F u‖ +
          ‖∫ u in t..t + delta, Q u‖) +
            ‖∫ u in t..t + delta, H u‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖∫ u in t..t + delta, F u‖ +
          ‖criticalLineShortDirichletPolynomial delta N t‖ +
            ‖∫ u in t..t + delta, H u‖ := by rw [hQeq]
  have hnormIntegral := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := F) htt
  have hnormEq :
      (∫ u in t..t + delta, ‖F u‖) =
        hardyShortAbsIntegral delta t := by
    dsimp only [hardyShortAbsIntegral]
    apply intervalIntegral.integral_congr
    intro u _hu
    dsimp only [F]
    exact (abs_hardyZ_eq_norm_riemannZeta u).symm
  rw [hnormEq] at hnormIntegral
  dsimp only [N] at htriangle ⊢
  nlinarith

end HardyTheorem
