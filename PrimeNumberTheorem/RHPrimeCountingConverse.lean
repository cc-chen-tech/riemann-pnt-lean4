import PrimeNumberTheorem.RHNaturalPsiError

open Filter MeasureTheory Asymptotics Topology

namespace PrimeNumberTheorem

private lemma hasDerivAt_logIntegral {x : ℝ} (hx : 1 < x) :
    HasDerivAt logIntegral (1 / Real.log x) x := by
  let f : ℝ → ℝ := fun t => 1 / Real.log t
  have hcont : ContinuousOn f (Set.uIcc 2 x) := by
    intro t ht
    have ht1 : 1 < t := by
      rw [Set.mem_uIcc] at ht
      rcases ht with ht | ht <;> linarith
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (continuousAt_const.div (Real.continuousAt_log ht0) hlog).continuousWithinAt
  have hfx : ContinuousAt f x := by
    have hx0 : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    dsimp [f]
    exact continuousAt_const.div (Real.continuousAt_log hx0) hlog
  have hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume := by
    exact ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi
      (fun y hy => by
        have hy1 : 1 < y := hy
        have hy0 : y ≠ 0 := by linarith
        have hlog : Real.log y ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
        exact continuousAt_const.div (Real.continuousAt_log hy0) hlog)
      x hx
  have hderiv := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable) hmeas hfx
  change HasDerivAt (fun u => ∫ t in (2)..u, 1 / Real.log t)
    (1 / Real.log x) x
  simpa [f] using hderiv

/-- Exact cancellation of the logarithmic-integral main term in the reverse
Abel summation formula. -/
lemma logIntegral_mul_log_sub_integral_div_eq_sub_two
    {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x * Real.log x -
        (∫ t in (2)..x, logIntegral t / t) = x - 2 := by
  have hderivLi : ∀ t ∈ Set.uIcc 2 x,
      HasDerivAt logIntegral (1 / Real.log t) t := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    apply hasDerivAt_logIntegral
    rcases ht with ht | ht <;> linarith
  have hderivLog : ∀ t ∈ Set.uIcc 2 x,
      HasDerivAt Real.log (1 / t) t := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    have ht0 : t ≠ 0 := by rcases ht with ht | ht <;> linarith
    simpa [one_div] using Real.hasDerivAt_log ht0
  have hLiInt : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
    exact (ContinuousOn.intervalIntegrable fun t ht => by
      rw [Set.mem_uIcc] at ht
      have ht1 : 1 < t := by rcases ht with ht | ht <;> linarith
      have ht0 : t ≠ 0 := by linarith
      have hlog : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
      exact (continuousAt_const.div (Real.continuousAt_log ht0) hlog).continuousWithinAt)
  have hInvInt : IntervalIntegrable (fun t : ℝ => 1 / t) volume 2 x := by
    exact (ContinuousOn.intervalIntegrable fun t ht => by
      rw [Set.mem_uIcc] at ht
      have ht0 : t ≠ 0 := by rcases ht with ht | ht <;> linarith
      exact (continuousAt_const.div continuousAt_id ht0).continuousWithinAt)
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := logIntegral) (u' := fun t : ℝ => 1 / Real.log t)
    (v := Real.log) (v' := fun t : ℝ => 1 / t)
    hderivLi hderivLog hLiInt hInvInt
  have hunit :
      (∫ t in (2)..x, (1 / Real.log t) * Real.log t) = x - 2 := by
    calc
      (∫ t in (2)..x, (1 / Real.log t) * Real.log t) =
          ∫ _t in (2)..x, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [Set.mem_uIcc] at ht
            have ht1 : 1 < t := by rcases ht with ht | ht <;> linarith
            field_simp [Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)]
      _ = x - 2 := by simp
  rw [hunit] at hip
  have hli2 : logIntegral 2 = 0 := by simp [logIntegral]
  rw [hli2] at hip
  have hip' :
      (∫ t in (2)..x, logIntegral t / t) =
        logIntegral x * Real.log x - (x - 2) := by
    simpa [div_eq_mul_inv] using hip
  rw [hip']
  ring

private lemma intervalIntegrable_logIntegral_div
    {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => logIntegral t / t) volume 2 x := by
  exact ContinuousOn.intervalIntegrable fun t ht => by
    rw [Set.mem_uIcc] at ht
    have ht1 : 1 < t := by rcases ht with ht | ht <;> linarith
    have ht0 : t ≠ 0 := by rcases ht with ht | ht <;> linarith
    exact ((hasDerivAt_logIntegral ht1).continuousAt.div
      continuousAt_id ht0).continuousWithinAt

private lemma intervalIntegrable_primeCounting_div
    {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (primeCounting t : ℝ) / t) volume 2 x := by
  let c : ℕ → ℝ := fun n => if n.Prime then 1 else 0
  have hg : IntegrableOn (fun t : ℝ => 1 / t) (Set.Icc 2 x) :=
    ContinuousOn.integrableOn_Icc fun t ht => by
      have ht0 : t ≠ 0 := by linarith [ht.1]
      exact (continuousAt_const.div continuousAt_id ht0).continuousWithinAt
  have hsum := integrableOn_mul_sum_Icc (c := c) (m := 0)
    (a := (2 : ℝ)) (b := x) (by norm_num) hg
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  refine hsum.congr_fun ?_ measurableSet_Icc
  intro t ht
  have ht0 : 0 ≤ t := by linarith [ht.1]
  change (1 / t) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
    (primeCounting t : ℝ) / t
  rw [primeCounting_eq_mathlib t ht0]
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]
  rw [Finset.card_eq_sum_ones, Nat.range_succ_eq_Icc_zero,
    Finset.sum_filter]
  simp [c, div_eq_mul_inv, mul_comm]

private lemma intervalIntegrable_primeCountingLi_error_div
    {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ => ((primeCounting t : ℝ) - logIntegral t) / t)
      volume 2 x := by
  simpa [sub_div] using
    (intervalIntegrable_primeCounting_div hx).sub
      (intervalIntegrable_logIntegral_div hx)

/-- Exact reverse partial-summation decomposition.  It separates the
prime-counting error from the logarithmic-integral main term before any
asymptotic estimate is applied. -/
lemma chebyshevTheta_sub_id_eq_primeCountingLi_error
    {x : ℝ} (hx : 2 ≤ x) :
    Chebyshev.theta x - x =
      (((primeCounting x : ℝ) - logIntegral x) * Real.log x -
        (∫ t in (2)..x,
          ((primeCounting t : ℝ) - logIntegral t) / t)) - 2 := by
  have hx0 : 0 ≤ x := by linarith
  have htheta :
      Chebyshev.theta x =
        (primeCounting x : ℝ) * Real.log x -
          ∫ t in (2)..x, (primeCounting t : ℝ) / t := by
    calc
      Chebyshev.theta x =
          (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x -
            ∫ t in (2)..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t :=
        Chebyshev.theta_eq_primeCounting_mul_log_sub_integral hx
      _ = (primeCounting x : ℝ) * Real.log x -
            ∫ t in (2)..x, (primeCounting t : ℝ) / t := by
        congr 1
        · rw [primeCounting_eq_mathlib x hx0]
        · apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.mem_uIcc] at ht
          have ht0 : 0 ≤ t := by rcases ht with ht | ht <;> linarith
          change (Nat.primeCounting ⌊t⌋₊ : ℝ) / t =
            (primeCounting t : ℝ) / t
          rw [primeCounting_eq_mathlib t ht0]
  have hmain := logIntegral_mul_log_sub_integral_div_eq_sub_two hx
  rw [htheta]
  have hsplit :
      (∫ t in (2)..x,
          ((primeCounting t : ℝ) - logIntegral t) / t) =
        (∫ t in (2)..x, (primeCounting t : ℝ) / t) -
          ∫ t in (2)..x, logIntegral t / t := by
    calc
      (∫ t in (2)..x,
          ((primeCounting t : ℝ) - logIntegral t) / t) =
          ∫ t in (2)..x,
            (primeCounting t : ℝ) / t - logIntegral t / t := by
              apply intervalIntegral.integral_congr
              intro t _
              ring
      _ = (∫ t in (2)..x, (primeCounting t : ℝ) / t) -
          ∫ t in (2)..x, logIntegral t / t :=
        intervalIntegral.integral_sub
          (intervalIntegrable_primeCounting_div hx)
          (intervalIntegrable_logIntegral_div hx)
  rw [hsplit]
  linarith

private lemma abs_integral_primeCountingLi_error_div_le
    {C x : ℝ} (hC : 0 ≤ C) (hx2 : 2 ≤ x) (hlogx : 1 ≤ Real.log x)
    (herror : ∀ t ≥ 2,
      |(primeCounting t : ℝ) - logIntegral t| ≤
        C * Real.sqrt t * Real.log t) :
    |∫ t in (2)..x, ((primeCounting t : ℝ) - logIntegral t) / t| ≤
      2 * C * Real.sqrt x * (Real.log x) ^ 2 := by
  let K : ℝ → ℝ := fun t => ((primeCounting t : ℝ) - logIntegral t) / t
  let M : ℝ → ℝ := fun t => C * Real.log x * (1 / Real.sqrt t)
  have hKint : IntervalIntegrable K volume 2 x := by
    simpa [K] using intervalIntegrable_primeCountingLi_error_div hx2
  have hMint : IntervalIntegrable M volume 2 x := by
    exact ContinuousOn.intervalIntegrable fun t ht => by
      rw [Set.mem_uIcc] at ht
      have htpos : 0 < t := by rcases ht with ht | ht <;> linarith
      have hsqrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 htpos).ne'
      dsimp [M]
      have hconst : ContinuousAt (fun _ : ℝ => C * Real.log x) t :=
        continuousAt_const
      have hinv : ContinuousAt (fun u : ℝ => (Real.sqrt u)⁻¹) t :=
        Real.continuous_sqrt.continuousAt.inv₀ hsqrt
      exact ContinuousAt.continuousWithinAt (by
        simpa [one_div] using hconst.mul hinv)
  have hpoint : ∀ t ∈ Set.Icc 2 x, |K t| ≤ M t := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have htx : t ≤ x := ht.2
    have htpos : 0 < t := by linarith
    have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
    have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hlogle : Real.log t ≤ Real.log x :=
      Real.log_le_log htpos htx
    have hEt := herror t ht2
    dsimp [K, M]
    calc
      |((primeCounting t : ℝ) - logIntegral t) / t| =
          |(primeCounting t : ℝ) - logIntegral t| / t := by
            rw [abs_div, abs_of_pos htpos]
      _ ≤ (C * Real.sqrt t * Real.log t) / t :=
        div_le_div_of_nonneg_right hEt htpos.le
      _ = C * Real.log t * (1 / Real.sqrt t) := by
        field_simp [hsqrtpos.ne', htpos.ne']
        rw [Real.sq_sqrt htpos.le]
        ring
      _ ≤ C * Real.log x * (1 / Real.sqrt t) := by
        have hinv0 : 0 ≤ 1 / Real.sqrt t := by positivity
        gcongr
  have habs : |∫ t in (2)..x, K t| ≤ ∫ t in (2)..x, |K t| :=
    intervalIntegral.abs_integral_le_integral_abs hx2
  have hmono : (∫ t in (2)..x, |K t|) ≤ ∫ t in (2)..x, M t := by
    exact intervalIntegral.integral_mono_on hx2 hKint.abs hMint hpoint
  have hpull :
      (∫ t in (2)..x, M t) =
        (C * Real.log x) * ∫ t in (2)..x, 1 / Real.sqrt t := by
    dsimp [M]
    rw [intervalIntegral.integral_const_mul]
  have hint :
      (∫ t in (2)..x, M t) ≤
        (C * Real.log x) * (2 * Real.sqrt x) := by
    rw [hpull]
    exact mul_le_mul_of_nonneg_left
      (integral_one_div_sqrt_le_two_sqrt (by norm_num) hx2)
      (mul_nonneg hC (le_trans zero_le_one hlogx))
  have hscale :
      (C * Real.log x) * (2 * Real.sqrt x) ≤
        2 * C * Real.sqrt x * (Real.log x) ^ 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hlog0 : 0 ≤ Real.log x := le_trans zero_le_one hlogx
    nlinarith [mul_nonneg hC hsqrt0, sq_nonneg (Real.log x - 1)]
  exact habs.trans (hmono.trans (hint.trans hscale))

/-- Reverse quantitative partial summation: the RH-scale prime-counting
`Li` error implies the RH-scale Chebyshev-`theta` error. -/
theorem RH_ThetaErrorBound_of_RH_PrimeCountingLiErrorBound
    (hπ : RH_PrimeCountingLiErrorBound) : RH_ThetaErrorBound := by
  rcases RH_ErrorBound_of_RH_PrimeCountingLiErrorBound hπ with
    ⟨C, hCpos, herror⟩
  rw [RH_ThetaErrorBound]
  refine Asymptotics.IsBigO.of_bound (3 * C + 2) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1 + 2)] with x hx
  have hx2 : 2 ≤ x := by nlinarith [Real.exp_pos 1]
  have hxpos : 0 < x := by linarith
  have hexp : Real.exp 1 ≤ x := by linarith
  have hlogx : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).2 hexp
  have hsqrt1 : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num)]
    all_goals nlinarith
  let E : ℝ := (primeCounting x : ℝ) - logIntegral x
  let I : ℝ := ∫ t in (2)..x,
    ((primeCounting t : ℝ) - logIntegral t) / t
  let S : ℝ := Real.sqrt x * (Real.log x) ^ 2
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  have hS1 : 1 ≤ S := by
    dsimp [S]
    have hlogsq : 1 ≤ (Real.log x) ^ 2 := by nlinarith
    nlinarith [mul_le_mul hsqrt1 hlogsq zero_le_one (Real.sqrt_nonneg x)]
  have hE : |E| ≤ C * Real.sqrt x * Real.log x := by
    simpa [E] using herror x hx2
  have hendpoint : |E * Real.log x| ≤ C * S := by
    rw [abs_mul, abs_of_nonneg (le_trans zero_le_one hlogx)]
    calc
      |E| * Real.log x ≤
          (C * Real.sqrt x * Real.log x) * Real.log x :=
        mul_le_mul_of_nonneg_right hE (le_trans zero_le_one hlogx)
      _ = C * S := by dsimp [S]; ring
  have hintegral : |I| ≤ 2 * C * S := by
    simpa [I, S, mul_assoc] using
      abs_integral_primeCountingLi_error_div_le hCpos.le hx2 hlogx herror
  have hdecomp : Chebyshev.theta x - x = (E * Real.log x - I) - 2 := by
    simpa [E, I] using chebyshevTheta_sub_id_eq_primeCountingLi_error hx2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hS0, hdecomp]
  calc
    |(E * Real.log x - I) - 2| ≤ |E * Real.log x| + |I| + 2 := by
      calc
        |(E * Real.log x - I) - 2| ≤ |E * Real.log x - I| + |(2 : ℝ)| :=
          abs_sub _ _
        _ ≤ (|E * Real.log x| + |I|) + 2 := by
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (abs_sub (E * Real.log x) I) 2
    _ ≤ C * S + 2 * C * S + 2 := by
      exact add_le_add (add_le_add hendpoint hintegral) le_rfl
    _ ≤ C * S + 2 * C * S + 2 * S := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left
          (mul_le_mul_of_nonneg_left hS1 (by norm_num : (0 : ℝ) ≤ 2))
          (C * S + 2 * C * S)
    _ = (3 * C + 2) * S := by ring

/-- The RH-scale prime-counting `Li` error implies the corresponding
Chebyshev-`psi` error through the reverse partial-summation estimate. -/
theorem RH_PsiErrorBound_of_RH_PrimeCountingLiErrorBound
    (hπ : RH_PrimeCountingLiErrorBound) : RH_PsiErrorBound :=
  RH_PsiErrorBound_of_RH_ThetaErrorBound
    (RH_ThetaErrorBound_of_RH_PrimeCountingLiErrorBound hπ)

/-- The RH-scale prime-counting `Li` error implies the Riemann hypothesis. -/
theorem riemannHypothesis_of_RH_PrimeCountingLiErrorBound
    (hπ : RH_PrimeCountingLiErrorBound) : RiemannHypothesis.Statement := by
  exact PrimeNumberTheorem.rh_statement_iff_mathlib.mp
    (ZeroFreeRegion.riemannHypothesis_of_RH_PsiErrorBound
      (RH_PsiErrorBound_of_RH_PrimeCountingLiErrorBound hπ))

/-- The classical von Koch equivalence between RH and the RH-scale
prime-counting `Li` error, now closed in both directions. -/
theorem rh_iff_optimal_error_proved : rh_iff_optimal_error :=
  rh_iff_optimal_error_of_implications
    ExplicitFormulaResidues.RH_PrimeCountingLiErrorBound_of_RiemannHypothesis
    riemannHypothesis_of_RH_PrimeCountingLiErrorBound

end PrimeNumberTheorem
