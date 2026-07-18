import HardyTheorem.HardyIntegralBasics
import HardyTheorem.VerticalGammaAsymptotic

open Complex Filter MeasureTheory Set Topology

namespace HardyTheorem

/-- Hardy's real-valued function is the real part of the zeta value after
rotation by the exact `Gammaℝ` unit phase. -/
theorem hardyZ_eq_re_exp_I_thetaPhase_mul_zeta (t : ℝ) :
    hardyZ t =
      (Complex.exp (I * thetaPhase t) *
        riemannZeta ((1 / 2 : ℂ) + I * t)).re := by
  rw [hardyZ_explicit]
  rw [show I * (thetaPhase t : ℂ) = (thetaPhase t : ℂ) * I by ring,
    Complex.exp_ofReal_mul_I]
  rw [Complex.mul_re]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

/-- A critical-line Dirichlet monomial rotated by the elementary Gamma phase
has exactly the Hardy oscillatory phase. -/
theorem exp_I_thetaModel_mul_inv_nat_cpow_criticalLine_eq
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    Complex.exp (I * thetaModel t) *
        (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp (I * OscillatoryIntegral.hardyPhase n t) := by
  rw [inv_nat_cpow_criticalLine_eq_exp hn]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog_sq : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by
    rw [Real.log_pow]
    norm_num
  have hlog_div :
      Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) =
        Real.log (t / (2 * Real.pi)) - 2 * Real.log n := by
    rw [show t / (2 * Real.pi * ((n : ℝ) ^ 2)) =
        (t / (2 * Real.pi)) / ((n : ℝ) ^ 2) by ring]
    rw [Real.log_div (by positivity) (by positivity), hlog_sq]
  rw [OscillatoryIntegral.hardyPhase, hlog_div]
  simp only [thetaModel]
  push_cast
  ring

/-- Once the Dirichlet index lies beyond `2 * sqrt T`, the Hardy phase is
uniformly nonstationary on `[T, 2T]`. -/
theorem norm_integral_cexp_hardyPhase_le_of_two_sqrt_lt
    {n : ℕ} (hn : n ≠ 0) {T : ℝ} (hT : 1 ≤ T)
    (hfar : 2 * Real.sqrt T < n) :
    ‖∫ t in T..(2 * T),
        Complex.exp (I * OscillatoryIntegral.hardyPhase n t)‖ ≤ 12 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hn_sq : 4 * T < (n : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt hTpos.le]
  have hden : 24 * T < 2 * Real.pi * (n : ℝ) ^ 2 := by
    have hpi : 6 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hmul : 6 * (n : ℝ) ^ 2 <
        (2 * Real.pi) * (n : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right hpi (sq_pos_of_pos hnpos)
    nlinarith
  have hlocal : ∀ x ∈ Icc T (2 * T),
      ContDiffAt ℝ 2 (OscillatoryIntegral.hardyPhase n) x := by
    intro x hx
    exact OscillatoryIntegral.contDiffAt_hardyPhase_two hn
      (hTpos.trans_le hx.1)
  have hderiv_le : ∀ x ∈ Icc T (2 * T),
      deriv (OscillatoryIntegral.hardyPhase n) x ≤ -(1 / 3 : ℝ) := by
    intro x hx
    have hxpos : 0 < x := hTpos.trans_le hx.1
    let q : ℝ := x / (2 * Real.pi * (n : ℝ) ^ 2)
    have hqpos : 0 < q := div_pos hxpos (by positivity)
    have hq : q ≤ 1 / 12 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * (n : ℝ) ^ 2)).2
      dsimp only [q]
      nlinarith [hx.2, hden]
    have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hqpos
    rw [OscillatoryIntegral.deriv_hardyPhase hn hxpos]
    change (1 / 2 : ℝ) * Real.log q ≤ -(1 / 3 : ℝ)
    nlinarith
  have hmono : MonotoneOn
      (deriv (OscillatoryIntegral.hardyPhase n)) (Icc T (2 * T)) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := hTpos.trans_le hx.1
    have hypos : 0 < y := hTpos.trans_le hy.1
    rw [OscillatoryIntegral.deriv_hardyPhase hn hxpos,
      OscillatoryIntegral.deriv_hardyPhase hn hypos]
    gcongr
  have haway : ∀ x ∈ Icc T (2 * T),
      (1 / 3 : ℝ) ≤ |deriv (OscillatoryIntegral.hardyPhase n) x| := by
    intro x hx
    have hle := hderiv_le x hx
    rw [abs_of_nonpos (hle.trans (by norm_num))]
    linarith
  have hbound :=
    OscillatoryIntegral.norm_integral_cexp_phase_le_of_monotone_deriv_local
      (show T ≤ 2 * T by linarith) (show (0 : ℝ) < 1 / 3 by norm_num)
      hlocal (Or.inl hmono) haway
  convert hbound using 1 <;> norm_num

theorem sum_inv_sqrt_Icc_one_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹ ≤
      1 + Real.sqrt N * Real.sqrt (harmonic N : ℝ) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      constructor
      · intro hn
        rcases hn with ⟨hn1, hnN⟩
        omega
      · intro hn
        rcases hn with rfl | hn
        · exact ⟨le_rfl, Nat.one_le_iff_ne_zero.mpr hN⟩
        · exact ⟨hn.1.trans' (by omega), hn.2⟩
    rw [hset, Finset.sum_insert (by simp)]
    norm_num
    exact sum_inv_sqrt_Icc_two_le N

theorem sum_inv_sqrt_Icc_one_le_two_sqrt (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹ ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hset : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      by_cases hN : N = 0
      · subst N
        norm_num
      · have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
        have hSpos : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
        have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
        have hsqrtS : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hSpos
        have hsqrt_le : Real.sqrt N ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) := by
          apply Real.sqrt_le_sqrt
          norm_num
        have hsqN : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hNpos.le
        have hsqS : (Real.sqrt ((N + 1 : ℕ) : ℝ)) ^ 2 = (N + 1 : ℕ) :=
          Real.sq_sqrt hSpos.le
        have hcross :
            1 ≤ 2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N) *
              Real.sqrt ((N + 1 : ℕ) : ℝ) := by
          have hdiff : 0 ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N :=
            sub_nonneg.mpr hsqrt_le
          have hsum :
              Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt N ≤
                2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by linarith
          calc
            1 = (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N) *
                (Real.sqrt ((N + 1 : ℕ) : ℝ) + Real.sqrt N) := by
              norm_num [Nat.cast_add, Nat.cast_one] at hsqS ⊢
              nlinarith [hsqN]
            _ ≤ (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N) *
                (2 * Real.sqrt ((N + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hsum hdiff
            _ = _ := by ring
        have hinv :
            (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ≤
              2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N) := by
          rw [show (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ =
            1 / Real.sqrt ((N + 1 : ℕ) : ℝ) by ring,
            div_le_iff₀ hsqrtS]
          exact hcross
        calc
          (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ +
              ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹ ≤
              (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ + 2 * Real.sqrt N := by
            simpa only [add_comm] using
              add_le_add_left ih (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹
          _ ≤ 2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by linarith

/-- The elementary-phase Dirichlet polynomial is bounded by a near-stationary
piece and a uniformly nonstationary piece. -/
theorem norm_integral_thetaModel_dirichletPolynomial_le
    {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..(2 * T),
        Complex.exp (I * thetaModel t) *
          (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
      48 * Real.sqrt T * Real.sqrt ⌊2 * Real.sqrt T⌋₊ +
        24 * Real.sqrt (firstZetaApproximationCutoff T) := by
  let N := firstZetaApproximationCutoff T
  let K := ⌊2 * Real.sqrt T⌋₊
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hsumint :
      (∫ t in T..(2 * T),
        Complex.exp (I * thetaModel t) *
          (∑ n ∈ Finset.Icc 1 N,
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))) =
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            ∫ t in T..(2 * T),
              Complex.exp (I * OscillatoryIntegral.hardyPhase n t) := by
    rw [show (fun t : ℝ =>
        Complex.exp (I * thetaModel t) *
          (∑ n ∈ Finset.Icc 1 N,
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))) =
        (fun t : ℝ => ∑ n ∈ Finset.Icc 1 N,
          Complex.exp (I * thetaModel t) *
            (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))) by
      funext t
      rw [Finset.mul_sum]]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n hnmem
      have hn : n ≠ 0 := by
        have := (Finset.mem_Icc.mp hnmem).1
        omega
      calc
        (∫ t in T..(2 * T),
            Complex.exp (I * thetaModel t) *
              (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))) =
            ∫ t in T..(2 * T),
              ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
                Complex.exp (I * OscillatoryIntegral.hardyPhase n t) := by
          apply intervalIntegral.integral_congr
          intro t htmem
          rw [Set.uIcc_of_le (show T ≤ 2 * T by linarith)] at htmem
          exact exp_I_thetaModel_mul_inv_nat_cpow_criticalLine_eq hn
            (hTpos.trans_le htmem.1)
        _ = ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            ∫ t in T..(2 * T),
              Complex.exp (I * OscillatoryIntegral.hardyPhase n t) :=
          intervalIntegral.integral_const_mul _ _
    · intro n hnmem
      have hn : n ≠ 0 := by
        have := (Finset.mem_Icc.mp hnmem).1
        omega
      have hrhsCont : ContinuousOn (fun t : ℝ =>
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            Complex.exp (I * OscillatoryIntegral.hardyPhase n t))
          (Set.Icc T (2 * T)) := by
        intro t htmem
        have htpos : 0 < t := hTpos.trans_le htmem.1
        exact (continuousAt_const.mul
          (continuousAt_const.mul
            (Complex.continuous_ofReal.continuousAt.comp
              (OscillatoryIntegral.contDiffAt_hardyPhase_two hn htpos).continuousAt)).cexp).continuousWithinAt
      have hrhsInt : IntervalIntegrable (fun t : ℝ =>
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            Complex.exp (I * OscillatoryIntegral.hardyPhase n t))
          volume T (2 * T) :=
        ContinuousOn.intervalIntegrable_of_Icc
          (show T ≤ 2 * T by linarith) hrhsCont
      apply hrhsInt.congr
      intro t htmem
      have htcc := Set.uIoc_subset_uIcc htmem
      rw [Set.uIcc_of_le (show T ≤ 2 * T by linarith)] at htcc
      exact (exp_I_thetaModel_mul_inv_nat_cpow_criticalLine_eq hn
        (hTpos.trans_le htcc.1)).symm
  rw [hsumint]
  calc
    ‖∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          ∫ t in T..(2 * T),
            Complex.exp (I * OscillatoryIntegral.hardyPhase n t)‖ ≤
        ∑ n ∈ Finset.Icc 1 N,
          ‖((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            ∫ t in T..(2 * T),
              Complex.exp (I * OscillatoryIntegral.hardyPhase n t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        if n ≤ K then (Real.sqrt n)⁻¹ * (24 * Real.sqrt T)
        else (Real.sqrt n)⁻¹ * 12 := by
      apply Finset.sum_le_sum
      intro n hnmem
      have hn : n ≠ 0 := by
        have := (Finset.mem_Icc.mp hnmem).1
        omega
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos hnpos]
      norm_num
      rw [← Real.sqrt_eq_rpow]
      by_cases hnear : n ≤ K
      · rw [if_pos hnear]
        have hsecond := OscillatoryIntegral.norm_integral_cexp_hardyPhase_le hn hT
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hsecond
        norm_num at hsecond
        have hsecond' :
            ‖∫ t in T..(2 * T),
                Complex.exp (I * OscillatoryIntegral.hardyPhase n t)‖ ≤
              24 * Real.sqrt T := hsecond.trans_eq (by ring)
        exact mul_le_mul_of_nonneg_left hsecond' (by positivity)
      · rw [if_neg hnear]
        have hfloor : 2 * Real.sqrt T < n := by
          calc
            2 * Real.sqrt T < (K : ℝ) + 1 := by
              simpa only [K] using Nat.lt_floor_add_one (2 * Real.sqrt T)
            _ ≤ n := by
              exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnear))
        exact mul_le_mul_of_nonneg_left
          (norm_integral_cexp_hardyPhase_le_of_two_sqrt_lt hn hT hfloor)
          (by positivity)
    _ ≤ 24 * Real.sqrt T *
          (∑ n ∈ Finset.Icc 1 K, (Real.sqrt n)⁻¹) +
        12 * (∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹) := by
      rw [Finset.sum_ite]
      have hnearSubset : (Finset.Icc 1 N).filter (fun n => n ≤ K) ⊆
          Finset.Icc 1 K := by
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        exact ⟨hn.1.1, hn.2⟩
      have hfarSubset : (Finset.Icc 1 N).filter (fun n => ¬n ≤ K) ⊆
          Finset.Icc 1 N := Finset.filter_subset _ _
      gcongr
      · rw [Finset.mul_sum]
        simpa only [mul_comm] using
          (Finset.sum_le_sum_of_subset_of_nonneg hnearSubset (by
            intro n _ _
            positivity) :
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≤ K),
              (Real.sqrt n)⁻¹ * (24 * Real.sqrt T)) ≤
            ∑ n ∈ Finset.Icc 1 K,
              (Real.sqrt n)⁻¹ * (24 * Real.sqrt T))
      · rw [Finset.mul_sum]
        simpa only [mul_comm] using
          (Finset.sum_le_sum_of_subset_of_nonneg hfarSubset (by
            intro n _ _
            positivity) :
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬n ≤ K),
              (Real.sqrt n)⁻¹ * 12) ≤
            ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹ * 12)
    _ ≤ 24 * Real.sqrt T * (2 * Real.sqrt K) +
        12 * (2 * Real.sqrt N) := by
      gcongr
      · exact sum_inv_sqrt_Icc_one_le_two_sqrt K
      · exact sum_inv_sqrt_Icc_one_le_two_sqrt N
    _ = _ := by ring

theorem norm_integral_thetaModel_dirichletPolynomial_le_rpow_three_quarters
    {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..(2 * T),
        Complex.exp (I * thetaModel t) *
          (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
      144 * T ^ (3 / 4 : ℝ) := by
  let K := ⌊2 * Real.sqrt T⌋₊
  let N := firstZetaApproximationCutoff T
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hK : (K : ℝ) ≤ 2 * Real.sqrt T := by
    exact Nat.floor_le (by positivity)
  have hN : (N : ℝ) ≤ 4 * T := by
    exact Nat.floor_le (by positivity)
  have hqpos : 0 < T ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hTpos _
  have hqSq : (T ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt T := by
    rw [pow_two, ← Real.rpow_add hTpos]
    norm_num
    rw [Real.sqrt_eq_rpow]
  have hsqrtK : Real.sqrt K ≤ 2 * T ^ (1 / 4 : ℝ) := by
    have hsquare : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt (by positivity)
    have hsqrt_nonneg := Real.sqrt_nonneg (K : ℝ)
    nlinarith [Real.sqrt_nonneg T]
  have hsqrtN : Real.sqrt N ≤ 2 * Real.sqrt T := by
    have hsquare : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (by positivity)
    have hTsquare : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
    have hsqrt_nonneg := Real.sqrt_nonneg (N : ℝ)
    nlinarith [Real.sqrt_nonneg T]
  have hmulRpow :
      Real.sqrt T * T ^ (1 / 4 : ℝ) = T ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hTpos]
    norm_num
  have hsqrt_le : Real.sqrt T ≤ T ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  calc
    ‖∫ t in T..(2 * T),
        Complex.exp (I * thetaModel t) *
          (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
        48 * Real.sqrt T * Real.sqrt K + 24 * Real.sqrt N := by
      simpa only [K, N] using norm_integral_thetaModel_dirichletPolynomial_le hT
    _ ≤ 48 * Real.sqrt T * (2 * T ^ (1 / 4 : ℝ)) +
        24 * (2 * Real.sqrt T) := by gcongr
    _ = 96 * (Real.sqrt T * T ^ (1 / 4 : ℝ)) + 48 * Real.sqrt T := by ring
    _ = 96 * T ^ (3 / 4 : ℝ) + 48 * Real.sqrt T := by
      rw [hmulRpow]
    _ ≤ 96 * T ^ (3 / 4 : ℝ) + 48 * T ^ (3 / 4 : ℝ) := by gcongr
    _ = 144 * T ^ (3 / 4 : ℝ) := by ring

/-- The dyadic Hardy-Z integral has the `T^(3/4)` upper bound required in
Hardy's contradiction argument. -/
theorem exists_abs_integral_hardyZ_le_rpow_three_quarters :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      |∫ t in T..(2 * T), hardyZ t| ≤ C * T ^ (3 / 4 : ℝ) := by
  obtain ⟨κ, Cφ, hCφ, hphase⟩ :=
    exists_norm_exp_I_thetaPhase_sub_const_mul_exp_I_thetaModel_le_inv
  obtain ⟨Cz, Tz, hCz, hTz, hzeta⟩ := criticalLineZetaFirstApprox
  refine ⟨144 + 4 * Cφ + Cz, max Tz 1, by positivity,
    le_max_right _ _, ?_⟩
  intro T hT
  have hTz' : Tz ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hTtwo : T ≤ 2 * T := by linarith
  let N := firstZetaApproximationCutoff T
  let P : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.Icc 1 N,
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)
  let A : ℝ → ℂ := fun t => Complex.exp (I * thetaPhase t)
  let B : ℝ → ℂ := fun t =>
    Complex.exp (I * κ) * Complex.exp (I * thetaModel t)
  let Z : ℝ → ℂ := fun t => riemannZeta ((1 / 2 : ℂ) + I * t)
  let E : ℝ → ℂ := fun t => A t * Z t - B t * P t
  have hN : (N : ℝ) ≤ 4 * T := by
    exact Nat.floor_le (by positivity)
  have hsqrtN : Real.sqrt N ≤ 2 * Real.sqrt T := by
    have hsquare : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (by positivity)
    have hTsquare : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sqrt_nonneg T]
  have hPnorm : ∀ t : ℝ, ‖P t‖ ≤ 4 * Real.sqrt T := by
    intro t
    calc
      ‖P t‖ ≤ ∑ n ∈ Finset.Icc 1 N,
          ‖1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ := by
        dsimp only [P]
        exact norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹ := by
        apply Finset.sum_congr rfl
        intro n hnmem
        have hnpos : 0 < n := by
          have := (Finset.mem_Icc.mp hnmem).1
          omega
        rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos]
        norm_num
        rw [← Real.sqrt_eq_rpow]
      _ ≤ 2 * Real.sqrt N := sum_inv_sqrt_Icc_one_le_two_sqrt N
      _ ≤ 4 * Real.sqrt T := by linarith
  have hEnorm : ∀ t ∈ Icc T (2 * T),
      ‖E t‖ ≤ (4 * Cφ + Cz) / Real.sqrt T := by
    intro t htmem
    have ht1 : 1 ≤ t := hT1.trans htmem.1
    obtain ⟨R, hZR, hR⟩ := hzeta T t hTz' htmem
    have hR' : ‖Z t - P t‖ ≤ Cz / Real.sqrt T := by
      have heq : Z t - P t = R := by
        dsimp only [Z, P, N]
        rw [hZR]
        ring
      rw [heq]
      exact hR
    have hA : ‖A t‖ = 1 := by
      dsimp only [A]
      exact Complex.norm_exp_I_mul_ofReal _
    have hphase' : ‖A t - B t‖ ≤ Cφ / T := by
      have hp := hphase t ht1
      have hdiv : Cφ / t ≤ Cφ / T :=
        div_le_div_of_nonneg_left hCφ hTpos htmem.1
      exact hp.trans hdiv
    have hdecomp : E t = (A t - B t) * P t + A t * (Z t - P t) := by
      dsimp only [E]
      ring
    rw [hdecomp]
    calc
      ‖(A t - B t) * P t + A t * (Z t - P t)‖ ≤
          ‖(A t - B t) * P t‖ + ‖A t * (Z t - P t)‖ :=
        norm_add_le _ _
      _ =
          ‖A t - B t‖ * ‖P t‖ + ‖A t‖ * ‖Z t - P t‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ (Cφ / T) * (4 * Real.sqrt T) +
          1 * (Cz / Real.sqrt T) := by
        apply add_le_add
        · exact mul_le_mul hphase' (hPnorm t) (norm_nonneg _) (by positivity)
        · rw [hA]
          simpa using hR'
      _ = (4 * Cφ + Cz) / Real.sqrt T := by
        have hsqrtpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
        have hsquare : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
        field_simp [hTpos.ne', hsqrtpos.ne']
        nlinarith
  have hAcont : ContinuousOn A (Icc T (2 * T)) := by
    exact continuousOn_exp_I_thetaPhase_Ici_one.mono
      (fun t ht => hT1.trans ht.1)
  have hZcont : ContinuousOn Z (Icc T (2 * T)) := by
    intro t htmem
    apply ContinuousAt.continuousWithinAt
    have hs : (1 / 2 : ℂ) + I * t ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      norm_num at hre
    have hg : ContinuousAt (fun x : ℝ => (1 / 2 : ℂ) + I * x) t := by fun_prop
    change ContinuousAt
      (riemannZeta ∘ (fun x : ℝ => (1 / 2 : ℂ) + I * x)) t
    exact ContinuousAt.comp (f := fun x : ℝ => (1 / 2 : ℂ) + I * x)
      (differentiableAt_riemannZeta hs).continuousAt hg
  have hBcont : ContinuousOn B (Icc T (2 * T)) := by
    intro t htmem
    have htpos : 0 < t := hTpos.trans_le htmem.1
    apply ContinuousAt.continuousWithinAt
    have htheta : ContinuousAt thetaModel t := by
      change ContinuousAt (fun x : ℝ =>
        x / 2 * Real.log (x / (2 * Real.pi)) - x / 2 - Real.pi / 8) t
      fun_prop (disch := positivity)
    exact continuousAt_const.mul
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp htheta)).cexp
  have hPcont : ContinuousOn P (Icc T (2 * T)) := by
    apply continuousOn_finset_sum
    intro n hnmem
    have hn : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hnmem).1
      omega
    intro t _htmem
    apply ContinuousAt.continuousWithinAt
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [show (fun x : ℝ =>
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * x)) =
      (fun x : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * x)) by
      funext x
      exact inv_nat_cpow_criticalLine_eq_exp hn x]
    fun_prop
  have hEcont : ContinuousOn E (Icc T (2 * T)) :=
    (hAcont.mul hZcont).sub (hBcont.mul hPcont)
  have hEint : IntervalIntegrable E volume T (2 * T) :=
    ContinuousOn.intervalIntegrable_of_Icc hTtwo hEcont
  have hEIntegral :
      ‖∫ t in T..(2 * T), E t‖ ≤ (4 * Cφ + Cz) * Real.sqrt T := by
    have hconstInt : IntervalIntegrable
        (fun _ : ℝ => (4 * Cφ + Cz) / Real.sqrt T) volume T (2 * T) :=
      continuous_const.intervalIntegrable _ _
    calc
      ‖∫ t in T..(2 * T), E t‖ ≤
          ∫ _t in T..(2 * T), (4 * Cφ + Cz) / Real.sqrt T :=
        intervalIntegral.norm_integral_le_of_norm_le hTtwo
          (Filter.Eventually.of_forall (fun t ht => hEnorm t ⟨ht.1.le, ht.2⟩)) hconstInt
      _ = (4 * Cφ + Cz) * Real.sqrt T := by
        rw [intervalIntegral.integral_const]
        have hsqrtpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
        have hsquare : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
        simp only [smul_eq_mul]
        field_simp [hsqrtpos.ne']
        nlinarith
  have hmain :
      ‖∫ t in T..(2 * T), B t * P t‖ ≤ 144 * T ^ (3 / 4 : ℝ) := by
    have heq :
        (∫ t in T..(2 * T), B t * P t) =
          Complex.exp (I * κ) *
            ∫ t in T..(2 * T),
              Complex.exp (I * thetaModel t) * P t := by
      calc
        (∫ t in T..(2 * T), B t * P t) =
            ∫ t in T..(2 * T), Complex.exp (I * κ) *
              (Complex.exp (I * thetaModel t) * P t) := by
          apply intervalIntegral.integral_congr
          intro t _
          dsimp only [B]
          ring
        _ = Complex.exp (I * κ) *
            ∫ t in T..(2 * T),
              Complex.exp (I * thetaModel t) * P t :=
          intervalIntegral.integral_const_mul _ _
    rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    simpa only [P, N] using
      norm_integral_thetaModel_dirichletPolynomial_le_rpow_three_quarters hT1
  have hAZint : IntervalIntegrable (fun t => A t * Z t) volume T (2 * T) :=
    ContinuousOn.intervalIntegrable_of_Icc hTtwo (hAcont.mul hZcont)
  have hBPint : IntervalIntegrable (fun t => B t * P t) volume T (2 * T) :=
    ContinuousOn.intervalIntegrable_of_Icc hTtwo (hBcont.mul hPcont)
  have hsplit :
      (∫ t in T..(2 * T), A t * Z t) =
        (∫ t in T..(2 * T), B t * P t) + ∫ t in T..(2 * T), E t := by
    rw [← intervalIntegral.integral_add hBPint hEint]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [E]
    ring
  have hreal :
      (∫ t in T..(2 * T), hardyZ t) =
        (∫ t in T..(2 * T), A t * Z t).re := by
    have hmap := Complex.reCLM.intervalIntegral_comp_comm hAZint
    have hmap' :
        (∫ t in T..(2 * T), (A t * Z t).re) =
          (∫ t in T..(2 * T), A t * Z t).re := by
      simpa using hmap
    rw [← hmap']
    apply intervalIntegral.integral_congr
    intro t _
    exact hardyZ_eq_re_exp_I_thetaPhase_mul_zeta t
  rw [hreal]
  calc
    |(∫ t in T..(2 * T), A t * Z t).re| ≤
        ‖∫ t in T..(2 * T), A t * Z t‖ := Complex.abs_re_le_norm _
    _ = ‖(∫ t in T..(2 * T), B t * P t) +
        ∫ t in T..(2 * T), E t‖ := by rw [hsplit]
    _ ≤ ‖∫ t in T..(2 * T), B t * P t‖ +
        ‖∫ t in T..(2 * T), E t‖ := norm_add_le _ _
    _ ≤ 144 * T ^ (3 / 4 : ℝ) +
        (4 * Cφ + Cz) * Real.sqrt T := add_le_add hmain hEIntegral
    _ ≤ 144 * T ^ (3 / 4 : ℝ) +
        (4 * Cφ + Cz) * T ^ (3 / 4 : ℝ) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)) (by positivity))
    _ = (144 + 4 * Cφ + Cz) * T ^ (3 / 4 : ℝ) := by ring

end HardyTheorem
