import HardyTheorem.HardyPhasePartialSecondMoment

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

set_option maxHeartbeats 1200000

/-- The complete linearized Hardy sum is the sum of its indices below and
above any prescribed natural cutoff. -/
theorem hardyPhaseLinearizedSum_eq_partial_add_partial
    (T delta t : ℝ) (M : ℕ) :
    hardyPhaseLinearizedSum T delta t =
      hardyPhaseLinearizedPartialSum
          ((Finset.Icc 1 (firstZetaApproximationCutoff T)).filter
            fun n ↦ n < M) delta t +
        hardyPhaseLinearizedPartialSum
          ((Finset.Icc 1 (firstZetaApproximationCutoff T)).filter
            fun n ↦ ¬n < M) delta t := by
  rw [hardyPhaseLinearizedSum, hardyPhaseLinearizedPartialSum,
    hardyPhaseLinearizedPartialSum]
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (Finset.Icc 1 (firstZetaApproximationCutoff T))
      (fun n ↦ n < M)
      (fun n ↦ hardyPhaseLinearizedCoeff n delta t)).symm

/-- A two-band estimate with constants independent of the window length.
The near band uses smoothing scale `sqrt T`; the far high band uses
`sqrt (T / delta)`.  The residual square-root term is the finite endpoint
cost of the near band. -/
theorem exists_integral_normSq_hardyPhaseLinearizedSum_le_twoBand :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ delta : ℝ, 1 ≤ delta →
        ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T ≥ T0,
          (∫ t in T..2 * T - delta,
            Complex.normSq (hardyPhaseLinearizedSum T delta t)) ≤
            A * delta * T +
              B * (delta ^ 4 + delta) * Real.sqrt T := by
  let Kc : ℝ := 5 * Real.pi + 4
  let logTwoSq : ℝ := (Real.log 2) ^ 2
  let A : ℝ := 2 * (200 + (8 + 392 * Kc) / logTwoSq)
  let B : ℝ := 2 * (4832 * Kc)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoSq : 0 < logTwoSq := by
    dsimp only [logTwoSq]
    positivity
  have hKc : 0 < Kc := by
    dsimp only [Kc]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨A, B, hA, hB, ?_⟩
  intro delta hdelta
  let T0 : ℝ := max 1
    (max delta (max (128 * Real.pi) (2 * Real.pi * delta ^ 2)))
  refine ⟨T0, le_max_left _ _, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hdeltapos : 0 < delta := zero_lt_one.trans_le hdelta
  have hrest :
      max delta (max (128 * Real.pi) (2 * Real.pi * delta ^ 2)) ≤ T :=
    (le_max_right (1 : ℝ) _).trans hT
  have hdeltaT : delta ≤ T := (le_max_left _ _).trans hrest
  have hrest' : max (128 * Real.pi) (2 * Real.pi * delta ^ 2) ≤ T :=
    (le_max_right delta _).trans hrest
  have hscaleT : 128 * Real.pi ≤ T := (le_max_left _ _).trans hrest'
  have hwindowT : 2 * Real.pi * delta ^ 2 ≤ T :=
    (le_max_right _ _).trans hrest'
  have hab : T ≤ 2 * T - delta := by linarith
  have hlen0 : 0 ≤ T - delta := sub_nonneg.mpr hdeltaT
  have hlenEq : (2 * T - delta) - T = T - delta := by ring
  have hlenAbs : |(2 * T - delta) - T| = T - delta := by
    rw [hlenEq, abs_of_nonneg hlen0]
  have hsqrtTpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hsqrtTsq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
  have hratioPos : 0 < T / delta := div_pos hTpos hdeltapos
  have hsqrtRatioPos : 0 < Real.sqrt (T / delta) :=
    Real.sqrt_pos.2 hratioPos
  have hsqrtRatioSq : (Real.sqrt (T / delta)) ^ 2 = T / delta :=
    Real.sq_sqrt hratioPos.le
  let N : ℕ := firstZetaApproximationCutoff T
  have hNpos : 0 < N := by
    dsimp only [N, firstZetaApproximationCutoff]
    exact Nat.floor_pos.mpr (by nlinarith)
  have hNreal : (N : ℝ) ≤ 4 * T := by
    dsimp only [N, firstZetaApproximationCutoff]
    exact Nat.floor_le (by positivity)
  have hscale : ∀ t ∈ Set.Icc T (2 * T - delta),
      8 ≤ hardyPhaseStationaryScale t := by
    intro t ht
    unfold hardyPhaseStationaryScale
    have ht0 : 0 ≤ t := hTpos.le.trans ht.1
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 8) (by positivity)]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    calc
      8 ^ 2 * (2 * Real.pi) = 128 * Real.pi := by ring
      _ ≤ T := hscaleT
      _ ≤ t := ht.1
  have hwindow : ∀ t ∈ Set.Icc T (2 * T - delta),
      delta ≤ hardyPhaseStationaryScale t := by
    intro t ht
    unfold hardyPhaseStationaryScale
    have ht0 : 0 ≤ t := hTpos.le.trans ht.1
    rw [Real.le_sqrt hdelta0 (by positivity)]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    calc
      delta ^ 2 * (2 * Real.pi) = 2 * Real.pi * delta ^ 2 := by ring
      _ ≤ T := hwindowT
      _ ≤ t := ht.1
  have hscale2T : 8 ≤ hardyPhaseStationaryScale (2 * T) := by
    unfold hardyPhaseStationaryScale
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 8) (by positivity)]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith
  obtain ⟨Klow, Khigh, L, hlowScale, hlowCutoff, hhighScale,
      hhighUpper, hhighCutoff, hlastCutoff⟩ :=
    exists_hardyPhaseDyadicCutoffs
      (t := 2 * T) (by positivity) hscale2T N
  let M : ℕ := 2 ^ Khigh
  let s : Finset ℕ := Finset.Icc 1 N
  let near : Finset ℕ := s.filter fun n ↦ n < M
  let far : Finset ℕ := s.filter fun n ↦ ¬n < M
  have hMpos : 0 < M := by
    dsimp only [M]
    positivity
  have hMcast : (M : ℝ) = (2 : ℝ) ^ Khigh := by
    norm_num [M]
  have hstationary2T_le_sqrtT :
      hardyPhaseStationaryScale (2 * T) ≤ Real.sqrt T := by
    unfold hardyPhaseStationaryScale
    apply Real.sqrt_le_sqrt
    have hpiOne : 1 ≤ Real.pi := by
      nlinarith [Real.pi_gt_three]
    calc
      2 * T / (2 * Real.pi) = T / Real.pi := by ring
      _ ≤ T := (div_le_iff₀ Real.pi_pos).2 (by nlinarith)
  have hMreal : (M : ℝ) ≤ 4 * Real.sqrt T := by
    rw [hMcast]
    exact hhighUpper.trans
      (mul_le_mul_of_nonneg_left hstationary2T_le_sqrtT (by norm_num))
  have hnearPos : ∀ n ∈ near, n ≠ 0 := by
    intro n hn
    have hsMem : n ∈ s := (Finset.mem_filter.mp hn).1
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hsMem).1
  have hfarPos : ∀ n ∈ far, n ≠ 0 := by
    intro n hn
    have hsMem : n ∈ s := (Finset.mem_filter.mp hn).1
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hsMem).1
  have hnearUpper : ∀ n ∈ near, n ≤ M := by
    intro n hn
    exact (Nat.le_of_lt (Finset.mem_filter.mp hn).2)
  have hfarUpper : ∀ n ∈ far, n ≤ N := by
    intro n hn
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
  have hfarLower : ∀ n ∈ far, 2 ^ Khigh ≤ n := by
    intro n hn
    have hnot : ¬n < M := (Finset.mem_filter.mp hn).2
    dsimp only [M] at hnot
    omega
  have hfarLast : ∀ n ∈ far, n < 2 ^ L := by
    intro n hn
    exact (hfarUpper n hn).trans_lt hlastCutoff
  have hscaleFar : ∀ t ∈ Set.Icc T (2 * T - delta),
      2 * hardyPhaseStationaryScale t ≤ (2 : ℝ) ^ Khigh := by
    intro t ht
    have htTwo : t ≤ 2 * T := ht.2.trans (sub_le_self _ hdelta0)
    have hrle :
        hardyPhaseStationaryScale t ≤
          hardyPhaseStationaryScale (2 * T) := by
      unfold hardyPhaseStationaryScale
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right htTwo (by positivity)
    exact (mul_le_mul_of_nonneg_left hrle (by norm_num)).trans hhighScale
  have hnearEnergy : ∀ t ∈ Set.Icc T (2 * T - delta),
      (∑ n ∈ near,
        Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
          200 * delta := by
    intro t ht
    exact sum_normSq_hardyPhaseLinearizedCoeff_full_le_mul
      near M (hTpos.trans_le ht.1) hdelta (hscale t ht) (hwindow t ht)
        hnearPos hnearUpper
  have hnearDeriv : ∀ t ∈ Set.Icc T (2 * T - delta),
      (∑ n ∈ near,
        Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
          204 * delta ^ 4 / T ^ 2 := by
    intro t ht
    have hraw := sum_normSq_deriv_hardyPhaseWindowCoeff_full_le_mul
      near M (hTpos.trans_le ht.1) hdelta (hscale t ht)
        hnearPos hnearUpper
    have hsq : T ^ 2 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - T), ht.1]
    exact hraw.trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hTpos) hsq)
  have hfarEnergy : ∀ t ∈ Set.Icc T (2 * T - delta),
      (∑ n ∈ far,
        Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
          8 / logTwoSq := by
    intro t ht
    simpa only [logTwoSq] using
      sum_normSq_hardyPhaseLinearizedCoeff_far_high_le
        far Khigh L (hTpos.trans_le ht.1) hdelta0 (hscaleFar t ht)
          hfarPos hfarLower hfarLast
  have hfarDeriv : ∀ t ∈ Set.Icc T (2 * T - delta),
      (∑ n ∈ far,
        Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
          25 * delta ^ 2 / (T ^ 2 * logTwoSq) := by
    intro t ht
    have hraw := sum_normSq_deriv_hardyPhaseWindowCoeff_far_high_le
      far Khigh L (hTpos.trans_le ht.1) hdelta (hscaleFar t ht)
        hfarPos hfarLower hfarLast
    have hsq : T ^ 2 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - T), ht.1]
    have hden : T ^ 2 * logTwoSq ≤ t ^ 2 * logTwoSq :=
      mul_le_mul_of_nonneg_right hsq hlogTwoSq.le
    simpa only [logTwoSq] using hraw.trans
      (div_le_div_of_nonneg_left (by positivity)
        (mul_pos (sq_pos_of_pos hTpos) hlogTwoSq) hden)
  have hnearRaw :=
    integral_normSq_hardyPhaseLinearizedPartialSum_le
      hMpos near hTpos hab hsqrtTpos hnearPos hnearUpper
        hnearEnergy hnearDeriv
  have hfarRaw :=
    integral_normSq_hardyPhaseLinearizedPartialSum_le
      hNpos far hTpos hab hsqrtRatioPos hfarPos hfarUpper
        hfarEnergy hfarDeriv
  have hnearBound :
      (∫ t in T..2 * T - delta,
        Complex.normSq (hardyPhaseLinearizedPartialSum near delta t)) ≤
        200 * delta * T +
          4832 * Kc * (delta ^ 4 + delta) * Real.sqrt T := by
    rw [hlenEq, abs_of_nonneg hlen0, hsqrtTsq] at hnearRaw
    calc
      (∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedPartialSum near delta t)) ≤
          (T - delta) * (200 * delta) +
            4 * Kc * M * (200 * delta) +
            (T - delta) *
              (2 * Kc * M *
                (T * (204 * delta ^ 4 / T ^ 2) +
                  T⁻¹ * (200 * delta))) := by
        simpa only [Kc] using hnearRaw
      _ ≤ 200 * delta * T +
          4832 * Kc * (delta ^ 4 + delta) * Real.sqrt T := by
        have hsqrt0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
        have hquartic : 0 ≤ delta ^ 4 := by positivity
        have hsum0 : 0 ≤ delta ^ 4 + delta := add_nonneg hquartic hdelta0
        have hdeltaSum : delta ≤ delta ^ 4 + delta := by linarith
        have hlenLe : T - delta ≤ T := sub_le_self T hdelta0
        have hM0 : 0 ≤ (M : ℝ) := by positivity
        have hdiag : (T - delta) * (200 * delta) ≤ 200 * delta * T := by
          nlinarith
        have hendpoint :
            4 * Kc * M * (200 * delta) ≤
              3200 * Kc * (delta ^ 4 + delta) * Real.sqrt T := by
          calc
            4 * Kc * M * (200 * delta) ≤
                4 * Kc * (4 * Real.sqrt T) * (200 * delta) := by
              gcongr
            _ = 3200 * Kc * delta * Real.sqrt T := by ring
            _ ≤ 3200 * Kc * (delta ^ 4 + delta) * Real.sqrt T := by
              gcongr
        have hinner :
            T * (204 * delta ^ 4 / T ^ 2) + T⁻¹ * (200 * delta) =
              (204 * delta ^ 4 + 200 * delta) / T := by
          field_simp [hTpos.ne']
        have hcoeff :
            204 * delta ^ 4 + 200 * delta ≤
              204 * (delta ^ 4 + delta) := by nlinarith
        have hvariation :
            (T - delta) *
                (2 * Kc * M *
                  (T * (204 * delta ^ 4 / T ^ 2) +
                    T⁻¹ * (200 * delta))) ≤
              1632 * Kc * (delta ^ 4 + delta) * Real.sqrt T := by
          rw [hinner]
          have hfrac0 : 0 ≤ (204 * delta ^ 4 + 200 * delta) / T := by
            positivity
          calc
            (T - delta) *
                (2 * Kc * M * ((204 * delta ^ 4 + 200 * delta) / T)) ≤
                T * (2 * Kc * (4 * Real.sqrt T) *
                  ((204 * delta ^ 4 + 200 * delta) / T)) := by
              gcongr
            _ = 8 * Kc * Real.sqrt T *
                (204 * delta ^ 4 + 200 * delta) := by
              field_simp [hTpos.ne']
              ring
            _ ≤ 8 * Kc * Real.sqrt T *
                (204 * (delta ^ 4 + delta)) := by
              exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
            _ = 1632 * Kc * (delta ^ 4 + delta) * Real.sqrt T := by ring
        linarith
  have hfarBound :
      (∫ t in T..2 * T - delta,
        Complex.normSq (hardyPhaseLinearizedPartialSum far delta t)) ≤
        ((8 + 392 * Kc) / logTwoSq) * delta * T := by
    rw [hlenEq, abs_of_nonneg hlen0, hsqrtRatioSq] at hfarRaw
    have hqInv : (T / delta)⁻¹ = delta / T := by
      field_simp [hTpos.ne', hdeltapos.ne']
    rw [hqInv] at hfarRaw
    dsimp only [Kc, logTwoSq] at hfarRaw ⊢
    have hlogSqPos : 0 < (Real.log 2) ^ 2 := by positivity
    have hlenLe : T - delta ≤ T := sub_le_self T hdelta0
    have hE0 : 0 ≤ 8 / (Real.log 2) ^ 2 := by positivity
    have hD0 : 0 ≤ 25 * delta ^ 2 / (T ^ 2 * (Real.log 2) ^ 2) := by
      positivity
    have hdiag :
        (T - delta) * (8 / (Real.log 2) ^ 2) ≤
          (8 / (Real.log 2) ^ 2) * delta * T := by
      have hdeltaOne : (1 : ℝ) ≤ delta := hdelta
      calc
        (T - delta) * (8 / (Real.log 2) ^ 2) ≤
            T * (8 / (Real.log 2) ^ 2) :=
          mul_le_mul_of_nonneg_right hlenLe hE0
        _ = 1 * (T * (8 / (Real.log 2) ^ 2)) := by ring
        _ ≤ delta * (T * (8 / (Real.log 2) ^ 2)) :=
          mul_le_mul_of_nonneg_right hdelta (mul_nonneg hTpos.le hE0)
        _ = (8 / (Real.log 2) ^ 2) * delta * T := by ring
    have hendpoint :
        4 * (5 * Real.pi + 4) * N * (8 / (Real.log 2) ^ 2) ≤
          (128 * (5 * Real.pi + 4) / (Real.log 2) ^ 2) *
            delta * T := by
      calc
        4 * (5 * Real.pi + 4) * N * (8 / (Real.log 2) ^ 2) ≤
            4 * (5 * Real.pi + 4) * (4 * T) *
              (8 / (Real.log 2) ^ 2) := by
          gcongr
        _ ≤ (128 * (5 * Real.pi + 4) / (Real.log 2) ^ 2) *
              delta * T := by
          calc
            4 * (5 * Real.pi + 4) * (4 * T) *
                (8 / (Real.log 2) ^ 2) =
                (128 * (5 * Real.pi + 4) / (Real.log 2) ^ 2) * T := by ring
            _ = 1 * ((128 * (5 * Real.pi + 4) /
                (Real.log 2) ^ 2) * T) := by ring
            _ ≤ delta * ((128 * (5 * Real.pi + 4) /
                (Real.log 2) ^ 2) * T) :=
              mul_le_mul_of_nonneg_right hdelta (by positivity)
            _ = (128 * (5 * Real.pi + 4) / (Real.log 2) ^ 2) *
                delta * T := by ring
    have hinner :
        (T / delta) *
              (25 * delta ^ 2 / (T ^ 2 * (Real.log 2) ^ 2)) +
            (delta / T) * (8 / (Real.log 2) ^ 2) =
          33 * delta / (T * (Real.log 2) ^ 2) := by
      field_simp [hTpos.ne', hdeltapos.ne', hlogSqPos.ne']
      ring
    have hvariation :
        (T - delta) *
            (2 * (5 * Real.pi + 4) * N *
              ((T / delta) *
                  (25 * delta ^ 2 / (T ^ 2 * (Real.log 2) ^ 2)) +
                (delta / T) * (8 / (Real.log 2) ^ 2))) ≤
          (264 * (5 * Real.pi + 4) / (Real.log 2) ^ 2) *
            delta * T := by
      rw [hinner]
      calc
        (T - delta) *
            (2 * (5 * Real.pi + 4) * N *
              (33 * delta / (T * (Real.log 2) ^ 2))) ≤
            T * (2 * (5 * Real.pi + 4) * (4 * T) *
              (33 * delta / (T * (Real.log 2) ^ 2))) := by
          gcongr
        _ = (264 * (5 * Real.pi + 4) / (Real.log 2) ^ 2) *
              delta * T := by
          field_simp [hTpos.ne', hlogSqPos.ne']
          ring
    calc
      (∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedPartialSum far delta t)) ≤
          (T - delta) * (8 / (Real.log 2) ^ 2) +
            4 * (5 * Real.pi + 4) * N * (8 / (Real.log 2) ^ 2) +
            (T - delta) *
              (2 * (5 * Real.pi + 4) * N *
                ((T / delta) *
                    (25 * delta ^ 2 / (T ^ 2 * (Real.log 2) ^ 2)) +
                  (delta / T) * (8 / (Real.log 2) ^ 2))) := hfarRaw
      _ ≤ ((8 + 392 * (5 * Real.pi + 4)) /
          (Real.log 2) ^ 2) * delta * T := by
        calc
          (T - delta) * (8 / (Real.log 2) ^ 2) +
              4 * (5 * Real.pi + 4) * N * (8 / (Real.log 2) ^ 2) +
              (T - delta) *
                (2 * (5 * Real.pi + 4) * N *
                  ((T / delta) *
                      (25 * delta ^ 2 / (T ^ 2 * (Real.log 2) ^ 2)) +
                    (delta / T) * (8 / (Real.log 2) ^ 2))) ≤
              (8 / (Real.log 2) ^ 2) * delta * T +
                (128 * (5 * Real.pi + 4) / (Real.log 2) ^ 2) * delta * T +
                (264 * (5 * Real.pi + 4) / (Real.log 2) ^ 2) * delta * T :=
            add_le_add (add_le_add hdiag hendpoint) hvariation
          _ = ((8 + 392 * (5 * Real.pi + 4)) /
              (Real.log 2) ^ 2) * delta * T := by ring
  have hnearCoeffCont : ∀ n ∈ near,
      ContinuousOn (fun t ↦ (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta t))
        (Set.Icc T (2 * T - delta)) := by
    intro n hn t ht
    exact ((hasDerivAt_hardyPhaseWindowCoeff n
      (hTpos.trans_le ht.1)).star).continuousAt.continuousWithinAt
  have hfarCoeffCont : ∀ n ∈ far,
      ContinuousOn (fun t ↦ (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta t))
        (Set.Icc T (2 * T - delta)) := by
    intro n hn t ht
    exact ((hasDerivAt_hardyPhaseWindowCoeff n
      (hTpos.trans_le ht.1)).star).continuousAt.continuousWithinAt
  let nearPoly : ℝ → ℂ :=
    MathlibAux.timeDependentLogPolynomial near
      (fun t n ↦ (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta t))
  let farPoly : ℝ → ℂ :=
    MathlibAux.timeDependentLogPolynomial far
      (fun t n ↦ (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta t))
  have hnearPolyCont : ContinuousOn nearPoly (Set.Icc T (2 * T - delta)) := by
    simpa only [nearPoly] using
      MathlibAux.continuousOn_timeDependentLogPolynomial near _ hnearCoeffCont
  have hfarPolyCont : ContinuousOn farPoly (Set.Icc T (2 * T - delta)) := by
    simpa only [farPoly] using
      MathlibAux.continuousOn_timeDependentLogPolynomial far _ hfarCoeffCont
  have hnearInt : IntervalIntegrable
      (fun t ↦ Complex.normSq (hardyPhaseLinearizedPartialSum near delta t))
      volume T (2 * T - delta) := by
    have hp : IntervalIntegrable (fun t ↦ Complex.normSq (nearPoly t))
        volume T (2 * T - delta) :=
      (Complex.continuous_normSq.comp_continuousOn hnearPolyCont).intervalIntegrable_of_Icc hab
    apply hp.congr
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact (normSq_hardyPhaseLinearizedPartialSum_eq_logPolynomial
      near (hTpos.trans ht.1) hnearPos).symm
  have hfarInt : IntervalIntegrable
      (fun t ↦ Complex.normSq (hardyPhaseLinearizedPartialSum far delta t))
      volume T (2 * T - delta) := by
    have hp : IntervalIntegrable (fun t ↦ Complex.normSq (farPoly t))
        volume T (2 * T - delta) :=
      (Complex.continuous_normSq.comp_continuousOn hfarPolyCont).intervalIntegrable_of_Icc hab
    apply hp.congr
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact (normSq_hardyPhaseLinearizedPartialSum_eq_logPolynomial
      far (hTpos.trans ht.1) hfarPos).symm
  have hsCoeffCont : ∀ n ∈ s,
      ContinuousOn (fun t ↦ (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta t))
        (Set.Icc T (2 * T - delta)) := by
    intro n hn t ht
    exact ((hasDerivAt_hardyPhaseWindowCoeff n
      (hTpos.trans_le ht.1)).star).continuousAt.continuousWithinAt
  let fullPoly : ℝ → ℂ :=
    MathlibAux.timeDependentLogPolynomial s
      (fun t n ↦ (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta t))
  have hfullPolyCont : ContinuousOn fullPoly (Set.Icc T (2 * T - delta)) := by
    simpa only [fullPoly] using
      MathlibAux.continuousOn_timeDependentLogPolynomial s _ hsCoeffCont
  have hfullInt : IntervalIntegrable
      (fun t ↦ Complex.normSq (hardyPhaseLinearizedSum T delta t))
      volume T (2 * T - delta) := by
    have hp : IntervalIntegrable (fun t ↦ Complex.normSq (fullPoly t))
        volume T (2 * T - delta) :=
      (Complex.continuous_normSq.comp_continuousOn hfullPolyCont).intervalIntegrable_of_Icc hab
    apply hp.congr
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    symm
    change Complex.normSq (hardyPhaseLinearizedSum T delta t) =
      Complex.normSq (fullPoly t)
    rw [normSq_hardyPhaseLinearizedSum_eq_negLogPolynomial
      (hTpos.trans ht.1), hardyPhaseNegLogPolynomial_eq_conj_positive,
      Complex.normSq_conj]
  have hmajorantInt : IntervalIntegrable
      (fun t ↦
        2 * Complex.normSq (hardyPhaseLinearizedPartialSum near delta t) +
          2 * Complex.normSq (hardyPhaseLinearizedPartialSum far delta t))
      volume T (2 * T - delta) :=
    (hnearInt.const_mul 2).add (hfarInt.const_mul 2)
  have hpoint : ∀ t ∈ Set.Icc T (2 * T - delta),
      Complex.normSq (hardyPhaseLinearizedSum T delta t) ≤
        2 * Complex.normSq (hardyPhaseLinearizedPartialSum near delta t) +
          2 * Complex.normSq (hardyPhaseLinearizedPartialSum far delta t) := by
    intro t ht
    rw [hardyPhaseLinearizedSum_eq_partial_add_partial T delta t M]
    simp only [Complex.normSq_eq_norm_sq]
    have hnorm := norm_add_le
      (hardyPhaseLinearizedPartialSum near delta t)
      (hardyPhaseLinearizedPartialSum far delta t)
    have hsq :
        ‖hardyPhaseLinearizedPartialSum near delta t +
            hardyPhaseLinearizedPartialSum far delta t‖ ^ 2 ≤
          (‖hardyPhaseLinearizedPartialSum near delta t‖ +
            ‖hardyPhaseLinearizedPartialSum far delta t‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    calc
      ‖hardyPhaseLinearizedPartialSum near delta t +
          hardyPhaseLinearizedPartialSum far delta t‖ ^ 2 ≤
          (‖hardyPhaseLinearizedPartialSum near delta t‖ +
            ‖hardyPhaseLinearizedPartialSum far delta t‖) ^ 2 := hsq
      _ ≤ 2 * ‖hardyPhaseLinearizedPartialSum near delta t‖ ^ 2 +
          2 * ‖hardyPhaseLinearizedPartialSum far delta t‖ ^ 2 := by
        nlinarith [sq_nonneg
          (‖hardyPhaseLinearizedPartialSum near delta t‖ -
            ‖hardyPhaseLinearizedPartialSum far delta t‖)]
  have hmono := intervalIntegral.integral_mono_on
    hab hfullInt hmajorantInt hpoint
  have hsplitIntegral :
      (∫ t in T..2 * T - delta,
        (2 * Complex.normSq (hardyPhaseLinearizedPartialSum near delta t) +
          2 * Complex.normSq (hardyPhaseLinearizedPartialSum far delta t))) =
        2 * (∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedPartialSum near delta t)) +
        2 * (∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedPartialSum far delta t)) := by
    rw [intervalIntegral.integral_add (hnearInt.const_mul 2)
      (hfarInt.const_mul 2)]
    simp only [intervalIntegral.integral_const_mul]
  rw [hsplitIntegral] at hmono
  calc
    (∫ t in T..2 * T - delta,
        Complex.normSq (hardyPhaseLinearizedSum T delta t)) ≤
        2 * (∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedPartialSum near delta t)) +
        2 * (∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedPartialSum far delta t)) := hmono
    _ ≤ 2 *
          (200 * delta * T +
            4832 * Kc * (delta ^ 4 + delta) * Real.sqrt T) +
        2 * (((8 + 392 * Kc) / logTwoSq) * delta * T) := by
      gcongr
    _ = A * delta * T +
        B * (delta ^ 4 + delta) * Real.sqrt T := by
      dsimp only [A, B]
      ring

end HardyTheorem
