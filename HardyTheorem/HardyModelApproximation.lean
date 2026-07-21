import HardyTheorem.HardyIntegralUpperBound

open Complex Set

namespace HardyTheorem

/-- On a Hardy dyadic interval, rotating the first zeta approximation by the
exact Gamma phase differs from the elementary phase model by `O(T⁻¹/²)`.

This exposes the pointwise model estimate used internally by the proof of the
Hardy-Z integral upper bound. -/
theorem exists_norm_rotated_riemannZeta_sub_thetaModel_dirichletPolynomial_le_inv_sqrt :
    ∃ κ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Icc T (2 * T) →
        ‖Complex.exp (I * thetaPhase t) *
              riemannZeta ((1 / 2 : ℂ) + I * t) -
            Complex.exp (I * κ) * Complex.exp (I * thetaModel t) *
              (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
                1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
          C / Real.sqrt T := by
  obtain ⟨κ, Cφ, hCφ, hphase⟩ :=
    exists_norm_exp_I_thetaPhase_sub_const_mul_exp_I_thetaModel_le_inv
  obtain ⟨Cz, Tz, hCz, hTz, hzeta⟩ := criticalLineZetaFirstApprox
  refine ⟨κ, 4 * Cφ + Cz, max Tz 1, by positivity,
    le_max_right _ _, ?_⟩
  intro T t hT htmem
  have hTz' : Tz ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  let N := firstZetaApproximationCutoff T
  let P : ℝ → ℂ := fun u =>
    ∑ n ∈ Finset.Icc 1 N,
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)
  let A : ℝ → ℂ := fun u => Complex.exp (I * thetaPhase u)
  let B : ℝ → ℂ := fun u =>
    Complex.exp (I * κ) * Complex.exp (I * thetaModel u)
  let Z : ℝ → ℂ := fun u => riemannZeta ((1 / 2 : ℂ) + I * u)
  have hN : (N : ℝ) ≤ 4 * T := by
    exact Nat.floor_le (by positivity)
  have hsqrtN : Real.sqrt N ≤ 2 * Real.sqrt T := by
    have hsquare : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (by positivity)
    have hTsquare : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sqrt_nonneg T]
  have hPnorm : ∀ u : ℝ, ‖P u‖ ≤ 4 * Real.sqrt T := by
    intro u
    calc
      ‖P u‖ ≤ ∑ n ∈ Finset.Icc 1 N,
          ‖1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)‖ := by
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
  have hdecomp :
      A t * Z t - B t * P t =
        (A t - B t) * P t + A t * (Z t - P t) := by
    ring
  change ‖A t * Z t - B t * P t‖ ≤
    (4 * Cφ + Cz) / Real.sqrt T
  rw [hdecomp]
  calc
    ‖(A t - B t) * P t + A t * (Z t - P t)‖ ≤
        ‖(A t - B t) * P t‖ + ‖A t * (Z t - P t)‖ :=
      norm_add_le _ _
    _ = ‖A t - B t‖ * ‖P t‖ + ‖A t‖ * ‖Z t - P t‖ := by
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

end HardyTheorem
