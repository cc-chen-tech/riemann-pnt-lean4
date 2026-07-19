import HardyTheorem.CriticalLineShortDirichlet

open scoped BigOperators

namespace MathlibAux

private theorem inv_nat_mul_log_sq_le_inv_log_sub_inv_log
    {n : ℕ} (hn : 3 ≤ n) :
    1 / ((n : ℝ) * (Real.log n) ^ 2) ≤
      1 / Real.log ((n - 1 : ℕ) : ℝ) - 1 / Real.log n := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hnm1pos : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlognm1 : 0 < Real.log ((n - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n - 1 by omega))
  have hlogmono : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log n := by
    exact Real.strictMonoOn_log.monotoneOn hnm1pos hnpos (by exact_mod_cast (Nat.sub_le n 1))
  have hratio : 0 < ((n - 1 : ℕ) : ℝ) / (n : ℝ) := div_pos hnm1pos hnpos
  have hlogratio := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hnm1pos.ne' hnpos.ne'] at hlogratio
  have hgap : 1 / (n : ℝ) ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := by
    rw [hcast] at hlogratio
    have hratio_alg : (((n : ℝ) - 1) / (n : ℝ) - 1) = -(1 / (n : ℝ)) := by
      field_simp
      ring
    rw [hratio_alg] at hlogratio
    rw [← hcast] at hlogratio
    linarith
  have hdenom : Real.log ((n - 1 : ℕ) : ℝ) * Real.log n ≤ (Real.log n) ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_right hlogmono hlogn.le
  have hinvden :
      1 / (Real.log n) ^ 2 ≤
        1 / (Real.log ((n - 1 : ℕ) : ℝ) * Real.log n) :=
    one_div_le_one_div_of_le (mul_pos hlognm1 hlogn) hdenom
  calc
    1 / ((n : ℝ) * (Real.log n) ^ 2) =
        (1 / (n : ℝ)) * (1 / (Real.log n) ^ 2) := by
          field_simp
    _ ≤ (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) *
        (1 / (Real.log n) ^ 2) :=
      mul_le_mul_of_nonneg_right hgap (by positivity)
    _ ≤ (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) *
        (1 / (Real.log ((n - 1 : ℕ) : ℝ) * Real.log n)) :=
      mul_le_mul_of_nonneg_left hinvden (sub_nonneg.mpr hlogmono)
    _ = 1 / Real.log ((n - 1 : ℕ) : ℝ) - 1 / Real.log n := by
      field_simp

private theorem sum_Icc_inv_nat_mul_log_sq_le_boundary
    {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
      1 / ((2 : ℝ) * (Real.log 2) ^ 2) +
        1 / Real.log 2 - 1 / Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | @succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1)]
      calc
        (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * (Real.log n) ^ 2)) +
              1 / (((N + 1 : ℕ) : ℝ) *
                (Real.log ((N + 1 : ℕ) : ℝ)) ^ 2) ≤
            (1 / ((2 : ℝ) * (Real.log 2) ^ 2) +
                1 / Real.log 2 - 1 / Real.log N) +
              (1 / Real.log (((N + 1) - 1 : ℕ) : ℝ) -
                1 / Real.log ((N + 1 : ℕ) : ℝ)) :=
          add_le_add ih (inv_nat_mul_log_sq_le_inv_log_sub_inv_log (by omega))
        _ = 1 / ((2 : ℝ) * (Real.log 2) ^ 2) +
              1 / Real.log 2 - 1 / Real.log ((N + 1 : ℕ) : ℝ) := by
          rw [Nat.add_sub_cancel]
          ring

/-- A concrete uniform bound for the logarithmic square weight. The constant
`4` is deliberately elementary rather than optimized. -/
theorem sum_Icc_inv_nat_mul_log_sq_le_four (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤ 4 := by
  by_cases hN : 2 ≤ N
  · have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
      exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlog2pos : 0 < Real.log 2 := by linarith
    have hinvlog2 : 1 / Real.log 2 ≤ 2 := by
      rw [div_le_iff₀ hlog2pos]
      linarith
    have hinvlog2sq : 1 / ((2 : ℝ) * (Real.log 2) ^ 2) ≤ 2 := by
      rw [div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hlog2pos))]
      nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
    calc
      (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
          1 / ((2 : ℝ) * (Real.log 2) ^ 2) +
            1 / Real.log 2 - 1 / Real.log N :=
        sum_Icc_inv_nat_mul_log_sq_le_boundary hN
      _ ≤ 1 / ((2 : ℝ) * (Real.log 2) ^ 2) + 1 / Real.log 2 := by
        have : 0 ≤ 1 / Real.log N := by positivity
        linarith
      _ ≤ 4 := by linarith
  · have hEmpty : Finset.Icc 2 N = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hnmem
      rcases Finset.mem_Icc.mp hnmem with ⟨hn2, hnN⟩
      omega
    simp [hEmpty]

/-- The logarithmic square weight, extended by zero at `0` and `1`, is
summable. -/
theorem summable_inv_nat_mul_log_sq :
    Summable (fun n : ℕ =>
      if 2 ≤ n then 1 / ((n : ℝ) * (Real.log n) ^ 2) else 0) := by
  apply summable_of_sum_range_le
  · intro n
    split_ifs
    · positivity
    · exact le_rfl
  · intro N
    rw [← Finset.sum_filter]
    calc
      (∑ n ∈ Finset.filter (fun n => 2 ≤ n) (Finset.range N),
          1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
          ∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * (Real.log n) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn
          exact Finset.mem_Icc.mpr ⟨hn.2, hn.1.le⟩
        · intro n hn _
          have hn2 := (Finset.mem_Icc.mp hn).1
          positivity
      _ ≤ 4 := sum_Icc_inv_nat_mul_log_sq_le_four N

end MathlibAux

namespace HardyTheorem

/-- The square norm of all short critical-line Dirichlet coefficients has a
universal finite bound, independent of the interval length and cutoff. -/
theorem sum_normSq_criticalLineShortDirichletCoeff_le_sixteen
    (δ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N,
      Complex.normSq (criticalLineShortDirichletCoeff δ n)) ≤ 16 := by
  calc
    (∑ n ∈ Finset.Icc 2 N,
        Complex.normSq (criticalLineShortDirichletCoeff δ n)) ≤
        ∑ n ∈ Finset.Icc 2 N,
          4 * (1 / ((n : ℝ) * (Real.log n) ^ 2)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hnorm := norm_criticalLineShortDirichletCoeff_le_two_div
        (δ := δ) hn2
      rw [Complex.normSq_eq_norm_sq]
      calc
        ‖criticalLineShortDirichletCoeff δ n‖ ^ 2 ≤
            (2 / (Real.sqrt n * Real.log n)) ^ 2 := by
          exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
        _ = 4 * (1 / ((n : ℝ) * (Real.log n) ^ 2)) := by
          rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
          ring
    _ = 4 * (∑ n ∈ Finset.Icc 2 N,
        1 / ((n : ℝ) * (Real.log n) ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * 4 := mul_le_mul_of_nonneg_left
      (MathlibAux.sum_Icc_inv_nat_mul_log_sq_le_four N) (by norm_num)
    _ = 16 := by norm_num

end HardyTheorem
