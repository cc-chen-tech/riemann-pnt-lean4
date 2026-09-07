import MathlibAux.GaussianExponentialPolynomialMeanSquare
import MathlibAux.GaussianBucketSchur

/-!
# A short Dirichlet polynomial under a Gaussian window

When all indices are at most `N` and the Gaussian width is at least `2 * N`,
distinct logarithmic frequencies occupy separated unit buckets after scaling
by `Delta / 2`.  The collision-safe Gaussian Schur estimate then reduces the
exact Gaussian Gram form to the coefficient square sum.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace MathlibAux

private theorem natDist_le_scaled_abs_log_sub
    {m n N : ℕ} {Delta : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hmN : m ≤ N) (hnN : n ≤ N)
    (hDelta : 2 * (N : ℝ) ≤ Delta) :
    (Nat.dist m n : ℝ) ≤
      |Delta / 2 * (-Real.log m) - Delta / 2 * (-Real.log n)| := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < (N : ℝ) := hmR.trans_le (by exact_mod_cast hmN)
  have hhalf : (N : ℝ) ≤ Delta / 2 := by linarith
  have hhalf0 : 0 ≤ Delta / 2 := hNpos.le.trans hhalf
  rcases le_total m n with hmn | hnm
  · have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hratio0 : 0 ≤ ((n : ℝ) - m) / n := div_nonneg (sub_nonneg.mpr hmnR) hnR.le
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hnR hmR)
    rw [inv_div, Real.log_div hnR.ne' hmR.ne'] at hlog
    have hratioLog : ((n : ℝ) - m) / n ≤ Real.log n - Real.log m := by
      have hrewrite : 1 - (m : ℝ) / n = ((n : ℝ) - m) / n := by
        field_simp
      simpa only [hrewrite] using hlog
    have hdistCast : (Nat.dist m n : ℝ) = (n : ℝ) - m := by
      rw [Nat.dist_eq_sub_of_le hmn, Nat.cast_sub hmn]
    have hfactor :
        (n : ℝ) * (((n : ℝ) - m) / n) = (n : ℝ) - m := by
      field_simp
    have hdistN :
        (n : ℝ) - m ≤ (N : ℝ) * (((n : ℝ) - m) / n) := by
      calc
        (n : ℝ) - m = (n : ℝ) * (((n : ℝ) - m) / n) := hfactor.symm
        _ ≤ (N : ℝ) * (((n : ℝ) - m) / n) :=
          mul_le_mul_of_nonneg_right hnNR hratio0
    have hNhalf :
        (N : ℝ) * (((n : ℝ) - m) / n) ≤
          (Delta / 2) * (((n : ℝ) - m) / n) :=
      mul_le_mul_of_nonneg_right hhalf hratio0
    have hscaled :
        (Delta / 2) * (((n : ℝ) - m) / n) ≤
          (Delta / 2) * (Real.log n - Real.log m) :=
      mul_le_mul_of_nonneg_left hratioLog hhalf0
    rw [hdistCast]
    calc
      (n : ℝ) - m ≤ (N : ℝ) * (((n : ℝ) - m) / n) := hdistN
      _ ≤ (Delta / 2) * (((n : ℝ) - m) / n) := hNhalf
      _ ≤ (Delta / 2) * (Real.log n - Real.log m) := hscaled
      _ = |Delta / 2 * (-Real.log m) -
          Delta / 2 * (-Real.log n)| := by
        rw [abs_of_nonneg]
        · ring
        · have hnonneg := mul_nonneg hhalf0
            (sub_nonneg.mpr (Real.log_le_log hmR hmnR))
          nlinarith
  · have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have hratio0 : 0 ≤ ((m : ℝ) - n) / m := div_nonneg (sub_nonneg.mpr hnmR) hmR.le
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hmR hnR)
    rw [inv_div, Real.log_div hmR.ne' hnR.ne'] at hlog
    have hratioLog : ((m : ℝ) - n) / m ≤ Real.log m - Real.log n := by
      have hrewrite : 1 - (n : ℝ) / m = ((m : ℝ) - n) / m := by
        field_simp
      simpa only [hrewrite] using hlog
    have hdistCast : (Nat.dist m n : ℝ) = (m : ℝ) - n := by
      rw [Nat.dist_eq_sub_of_le_right hnm, Nat.cast_sub hnm]
    have hfactor :
        (m : ℝ) * (((m : ℝ) - n) / m) = (m : ℝ) - n := by
      field_simp
    have hdistN :
        (m : ℝ) - n ≤ (N : ℝ) * (((m : ℝ) - n) / m) := by
      calc
        (m : ℝ) - n = (m : ℝ) * (((m : ℝ) - n) / m) := hfactor.symm
        _ ≤ (N : ℝ) * (((m : ℝ) - n) / m) :=
          mul_le_mul_of_nonneg_right hmNR hratio0
    have hNhalf :
        (N : ℝ) * (((m : ℝ) - n) / m) ≤
          (Delta / 2) * (((m : ℝ) - n) / m) :=
      mul_le_mul_of_nonneg_right hhalf hratio0
    have hscaled :
        (Delta / 2) * (((m : ℝ) - n) / m) ≤
          (Delta / 2) * (Real.log m - Real.log n) :=
      mul_le_mul_of_nonneg_left hratioLog hhalf0
    rw [hdistCast]
    calc
      (m : ℝ) - n ≤ (N : ℝ) * (((m : ℝ) - n) / m) := hdistN
      _ ≤ (Delta / 2) * (((m : ℝ) - n) / m) := hNhalf
      _ ≤ (Delta / 2) * (Real.log m - Real.log n) := hscaled
      _ = |Delta / 2 * (-Real.log m) -
          Delta / 2 * (-Real.log n)| := by
        rw [abs_of_nonpos]
        · ring
        · have hlognonneg : 0 ≤ Real.log m - Real.log n :=
            sub_nonneg.mpr (Real.log_le_log hnR hnmR)
          nlinarith

/-- Gaussian logarithmic-frequency Gram forms of length at most `N` satisfy
an absolute Schur bound once `Delta ≥ 2N`. -/
theorem gaussian_log_frequency_kernel_le
    {N : ℕ} {Delta : ℝ}
    (hDelta : 2 * (N : ℝ) ≤ Delta)
    (S : Finset ℕ) (hpos : ∀ n ∈ S, 0 < n)
    (hupper : ∀ n ∈ S, n ≤ N)
    (mass : ℕ → ℝ) (hmass : ∀ n ∈ S, 0 ≤ mass n) :
    (∑ m ∈ S, ∑ n ∈ S,
        mass m * mass n *
          Real.exp (-(Delta ^ 2 *
            ((-Real.log m) - (-Real.log n)) ^ 2) / 4)) ≤
      gaussianBucketSchurConstant * ∑ n ∈ S, mass n ^ 2 := by
  have hschur := sum_gaussianKernel_le_bucketEnergy
    S mass (fun n : ℕ => Delta / 2 * (-Real.log n)) id
    (m := 1) (by norm_num) hmass (fun i hi j hj => by
      have hdist := natDist_le_scaled_abs_log_sub
        (hpos i hi) (hpos j hj) (hupper i hi) (hupper j hj) hDelta
      have hsub : (((Nat.dist i j - 1 : ℕ) : ℝ) : ℝ) ≤
          (Nat.dist i j : ℝ) := by
        exact_mod_cast Nat.sub_le (Nat.dist i j) 1
      exact hsub.trans hdist)
  calc
    (∑ m ∈ S, ∑ n ∈ S,
        mass m * mass n *
          Real.exp (-(Delta ^ 2 *
            ((-Real.log m) - (-Real.log n)) ^ 2) / 4)) =
        ∑ m ∈ S, ∑ n ∈ S,
          mass m * mass n *
            Real.exp (-1 *
              (Delta / 2 * (-Real.log m) -
                Delta / 2 * (-Real.log n)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      congr 2
      ring
    _ ≤ gaussianBucketSchurConstant *
        ∑ n ∈ S.image id,
          (∑ i ∈ S.filter (fun i => id i = n), mass i) ^ 2 := hschur
    _ = gaussianBucketSchurConstant * ∑ n ∈ S, mass n ^ 2 := by
      congr 1
      change (∑ n ∈ S.image (fun x => x),
        (∑ i ∈ S.filter (fun i => i = n), mass i) ^ 2) =
          ∑ n ∈ S, mass n ^ 2
      rw [Finset.image_id']
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_eq_single n
      · intro i hi hin
        exact False.elim (hin (Finset.mem_filter.mp hi).2)
      · intro hnfilter
        exact False.elim (hnfilter (Finset.mem_filter.mpr ⟨hn, rfl⟩))

/-- A Dirichlet polynomial shorter than half the Gaussian width has local
Gaussian second moment bounded by an absolute constant times its coefficient
energy. -/
theorem integral_gaussian_mul_normSq_dirichletPolynomial_le
    {N : ℕ} (hN : 0 < N) {Delta : ℝ}
    (hDelta : 2 * (N : ℝ) ≤ Delta) (w : ℝ)
    (S : Finset ℕ) (hpos : ∀ n ∈ S, 0 < n)
    (hupper : ∀ n ∈ S, n ≤ N) (coeff : ℕ → ℂ) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (exponentialPolynomial S coeff (fun n => -Real.log n) t)) ≤
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        gaussianBucketSchurConstant * ∑ n ∈ S, ‖coeff n‖ ^ 2 := by
  have hDeltaPos : 0 < Delta := by
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    linarith
  have hmean := integral_gaussian_mul_normSq_exponentialPolynomial_le
    hDeltaPos w S coeff (fun n => -Real.log n)
  have hkernel := gaussian_log_frequency_kernel_le hDelta S hpos hupper
    (fun n => ‖coeff n‖) (fun _ _ => norm_nonneg _)
  calc
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (exponentialPolynomial S coeff (fun n => -Real.log n) t)) ≤
        Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
          ∑ m ∈ S, ∑ n ∈ S,
            ‖coeff m‖ * ‖coeff n‖ *
              Real.exp (-(Delta ^ 2 *
                ((-Real.log m) - (-Real.log n)) ^ 2) / 4) := hmean
    _ ≤ Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        (gaussianBucketSchurConstant * ∑ n ∈ S, ‖coeff n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hkernel (Real.sqrt_nonneg _)
    _ = _ := by ring

end MathlibAux
