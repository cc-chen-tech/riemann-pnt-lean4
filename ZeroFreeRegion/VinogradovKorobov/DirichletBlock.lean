import ZeroFreeRegion.VinogradovKorobov.WeightedSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The real amplitude `n⁻ˢ` in the Dirichlet monomial
`n⁻⁽ˢ⁺ⁱᵗ⁾`. -/
noncomputable def dirichletWeight (sigma : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-sigma)

lemma dirichletWeight_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ dirichletWeight sigma n := by
  exact Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- For nonnegative real part, Dirichlet amplitudes decrease along every
positive integer block. -/
lemma dirichletWeight_antitone
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    dirichletWeight sigma (m + (k + 1)) ≤
      dirichletWeight sigma (m + k) := by
  apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hsigma)
  · exact Set.mem_Ioi.mpr (by positivity)
  · exact Set.mem_Ioi.mpr (by positivity)
  · exact_mod_cast (show m + k ≤ m + (k + 1) by omega)

/-- Dirichlet weights with nonnegative real part are antitone on all positive
integer arguments. -/
lemma dirichletWeight_le_of_le
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) :
    dirichletWeight sigma n ≤ dirichletWeight sigma m := by
  apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hsigma)
  · exact Set.mem_Ioi.mpr (by exact_mod_cast hm)
  · exact Set.mem_Ioi.mpr (by exact_mod_cast hm.trans_le hmn)
  · exact_mod_cast hmn

/-- Split a Dirichlet monomial into its decreasing real amplitude and unit
logarithmic oscillation. -/
lemma inv_nat_cpow_eq_dirichletWeight_mul_zetaOscillation
    {n : ℕ} (hn : n ≠ 0) (sigma t : ℝ) :
    1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t) =
      (dirichletWeight sigma n : ℂ) * zetaOscillation t n := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hweight :
      (dirichletWeight sigma n : ℂ) = ((n : ℂ) ^ (sigma : ℂ))⁻¹ := by
    rw [dirichletWeight, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    rw [show ((-sigma : ℝ) : ℂ) = -(sigma : ℂ) by norm_num]
    rw [Complex.cpow_neg]
    norm_num
  have himag :
      ((n : ℂ) ^ (Complex.I * t))⁻¹ = zetaOscillation t n := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg,
      ← Complex.natCast_log]
    unfold zetaOscillation phaseTerm
    congr 1
    push_cast
    ring
  rw [Complex.cpow_add _ _ hnC, one_div, mul_inv_rev, himag, hweight]
  exact mul_comm _ _

/-- Abel transfer from uniform unweighted logarithmic prefix bounds to a
finite Dirichlet block. -/
theorem norm_dirichletBlock_le_weight_mul
    (sigma t : ℝ) (m N : ℕ) (B : ℝ)
    (hsigma : 0 ≤ sigma) (hm : 0 < m)
    (hpartial : ∀ k ≤ N,
      ‖∑ j ∈ Finset.range (k + 1), zetaOscillation t (m + j)‖ ≤ B) :
    ‖∑ k ∈ Finset.range (N + 1),
        1 / ((m + k : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ≤
      dirichletWeight sigma m * B := by
  have hrewrite : ∀ k ≤ N,
      1 / ((m + k : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t) =
        (dirichletWeight sigma (m + k) : ℂ) *
          zetaOscillation t (m + k) := by
    intro k hk
    apply inv_nat_cpow_eq_dirichletWeight_mul_zetaOscillation
    omega
  calc
    ‖∑ k ∈ Finset.range (N + 1),
        1 / ((m + k : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ =
        ‖∑ k ∈ Finset.range (N + 1),
          (dirichletWeight sigma (m + k) : ℂ) *
            zetaOscillation t (m + k)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact hrewrite k (by simpa using Finset.mem_range.mp hk)
    _ ≤ dirichletWeight sigma (m + 0) * B := by
      apply norm_weighted_sum_le_first_mul
      · intro k hk
        exact dirichletWeight_nonneg sigma (m + k)
      · intro k hk
        exact dirichletWeight_antitone hsigma hm k
      · exact hpartial
    _ = dirichletWeight sigma m * B := by simp

end ZeroFreeRegion.VinogradovKorobov
