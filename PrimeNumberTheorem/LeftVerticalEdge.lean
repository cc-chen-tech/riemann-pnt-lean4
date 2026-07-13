import PrimeNumberTheorem.LeftHorizontalEdge
import PrimeNumberTheorem.ExplicitFormulaRectangle

open Complex Filter Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- On a vertical line through a negative odd integer, the cotangent factor
arising from digamma reflection is uniformly bounded, including at height
zero. -/
theorem norm_cot_odd_vertical_le_one (N : ℕ) (t : ℝ) :
    ‖Complex.cot (Real.pi *
      ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) / 2 +
        Real.pi * (t : ℂ) * I / 2)‖ ≤ 1 := by
  let x : ℝ := -((N : ℝ) * Real.pi + Real.pi / 2)
  let y : ℝ := Real.pi * t / 2
  have harg :
      Real.pi * (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ)) / 2 +
          Real.pi * (t : ℂ) * I / 2 =
        (x : ℂ) + (y : ℂ) * I := by
    dsimp [x, y]
    push_cast
    ring
  have hsin : Real.sin x ^ 2 = 1 := by
    have hzero : Real.sin ((N : ℝ) * Real.pi) = 0 := by
      exact Real.sin_nat_mul_pi N
    have hunit := Real.sin_sq_add_cos_sq ((N : ℝ) * Real.pi)
    dsimp [x]
    rw [Real.sin_neg, Real.sin_add]
    simp only [Real.sin_pi_div_two, Real.cos_pi_div_two, mul_zero, mul_one, neg_sq]
    nlinarith
  have hcos : Real.cos x ^ 2 = 0 := by
    dsimp [x]
    rw [Real.cos_neg]
    simp [Real.cos_add, Real.sin_nat_mul_pi]
  have hsinSq :
      Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) =
        Real.sin x ^ 2 + Real.sinh y ^ 2 := by
    rw [Complex.sin_add_mul_I]
    simp [Complex.normSq_apply, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, sq]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.cosh_sq_sub_sinh_sq y]
  have hcosSq :
      Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) =
        Real.cos x ^ 2 + Real.sinh y ^ 2 := by
    rw [Complex.cos_add_mul_I]
    simp [Complex.normSq_apply, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, sq]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.cosh_sq_sub_sinh_sq y]
  rw [harg, Complex.cot_eq_cos_div_sin, norm_div]
  apply (sq_le_sq₀ (div_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).1
  rw [div_pow, Complex.sq_norm, Complex.sq_norm, hsinSq, hcosSq, hsin, hcos]
  have hy : 0 ≤ Real.sinh y ^ 2 := sq_nonneg _
  have hden : 0 < 1 + Real.sinh y ^ 2 := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- The logarithmic derivative of Deligne's real Gamma factor at every point
where its ordinary Gamma factor is regular. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    logDeriv Complex.Gammaℝ s =
      -Complex.log Real.pi / 2 + Complex.digamma (s / 2) / 2 := by
  let A : ℂ → ℂ := fun z => (Real.pi : ℂ) ^ (-z / 2)
  let G : ℂ → ℂ := fun z => Complex.Gamma (z / 2)
  have hbase : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA : A s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hG : G s ≠ 0 := Complex.Gamma_ne_zero hsGamma
  have hAdiff : DifferentiableAt ℂ A s := by
    dsimp [A]
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hbase)
  have hGdiff : DifferentiableAt ℂ G s := by
    exact (Complex.differentiableAt_Gamma (s / 2) hsGamma).comp s (by fun_prop)
  have hAlog : logDeriv A s = -Complex.log Real.pi / 2 := by
    simp only [A, logDeriv_apply]
    rw [Complex.deriv_const_cpow (by fun_prop :
      DifferentiableAt ℂ (fun z : ℂ => -z / 2) s)]
    rw [show deriv (fun z : ℂ => -z / 2) s = -(1 : ℂ) / 2 by
      exact ((hasDerivAt_neg s).div_const 2).deriv]
    field_simp
  have hGlog : logDeriv G s = Complex.digamma (s / 2) / 2 := by
    have hcomp := logDeriv_comp
      (f := Complex.Gamma) (g := fun z : ℂ => z / 2) (x := s)
      (Complex.differentiableAt_Gamma (s / 2) hsGamma) (by fun_prop)
    calc
      logDeriv G s = logDeriv Complex.Gamma (s / 2) *
          deriv (fun z : ℂ => z / 2) s := by simpa [G] using hcomp
      _ = Complex.digamma (s / 2) * ((1 : ℂ) / 2) := by
        rw [← Complex.digamma_def]
        congr 1
        exact (hasDerivAt_id s).div_const 2 |>.deriv
      _ = Complex.digamma (s / 2) / 2 := by ring
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) *
    Complex.Gamma (z / 2)) s = _
  change logDeriv (fun z : ℂ => A z * G z) s = _
  rw [logDeriv_mul s hA hG hAdiff hGdiff, hAlog, hGlog]

/-- Good contour heights can be chosen with linear growth.  The upper bound is
needed because exponential decay in the moving left edge must dominate the
length of the vertical segment. -/
theorem exists_linearlyControlled_goodHeight_gt_one :
    ∃ (K : ℕ) (T : ℕ → ℝ), StrictMono T ∧ Tendsto T atTop atTop ∧
      ∀ n, ((n + K : ℕ) : ℝ) < T n ∧
        T n < ((n + K : ℕ) : ℝ) + 1 ∧
        1 < T n ∧ ExplicitFormulaAux.goodHeight (T n) := by
  classical
  let T : ℕ → ℝ := fun n => Classical.choose
    (ExplicitFormulaAux.exists_goodHeight_Ioo ((n + 2 : ℕ) : ℝ))
  have hT (n : ℕ) :
      ((n + 2 : ℕ) : ℝ) < T n ∧
        T n < ((n + 2 : ℕ) : ℝ) + 1 ∧
        ExplicitFormulaAux.goodHeight (T n) := by
    exact Classical.choose_spec
      (ExplicitFormulaAux.exists_goodHeight_Ioo ((n + 2 : ℕ) : ℝ))
  have hmono : StrictMono T := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hn := (hT n).2.1
    have hnext := (hT (n + 1)).1
    norm_num [Nat.cast_add, Nat.cast_one] at hn hnext
    linarith
  have htend : Tendsto T atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (Nat.ceil b)] with n hn
    have hbceil : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
    have hceiln : (Nat.ceil b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnshift : (n : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ n + 2 by omega)
    exact le_trans hbceil (le_trans hceiln (hnshift.trans (hT n).1.le))
  refine ⟨2, T, hmono, htend, ?_⟩
  intro n
  have htwo : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ n + 2 by omega)
  exact ⟨(hT n).1, (hT n).2.1,
    lt_trans (lt_of_lt_of_le one_lt_two htwo) (hT n).1, (hT n).2.2⟩

end ExplicitFormulaResidues
end PrimeNumberTheorem
