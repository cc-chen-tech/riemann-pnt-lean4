import HardyTheorem.SelbergFirstMomentRightEdgeFinite
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex MeasureTheory
open scoped BigOperators Topology
open Filter

namespace HardyTheorem

/-!
# The genuine right edge in Selberg's first-moment rectangle

On `re(s) = 2`, the zeta Dirichlet series converges uniformly in the height
variable.  Multiplication by the fixed finite mollifier therefore carries the
finite right-edge estimate to the actual auxiliary function
`ζ(s) ψ_X(s)^2`.
-/

/-- The analytic auxiliary product used for the first-moment contour.  This is
not the reflected product used in the second moment; on the critical line only
its modulus is needed. -/
noncomputable def selbergFirstMomentAuxiliary (X : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta s * selbergSqrtZetaMollifier X s) *
    selbergSqrtZetaMollifier X s

private noncomputable def selbergRightZetaPartial
    (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N,
    1 / ((k + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + I * t)

private theorem selbergRightZetaPartial_eq_Icc (N : ℕ) (t : ℝ) :
    selbergRightZetaPartial N t =
      ∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((2 : ℂ) + I * t) := by
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp [selbergRightZetaPartial, add_comm]

private theorem tendstoUniformlyOn_selbergRightZetaPartial
    {a b : ℝ} :
    TendstoUniformlyOn selbergRightZetaPartial
      (fun t : ℝ => riemannZeta ((2 : ℂ) + I * t)) atTop
        (Set.uIcc a b) := by
  let u : ℕ → ℝ := fun k => (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hu : Summable u := by
    exact (summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by omega : 1 < (2 : ℕ)))
  have hterm (k : ℕ) (t : ℝ) :
      ‖1 / ((k + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + I * t)‖ ≤ u k := by
    have hk : 0 < k + 1 := Nat.succ_pos k
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hk]
    rw [show (((2 : ℂ) + I * t).re) = 2 by norm_num, Real.rpow_two]
    simp only [u, one_div]
    exact le_rfl
  have hbase := tendstoUniformlyOn_tsum_nat hu
    (s := Set.uIcc a b) (fun k t _ht => hterm k t)
  convert hbase using 1
  · rfl
  · funext t
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow
      (show 1 < (((2 : ℂ) + I * t).re) by norm_num)]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem norm_selbergRightZetaPartial_le_two (N : ℕ) (t : ℝ) :
    ‖selbergRightZetaPartial N t‖ ≤ 2 := by
  rw [selbergRightZetaPartial_eq_Icc]
  calc
    ‖∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((2 : ℂ) + I * t)‖ ≤
        ∑ m ∈ Finset.Icc 1 N,
          ‖1 / (m : ℂ) ^ ((2 : ℂ) + I * t)‖ :=
      norm_sum_le _ _
    _ = ∑ m ∈ Finset.Icc 1 N, (((m : ℝ) ^ 2))⁻¹ := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmpos : 0 < m := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hm).1
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hmpos]
      rw [show (((2 : ℂ) + I * t).re) = 2 by norm_num, Real.rpow_two]
      simp only [one_div]
    _ ≤ 2 := MathlibAux.sum_inv_sq_Icc_one_le_two N

private theorem norm_selbergSqrtZetaMollifier_rightLine_le_two
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    ‖selbergSqrtZetaMollifier X ((2 : ℂ) + I * t)‖ ≤ 2 := by
  unfold selbergSqrtZetaMollifier selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ ((2 : ℂ) + I * t))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergSqrtZetaTaperedCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ ((2 : ℂ) + I * t))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (((n : ℝ) ^ 2))⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hnpos : 0 < n := Nat.zero_lt_of_lt hn1
      have hcoeff : ‖(selbergSqrtZetaTaperedCoeff X n : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          abs_selbergSqrtZetaTaperedCoeff_le_one hX hn1 hnX
      rw [norm_mul, norm_div, norm_one,
        Complex.norm_natCast_cpow_of_pos hnpos]
      rw [show (((2 : ℂ) + I * t).re) = 2 by norm_num, Real.rpow_two]
      simp only [one_div]
      exact mul_le_of_le_one_left (by positivity) hcoeff
    _ ≤ 2 := MathlibAux.sum_inv_sq_Icc_one_le_two X

/-- The right-edge auxiliary integral differs from its constant coefficient by
at most an absolute constant, uniformly in the interval and mollifier length. -/
theorem norm_intervalIntegral_selbergFirstMomentAuxiliary_rightLine_sub_one_le
    {X : ℕ} (hX : 2 ≤ X) {a b : ℝ} :
    ‖∫ t in a..b,
        (selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t) - 1)‖ ≤
      16 / Real.log 2 := by
  let F : ℕ → ℝ → ℂ := fun N t =>
    (selbergRightZetaPartial N t *
        selbergSqrtZetaMollifier X ((2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((2 : ℂ) + I * t) - 1
  let f : ℝ → ℂ := fun t =>
    selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t) - 1
  have hMcont : Continuous (fun t : ℝ =>
      selbergSqrtZetaMollifier X ((2 : ℂ) + I * t)) := by
    unfold selbergSqrtZetaMollifier selbergMollifier
    apply continuous_finsetSum
    intro n hn
    have hn0 : n ≠ 0 :=
      Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    have hexponent : Continuous (fun t : ℝ => (2 : ℂ) + I * t) := by
      fun_prop
    have hpow : Continuous (fun t : ℝ =>
        (n : ℂ) ^ ((2 : ℂ) + I * t)) :=
      hexponent.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn0))
    exact continuous_const.mul
      (continuous_const.div hpow (fun _ =>
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn0)))))
  have hcont : ∀ᶠ N : ℕ in atTop,
      ContinuousOn (F N) (Set.uIcc a b) := by
    filter_upwards with N
    apply Continuous.continuousOn
    dsimp [F]
    apply Continuous.sub
    · apply Continuous.mul
      · apply Continuous.mul
        · apply continuous_finsetSum
          intro k _hk
          have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
          have hexponent : Continuous (fun t : ℝ => (2 : ℂ) + I * t) := by
            fun_prop
          have hpow : Continuous (fun t : ℝ =>
              ((k + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + I * t)) :=
            hexponent.const_cpow (Or.inl hk0)
          exact continuous_const.div hpow (fun _ =>
            Complex.cpow_ne_zero_iff.mpr (Or.inl hk0))
        · exact hMcont
      · exact hMcont
    · exact continuous_const
  have hbound (N : ℕ) (t : ℝ) : ‖F N t‖ ≤ 9 := by
    have hZ := norm_selbergRightZetaPartial_le_two N t
    have hM := norm_selbergSqrtZetaMollifier_rightLine_le_two hX t
    dsimp [F]
    calc
      ‖selbergRightZetaPartial N t *
            selbergSqrtZetaMollifier X ((2 : ℂ) + I * t) *
            selbergSqrtZetaMollifier X ((2 : ℂ) + I * t) - 1‖ ≤
          ‖selbergRightZetaPartial N t *
            selbergSqrtZetaMollifier X ((2 : ℂ) + I * t) *
            selbergSqrtZetaMollifier X ((2 : ℂ) + I * t)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ (2 * 2) * 2 + 1 := by
        rw [norm_mul, norm_mul, norm_one]
        gcongr
      _ = 9 := by norm_num
  have hpoint (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      Tendsto (fun N => F N t) atTop (nhds (f t)) := by
    have hZ :=
      (tendstoUniformlyOn_selbergRightZetaPartial (a := a) (b := b)).tendsto_at ht
    dsimp [F, f, selbergFirstMomentAuxiliary]
    exact (((hZ.mul_const
      (selbergSqrtZetaMollifier X ((2 : ℂ) + I * t))).mul_const
        (selbergSqrtZetaMollifier X ((2 : ℂ) + I * t))).sub
          tendsto_const_nhds)
  have hint : Tendsto (fun N => ∫ t in a..b, F N t) atTop
      (nhds (∫ t in a..b, f t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => 9)
    · exact hcont.mono fun _N hN =>
        (hN.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
    · exact Filter.Eventually.of_forall fun N =>
        Filter.Eventually.of_forall fun t _ht => hbound N t
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t ht =>
        hpoint t (Set.uIoc_subset_uIcc ht)
  apply le_of_tendsto hint.norm
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hfinite :=
    norm_intervalIntegral_selbergFirstMomentRightTriplePolynomial_sub_one_le
      hN hX (a := a) (b := b)
  rw [show (fun t => F N t) = fun t =>
      selbergFirstMomentRightTriplePolynomial N X t - 1 by
    funext t
    dsimp [F]
    rw [selbergRightZetaPartial_eq_Icc,
      finiteZeta_mul_sqrtZetaMollifier_sq_rightLine_eq]]
  exact hfinite

end HardyTheorem
