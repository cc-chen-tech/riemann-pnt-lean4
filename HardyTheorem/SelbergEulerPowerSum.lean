import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Set Finset
open scoped BigOperators

namespace HardyTheorem

/-!
# Uniform Euler summation for Selberg's diagonal Gaussian

For `0 < theta <= 1/2`, subtract from `n^(theta-1)` the normalized
increment of `x^theta`.  Concavity makes the correction nonnegative and
dominates it by a telescoping difference.  Its infinite sum therefore gives
the bounded constant in Euler summation, while its tail is
`O(N^(theta-1))` with constant one.
-/

noncomputable def selbergEulerPowerCorrection (theta : ℝ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) ^ (theta - 1)) -
    ((((n + 2 : ℕ) : ℝ) ^ theta -
        ((n + 1 : ℕ) : ℝ) ^ theta) / theta)

noncomputable def selbergEulerPowerConstant (theta : ℝ) : ℝ :=
  theta * (∑' n : ℕ, selbergEulerPowerCorrection theta n) - 1

private theorem selbergEulerPowerCorrection_bounds
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (n : ℕ) :
    0 ≤ selbergEulerPowerCorrection theta n ∧
      selbergEulerPowerCorrection theta n ≤
        (((n + 1 : ℕ) : ℝ) ^ (theta - 1) -
          ((n + 2 : ℕ) : ℝ) ^ (theta - 1)) := by
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  let b : ℝ := ((n + 2 : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x => x ^ theta
  have ha0 : 0 < a := by
    dsimp [a]
    positivity
  have hb0 : 0 < b := by
    dsimp [b]
    positivity
  have hab : a < b := by
    dsimp [a, b]
    norm_num
  have hdiff : DifferentiableOn ℝ f (Set.Icc a b) := by
    intro x hx
    exact (Real.differentiableAt_rpow_const_of_ne theta
      (ne_of_gt (ha0.trans_le hx.1))).differentiableWithinAt
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope f hab hdiff.continuousOn
      (hdiff.mono Set.Ioo_subset_Icc_self)
  have hc0 : 0 < c := ha0.trans hc.1
  have hba : b - a = 1 := by
    dsimp [a, b]
    norm_num
  have hderiv : deriv f c = theta * c ^ (theta - 1) := by
    exact Real.deriv_rpow_const c theta
  rw [hderiv, hba, div_one] at hcderiv
  have hquot : (b ^ theta - a ^ theta) / theta =
      c ^ (theta - 1) := by
    rw [← hcderiv]
    field_simp [htheta0.ne']
  have hexp : theta - 1 ≤ 0 := by linarith
  have hca : c ^ (theta - 1) ≤ a ^ (theta - 1) :=
    Real.rpow_le_rpow_of_nonpos ha0 hc.1.le hexp
  have hbc : b ^ (theta - 1) ≤ c ^ (theta - 1) :=
    Real.rpow_le_rpow_of_nonpos hc0 hc.2.le hexp
  change 0 ≤ a ^ (theta - 1) -
      (b ^ theta - a ^ theta) / theta ∧
    a ^ (theta - 1) - (b ^ theta - a ^ theta) / theta ≤
      a ^ (theta - 1) - b ^ (theta - 1)
  rw [hquot]
  constructor <;> linarith

theorem selbergEulerPowerCorrection_nonneg
    {theta : ℝ} (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (n : ℕ) :
    0 ≤ selbergEulerPowerCorrection theta n :=
  (selbergEulerPowerCorrection_bounds htheta0 (by linarith) n).1

private theorem sum_range_selbergEulerPowerMajorant_le
    {theta : ℝ} (_hthetaHalf : theta ≤ 1 / 2) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (((n + 1 : ℕ) : ℝ) ^ (theta - 1) -
        ((n + 2 : ℕ) : ℝ) ^ (theta - 1))) ≤ 1 := by
  rw [Finset.sum_range_sub']
  have hnonneg : 0 ≤ (((N + 1 : ℕ) : ℝ) ^ (theta - 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hone : (((0 + 1 : ℕ) : ℝ) ^ (theta - 1)) = 1 := by
    norm_num
  rw [hone]
  linarith

theorem summable_selbergEulerPowerCorrection
    {theta : ℝ} (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    Summable (selbergEulerPowerCorrection theta) := by
  let M : ℕ → ℝ := fun n =>
    (((n + 1 : ℕ) : ℝ) ^ (theta - 1) -
      ((n + 2 : ℕ) : ℝ) ^ (theta - 1))
  have hM0 (n : ℕ) : 0 ≤ M n := by
    have hn0 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hnle : ((n + 1 : ℕ) : ℝ) ≤ (n + 2 : ℕ) := by
      exact_mod_cast Nat.le_succ (n + 1)
    exact sub_nonneg.mpr
      (Real.rpow_le_rpow_of_nonpos hn0 hnle (by linarith))
  have hMsum : Summable M := by
    apply summable_of_sum_range_le hM0
    intro N
    simpa only [M] using
      sum_range_selbergEulerPowerMajorant_le hthetaHalf N
  exact Summable.of_nonneg_of_le
    (selbergEulerPowerCorrection_nonneg htheta0 hthetaHalf)
    (fun n =>
      (selbergEulerPowerCorrection_bounds htheta0 (by linarith) n).2)
    hMsum

private theorem tsum_selbergEulerPowerCorrection_mem_Icc
    {theta : ℝ} (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    (∑' n : ℕ, selbergEulerPowerCorrection theta n) ∈
      Set.Icc (0 : ℝ) 1 := by
  have hnonneg := selbergEulerPowerCorrection_nonneg htheta0 hthetaHalf
  constructor
  · exact tsum_nonneg hnonneg
  · apply Real.tsum_le_of_sum_range_le hnonneg
    intro N
    calc
      (∑ n ∈ Finset.range N, selbergEulerPowerCorrection theta n) ≤
          ∑ n ∈ Finset.range N,
            (((n + 1 : ℕ) : ℝ) ^ (theta - 1) -
              ((n + 2 : ℕ) : ℝ) ^ (theta - 1)) := by
        exact Finset.sum_le_sum fun n _ =>
          (selbergEulerPowerCorrection_bounds htheta0 (by linarith) n).2
      _ ≤ 1 := sum_range_selbergEulerPowerMajorant_le hthetaHalf N

theorem abs_selbergEulerPowerConstant_le_one
    {theta : ℝ} (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    |selbergEulerPowerConstant theta| ≤ 1 := by
  have hD := tsum_selbergEulerPowerCorrection_mem_Icc htheta0 hthetaHalf
  have hprod : theta *
      (∑' n : ℕ, selbergEulerPowerCorrection theta n) ≤ 1 / 2 := by
    calc
      theta * (∑' n : ℕ, selbergEulerPowerCorrection theta n) ≤
          (1 / 2 : ℝ) * 1 :=
        mul_le_mul hthetaHalf hD.2 hD.1 (by norm_num)
      _ = 1 / 2 := by ring
  have hnonpos : selbergEulerPowerConstant theta ≤ 0 := by
    unfold selbergEulerPowerConstant
    linarith
  rw [abs_of_nonpos hnonpos]
  unfold selbergEulerPowerConstant
  have hprod0 : 0 ≤ theta *
      (∑' n : ℕ, selbergEulerPowerCorrection theta n) :=
    mul_nonneg htheta0.le hD.1
  linarith

private theorem tsum_nat_add_selbergEulerPowerCorrection_le
    {theta : ℝ} (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (N : ℕ) :
    (∑' k : ℕ, selbergEulerPowerCorrection theta (k + N)) ≤
      (((N + 1 : ℕ) : ℝ) ^ (theta - 1)) := by
  have hnonneg (k : ℕ) :
      0 ≤ selbergEulerPowerCorrection theta (k + N) :=
    selbergEulerPowerCorrection_nonneg htheta0 hthetaHalf _
  apply Real.tsum_le_of_sum_range_le hnonneg
  intro M
  calc
    (∑ k ∈ Finset.range M,
        selbergEulerPowerCorrection theta (k + N)) ≤
        ∑ k ∈ Finset.range M,
          ((((k + N) + 1 : ℕ) : ℝ) ^ (theta - 1) -
            (((k + N) + 2 : ℕ) : ℝ) ^ (theta - 1)) := by
      exact Finset.sum_le_sum fun k _ =>
        (selbergEulerPowerCorrection_bounds htheta0 (by linarith) _).2
    _ = (((N + 1 : ℕ) : ℝ) ^ (theta - 1)) -
        (((M + N) + 1 : ℕ) : ℝ) ^ (theta - 1) := by
      let f : ℕ → ℝ := fun k =>
        (((k + N + 1 : ℕ) : ℝ) ^ (theta - 1))
      calc
        (∑ k ∈ Finset.range M,
            ((((k + N) + 1 : ℕ) : ℝ) ^ (theta - 1) -
              (((k + N) + 2 : ℕ) : ℝ) ^ (theta - 1))) =
            ∑ k ∈ Finset.range M, (f k - f (k + 1)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          dsimp [f]
          have hleft : (k + N) + 1 = k + N + 1 := by omega
          have hright : (k + N) + 2 = (k + 1) + N + 1 := by omega
          rw [hleft, hright]
        _ = f 0 - f M := by rw [Finset.sum_range_sub']
        _ = _ := by
          dsimp [f]
          have hzero : 0 + N + 1 = N + 1 := by omega
          have hend : M + N + 1 = (M + N) + 1 := by omega
          rw [hzero, hend]
    _ ≤ (((N + 1 : ℕ) : ℝ) ^ (theta - 1)) := by
      exact sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem sum_range_power_eq_increment_add_correction
    {theta : ℝ} (_htheta0 : 0 < theta) (N : ℕ) :
    (∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ) ^ (theta - 1))) =
      ((((N + 1 : ℕ) : ℝ) ^ theta - 1) / theta) +
        ∑ n ∈ Finset.range N, selbergEulerPowerCorrection theta n := by
  calc
    (∑ n ∈ Finset.range N,
        (((n + 1 : ℕ) : ℝ) ^ (theta - 1))) =
        ∑ n ∈ Finset.range N,
          (selbergEulerPowerCorrection theta n +
            ((((n + 2 : ℕ) : ℝ) ^ theta -
              ((n + 1 : ℕ) : ℝ) ^ theta) / theta)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      unfold selbergEulerPowerCorrection
      ring
    _ = (∑ n ∈ Finset.range N,
          selbergEulerPowerCorrection theta n) +
        ∑ n ∈ Finset.range N,
          ((((n + 2 : ℕ) : ℝ) ^ theta -
            ((n + 1 : ℕ) : ℝ) ^ theta) / theta) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ n ∈ Finset.range N,
          selbergEulerPowerCorrection theta n) +
        ((((N + 1 : ℕ) : ℝ) ^ theta - 1) / theta) := by
      rw [← Finset.sum_div]
      have htel :
          (∑ n ∈ Finset.range N,
              (((n + 2 : ℕ) : ℝ) ^ theta -
                ((n + 1 : ℕ) : ℝ) ^ theta)) =
            ((N + 1 : ℕ) : ℝ) ^ theta - 1 := by
        induction N with
        | zero => simp
        | succ N ih =>
            rw [Finset.sum_range_succ, ih]
            simp only [Nat.cast_add, Nat.cast_one]
            ring_nf
      rw [htel]
    _ = _ := by ring

/-- Exact uniform Euler decomposition.  The constant is independent of `N`,
and the nonnegative remainder has the sharp telescoping majorant needed in
the diagonal Gaussian calculation. -/
theorem exists_selbergEulerPowerSum_remainder
    {theta : ℝ} (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (N : ℕ) :
    ∃ R : ℝ,
      0 ≤ R ∧ R ≤ ((N + 1 : ℕ) : ℝ) ^ (theta - 1) ∧
      (∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ) ^ (theta - 1))) =
        (((N + 1 : ℕ) : ℝ) ^ theta +
            selbergEulerPowerConstant theta) / theta - R := by
  let R : ℝ := ∑' k : ℕ, selbergEulerPowerCorrection theta (k + N)
  have hsummable := summable_selbergEulerPowerCorrection htheta0 hthetaHalf
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact tsum_nonneg fun k =>
      selbergEulerPowerCorrection_nonneg htheta0 hthetaHalf _
  have hRle : R ≤ ((N + 1 : ℕ) : ℝ) ^ (theta - 1) := by
    exact tsum_nat_add_selbergEulerPowerCorrection_le
      htheta0 hthetaHalf N
  refine ⟨R, hR0, hRle, ?_⟩
  have hsplit :
      (∑' n : ℕ, selbergEulerPowerCorrection theta n) =
        (∑ n ∈ Finset.range N, selbergEulerPowerCorrection theta n) + R := by
    symm
    exact hsummable.sum_add_tsum_nat_add N
  rw [sum_range_power_eq_increment_add_correction htheta0 N]
  unfold selbergEulerPowerConstant
  rw [hsplit]
  dsimp [R]
  field_simp [htheta0.ne']
  ring

end HardyTheorem
