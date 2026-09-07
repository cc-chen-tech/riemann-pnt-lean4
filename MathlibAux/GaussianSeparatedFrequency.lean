import MathlibAux.GaussianBucketSchur
import MathlibAux.GaussianExponentialPolynomialMeanSquare

/-!
# Gaussian mean squares for uniformly separated finite frequencies

After scaling by `Delta / 2`, a separation `2 / Delta` becomes unit
separation.  Flooring the shifted nonnegative scaled frequencies gives
collision-free unit buckets, so the collision-safe Gaussian Schur theorem
reduces the Gram form to the ordinary coefficient energy.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace MathlibAux

private theorem abs_scaled_frequency_sub_lt_one_of_same_floor
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfloor : Nat.floor x = Nat.floor y) :
    |x - y| < 1 := by
  have hxLower : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
  have hxUpper : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  have hyLower : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hy
  have hyUpper : y < (Nat.floor y : ℝ) + 1 := Nat.lt_floor_add_one y
  rw [hfloor] at hxLower hxUpper
  rw [abs_lt]
  constructor <;> linarith

/-- A Gaussian Gram form over frequencies separated by `2 / Delta` is
bounded by an absolute Schur constant times the coefficient square energy.
The lower bound merely supplies a common shift before taking natural-number
unit buckets. -/
theorem gaussian_frequency_kernel_le_of_separated
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (mass : ι → ℝ) (freq : ι → ℝ)
    {Delta lower : ℝ} (hDelta : 0 < Delta)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hlower : ∀ i ∈ S, lower ≤ freq i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      2 / Delta ≤ |freq i - freq j|) :
    (∑ i ∈ S, ∑ j ∈ S,
        mass i * mass j *
          Real.exp (-(Delta ^ 2 * (freq i - freq j) ^ 2) / 4)) ≤
      gaussianBucketSchurConstant * ∑ i ∈ S, mass i ^ 2 := by
  classical
  let scaled : ι → ℝ := fun i => Delta / 2 * (freq i - lower)
  let bucket : ι → ℕ := fun i => Nat.floor (scaled i)
  have hscaledNonneg : ∀ i ∈ S, 0 ≤ scaled i := by
    intro i hi
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (hlower i hi))
  have hbucketGap : ∀ i ∈ S, ∀ j ∈ S,
      (((Nat.dist (bucket i) (bucket j) - 1 : ℕ) : ℝ) ≤
        |scaled i - scaled j|) := by
    intro i hi j hj
    exact natDist_sub_one_le_abs_sub_of_mem_unit
      (Nat.floor_le (hscaledNonneg i hi))
      (Nat.lt_floor_add_one (scaled i))
      (Nat.floor_le (hscaledNonneg j hj))
      (Nat.lt_floor_add_one (scaled j))
  have hbucketInj : Set.InjOn bucket (S : Set ι) := by
    intro i hi j hj hij
    by_contra hne
    have hsepij := hsep i hi j hj hne
    have hscalePos : 0 < Delta / 2 := by positivity
    have hscaleSep : 1 ≤ |scaled i - scaled j| := by
      have hmul := mul_le_mul_of_nonneg_left hsepij hscalePos.le
      calc
        (1 : ℝ) = (Delta / 2) * (2 / Delta) := by field_simp
        _ ≤ (Delta / 2) * |freq i - freq j| := hmul
        _ = |scaled i - scaled j| := by
          dsimp only [scaled]
          rw [show Delta / 2 * (freq i - lower) -
              Delta / 2 * (freq j - lower) =
              Delta / 2 * (freq i - freq j) by ring,
            abs_mul, abs_of_pos hscalePos]
    have hlt := abs_scaled_frequency_sub_lt_one_of_same_floor
      (hscaledNonneg i hi) (hscaledNonneg j hj) hij
    linarith
  have hschur := sum_gaussianKernel_le_bucketEnergy
    S mass scaled bucket (m := 1) (by norm_num) hmass hbucketGap
  have hkernel :
      (∑ i ∈ S, ∑ j ∈ S,
          mass i * mass j *
            Real.exp (-1 * (scaled i - scaled j) ^ 2)) ≤
        gaussianBucketSchurConstant *
          ∑ n ∈ S.image bucket,
            (∑ i ∈ S.filter (fun i => bucket i = n), mass i) ^ 2 :=
    hschur
  calc
    (∑ i ∈ S, ∑ j ∈ S,
        mass i * mass j *
          Real.exp (-(Delta ^ 2 * (freq i - freq j) ^ 2) / 4)) =
      ∑ i ∈ S, ∑ j ∈ S,
        mass i * mass j *
          Real.exp (-1 * (scaled i - scaled j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      dsimp only [scaled]
      ring
    _ ≤ gaussianBucketSchurConstant *
          ∑ n ∈ S.image bucket,
            (∑ i ∈ S.filter (fun i => bucket i = n), mass i) ^ 2 :=
      hkernel
    _ = gaussianBucketSchurConstant * ∑ i ∈ S, mass i ^ 2 := by
      congr 1
      rw [Finset.sum_image hbucketInj]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hbucketEq : bucket j = bucket i :=
          (Finset.mem_filter.mp hj).2
        exact False.elim (hji (hbucketInj
          (Finset.mem_filter.mp hj).1 hi hbucketEq))
      · intro hiFilter
        exact False.elim (hiFilter (Finset.mem_filter.mpr ⟨hi, rfl⟩))

/-- Integrated form of `gaussian_frequency_kernel_le_of_separated`. -/
theorem integral_gaussian_mul_normSq_exponentialPolynomial_le_of_separated
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {Delta lower : ℝ} (hDelta : 0 < Delta) (w : ℝ)
    (hlower : ∀ i ∈ S, lower ≤ freq i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      2 / Delta ≤ |freq i - freq j|) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq (exponentialPolynomial S coeff freq t)) ≤
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        gaussianBucketSchurConstant * ∑ i ∈ S, ‖coeff i‖ ^ 2 := by
  have hmean := integral_gaussian_mul_normSq_exponentialPolynomial_le
    hDelta w S coeff freq
  have hkernel := gaussian_frequency_kernel_le_of_separated
    S (fun i => ‖coeff i‖) freq hDelta
    (fun _ _ => norm_nonneg _) hlower hsep
  calc
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq (exponentialPolynomial S coeff freq t)) ≤
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        ∑ i ∈ S, ∑ j ∈ S,
          ‖coeff i‖ * ‖coeff j‖ *
            Real.exp (-(Delta ^ 2 * (freq i - freq j) ^ 2) / 4) := hmean
    _ ≤ Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        (gaussianBucketSchurConstant * ∑ i ∈ S, ‖coeff i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hkernel (Real.sqrt_nonneg _)
    _ = _ := by ring

end MathlibAux
