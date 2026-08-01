import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist

open scoped BigOperators

namespace MathlibAux

noncomputable section

/-!
# A collision-safe Gaussian Schur bound

Unit frequency buckets avoid any minimum-spacing hypothesis inside a bucket.
The Gaussian interaction between buckets is dominated by a summable kernel,
and a finite Schur argument reduces the full quadratic form to the sum of
squared bucket masses.
-/

/-- Summable profile attached to a distance between unit frequency buckets. -/
def gaussianBucketProfile (d : ℕ) : ℝ :=
  Real.exp (-((d - 1 : ℕ) : ℝ))

/-- Symmetric interaction kernel between two unit frequency buckets. -/
def gaussianBucketKernel (n k : ℕ) : ℝ :=
  gaussianBucketProfile (Nat.dist n k)

/-- A uniform row-sum bound for `gaussianBucketKernel`. -/
def gaussianBucketSchurConstant : ℝ :=
  2 * ∑' d : ℕ, gaussianBucketProfile d

theorem gaussianBucketProfile_nonneg (d : ℕ) :
    0 ≤ gaussianBucketProfile d :=
  (Real.exp_pos _).le

theorem gaussianBucketKernel_nonneg (n k : ℕ) :
    0 ≤ gaussianBucketKernel n k :=
  gaussianBucketProfile_nonneg _

theorem gaussianBucketKernel_comm (n k : ℕ) :
    gaussianBucketKernel n k = gaussianBucketKernel k n := by
  rw [gaussianBucketKernel, gaussianBucketKernel, Nat.dist_comm]

/-- The shifted exponential bucket profile is summable. -/
theorem summable_gaussianBucketProfile :
    Summable gaussianBucketProfile := by
  have htail :
      Summable (fun d : ℕ => gaussianBucketProfile (d + 1)) := by
    simpa [gaussianBucketProfile] using Real.summable_exp_neg_nat
  exact (summable_nat_add_iff 1).mp
    (by simpa [Nat.add_comm] using htail)

/-- Closed form of the fixed Schur constant. -/
theorem gaussianBucketSchurConstant_eq :
    gaussianBucketSchurConstant =
      2 * (1 + (1 - Real.exp (-1))⁻¹) := by
  have htail :
      (∑' d : ℕ, Real.exp (-(d : ℝ))) =
        (1 - Real.exp (-1))⁻¹ := by
    have hfun :
        (fun d : ℕ => Real.exp (-(d : ℝ))) =
          fun d : ℕ => Real.exp (-1) ^ d := by
      funext d
      rw [show -(d : ℝ) = (d : ℝ) * (-1) by ring,
        Real.exp_nat_mul]
    rw [hfun]
    exact tsum_geometric_of_lt_one
      (Real.exp_pos (-1)).le
      (Real.exp_lt_one_iff.mpr (by norm_num))
  have hsplit :=
    summable_gaussianBucketProfile.sum_add_tsum_nat_add 1
  have htailFun :
      (fun d : ℕ => gaussianBucketProfile (d + 1)) =
        fun d : ℕ => Real.exp (-(d : ℝ)) := by
    funext d
    simp [gaussianBucketProfile]
  unfold gaussianBucketSchurConstant
  calc
    2 * ∑' d : ℕ, gaussianBucketProfile d =
        2 * ((∑ d ∈ Finset.range 1, gaussianBucketProfile d) +
          ∑' d : ℕ, gaussianBucketProfile (d + 1)) := by
      rw [hsplit]
    _ = 2 * (1 + (1 - Real.exp (-1))⁻¹) := by
      rw [htailFun, htail]
      simp [gaussianBucketProfile]

/-- The Schur constant is strictly positive. -/
theorem gaussianBucketSchurConstant_pos :
    0 < gaussianBucketSchurConstant := by
  rw [gaussianBucketSchurConstant_eq]
  have hden : 0 < 1 - Real.exp (-1) := by
    linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)]
  positivity

private theorem card_filter_natDist_eq_le_two
    (K : Finset ℕ) (n d : ℕ) :
    (K.filter fun k => Nat.dist n k = d).card ≤ 2 := by
  have hsubset :
      (K.filter fun k => Nat.dist n k = d) ⊆ {n - d, n + d} := by
    intro k hk
    have hdist : Nat.dist n k = d := (Finset.mem_filter.mp hk).2
    by_cases hkn : k ≤ n
    · have hsub : n - k = d := by
        simpa [Nat.dist_eq_sub_of_le_right hkn] using hdist
      have hkEq : k = n - d := by omega
      simp [hkEq]
    · have hnk : n ≤ k := by omega
      have hsub : k - n = d := by
        simpa [Nat.dist_eq_sub_of_le hnk] using hdist
      have hkEq : k = n + d := by omega
      simp [hkEq]
  exact (Finset.card_le_card hsubset).trans Finset.card_le_two

/-- Every finite row of the bucket kernel is bounded by one absolute
constant, independently of the number of buckets. -/
theorem sum_gaussianBucketKernel_le (K : Finset ℕ) (n : ℕ) :
    (∑ k ∈ K, gaussianBucketKernel n k) ≤
      gaussianBucketSchurConstant := by
  classical
  let D : Finset ℕ := K.image (Nat.dist n)
  have hmaps : ∀ k ∈ K, Nat.dist n k ∈ D := by
    intro k hk
    exact Finset.mem_image_of_mem _ hk
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun k => gaussianBucketKernel n k)
  calc
    (∑ k ∈ K, gaussianBucketKernel n k) =
        ∑ d ∈ D,
          ∑ k ∈ K.filter (fun k => Nat.dist n k = d),
            gaussianBucketKernel n k := hfiber.symm
    _ = ∑ d ∈ D,
        ((K.filter fun k => Nat.dist n k = d).card : ℝ) *
          gaussianBucketProfile d := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ k ∈ K.filter (fun k => Nat.dist n k = d),
            gaussianBucketKernel n k) =
            ∑ _k ∈ K.filter (fun k => Nat.dist n k = d),
              gaussianBucketProfile d := by
          apply Finset.sum_congr rfl
          intro k hk
          have hdist : Nat.dist n k = d := (Finset.mem_filter.mp hk).2
          simp [gaussianBucketKernel, hdist]
        _ = ((K.filter fun k => Nat.dist n k = d).card : ℝ) *
              gaussianBucketProfile d := by
          simp
    _ ≤ ∑ d ∈ D, 2 * gaussianBucketProfile d := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_filter_natDist_eq_le_two K n d
      · exact gaussianBucketProfile_nonneg d
    _ = 2 * ∑ d ∈ D, gaussianBucketProfile d := by
      rw [Finset.mul_sum]
    _ ≤ 2 * ∑' d : ℕ, gaussianBucketProfile d := by
      exact mul_le_mul_of_nonneg_left
        (summable_gaussianBucketProfile.sum_le_tsum D
          (fun d hd => gaussianBucketProfile_nonneg d))
        (by norm_num)
    _ = gaussianBucketSchurConstant := rfl

/-- A Gaussian interaction is dominated by the bucket kernel whenever the
frequency gap is at least the bucket distance minus one. -/
theorem exp_neg_mul_sq_le_gaussianBucketKernel
    {m x : ℝ} {n k : ℕ}
    (hm : 1 ≤ m)
    (hgap : (((Nat.dist n k - 1 : ℕ) : ℝ) ≤ |x|)) :
    Real.exp (-m * x ^ 2) ≤ gaussianBucketKernel n k := by
  let rNat : ℕ := Nat.dist n k - 1
  let r : ℝ := (rNat : ℝ)
  have hm0 : 0 ≤ m := le_trans (by norm_num) hm
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hxSq : |x| ^ 2 = x ^ 2 := by
    rw [sq_abs]
  have hrSqLe : r ^ 2 ≤ x ^ 2 := by
    rw [← hxSq]
    exact pow_le_pow_left₀ hr0 hgap 2
  by_cases hrNatZero : rNat = 0
  · have hexp : Real.exp (-m * x ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg hm0 (sq_nonneg x)]
    simpa [gaussianBucketKernel, gaussianBucketProfile, rNat, r,
      hrNatZero] using hexp
  · have hrOneNat : 1 ≤ rNat := Nat.one_le_iff_ne_zero.mpr hrNatZero
    have hrOne : 1 ≤ r := by
      dsimp [r]
      exact_mod_cast hrOneNat
    have hrLeSq : r ≤ r ^ 2 := by nlinarith
    have hxSqLeMul : x ^ 2 ≤ m * x ^ 2 := by
      nlinarith [sq_nonneg x]
    have hrLe : r ≤ m * x ^ 2 :=
      hrLeSq.trans (hrSqLe.trans hxSqLeMul)
    have hexp :
        Real.exp (-m * x ^ 2) ≤ Real.exp (-r) :=
      Real.exp_le_exp.mpr (by nlinarith)
    simpa [gaussianBucketKernel, gaussianBucketProfile, rNat, r]
      using hexp

/-- Frequencies lying in unit intervals indexed by `n` and `k` are
separated by at least the integer bucket distance minus one. -/
theorem natDist_sub_one_le_abs_sub_of_mem_unit
    {a b : ℝ} {n k : ℕ}
    (hna : (n : ℝ) ≤ a) (han : a < (n : ℝ) + 1)
    (hkb : (k : ℝ) ≤ b) (hbk : b < (k : ℝ) + 1) :
    (((Nat.dist n k - 1 : ℕ) : ℝ) ≤ |a - b|) := by
  rcases le_total n k with hnk | hkn
  · rw [Nat.dist_eq_sub_of_le hnk]
    by_cases hclose : k ≤ n + 1
    · have hzero : k - n - 1 = 0 := by omega
      simp [hzero]
    · have hfar : n + 1 ≤ k := by omega
      have hab : a ≤ b := by
        have hcast : (n : ℝ) + 1 ≤ (k : ℝ) := by
          exact_mod_cast hfar
        linarith
      rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      have hcast :
          ((k - n - 1 : ℕ) : ℝ) =
            (k : ℝ) - (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k - n), Nat.cast_sub hnk]
        norm_num
      rw [hcast]
      linarith
  · rw [Nat.dist_eq_sub_of_le_right hkn]
    by_cases hclose : n ≤ k + 1
    · have hzero : n - k - 1 = 0 := by omega
      simp [hzero]
    · have hfar : k + 1 ≤ n := by omega
      have hba : b ≤ a := by
        have hcast : (k : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast hfar
        linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      have hcast :
          ((n - k - 1 : ℕ) : ℝ) =
            (n : ℝ) - (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n - k), Nat.cast_sub hkn]
        norm_num
      rw [hcast]
      linarith

/-- Schur bound for the bucket kernel itself. -/
theorem sum_mul_gaussianBucketKernel_le
    (K : Finset ℕ) (u : ℕ → ℝ) :
    (∑ n ∈ K, ∑ k ∈ K,
        u n * u k * gaussianBucketKernel n k) ≤
      gaussianBucketSchurConstant * ∑ n ∈ K, u n ^ 2 := by
  have hpair (n k : ℕ) :
      2 * (u n * u k * gaussianBucketKernel n k) ≤
        (u n ^ 2 + u k ^ 2) * gaussianBucketKernel n k := by
    have hsq : 0 ≤ (u n - u k) ^ 2 := sq_nonneg _
    have hk := gaussianBucketKernel_nonneg n k
    nlinarith
  have htwo :
      2 * (∑ n ∈ K, ∑ k ∈ K,
          u n * u k * gaussianBucketKernel n k) ≤
        ∑ n ∈ K, ∑ k ∈ K,
          (u n ^ 2 + u k ^ 2) * gaussianBucketKernel n k := by
    calc
      2 * (∑ n ∈ K, ∑ k ∈ K,
          u n * u k * gaussianBucketKernel n k) =
          ∑ n ∈ K, ∑ k ∈ K,
            2 * (u n * u k * gaussianBucketKernel n k) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro k hk
        exact hpair n k
  have hleft :
      (∑ n ∈ K, ∑ k ∈ K,
          u n ^ 2 * gaussianBucketKernel n k) ≤
        gaussianBucketSchurConstant * ∑ n ∈ K, u n ^ 2 := by
    calc
      (∑ n ∈ K, ∑ k ∈ K,
          u n ^ 2 * gaussianBucketKernel n k) =
          ∑ n ∈ K,
            u n ^ 2 * ∑ k ∈ K, gaussianBucketKernel n k := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ K,
          u n ^ 2 * gaussianBucketSchurConstant := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left
          (sum_gaussianBucketKernel_le K n) (sq_nonneg _)
      _ = gaussianBucketSchurConstant * ∑ n ∈ K, u n ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hright :
      (∑ n ∈ K, ∑ k ∈ K,
          u k ^ 2 * gaussianBucketKernel n k) ≤
        gaussianBucketSchurConstant * ∑ n ∈ K, u n ^ 2 := by
    calc
      (∑ n ∈ K, ∑ k ∈ K,
          u k ^ 2 * gaussianBucketKernel n k) =
          ∑ k ∈ K, ∑ n ∈ K,
            u k ^ 2 * gaussianBucketKernel k n := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro n hn
        rw [gaussianBucketKernel_comm]
      _ ≤ gaussianBucketSchurConstant * ∑ k ∈ K, u k ^ 2 :=
        hleft
  have hsplit :
      (∑ n ∈ K, ∑ k ∈ K,
          (u n ^ 2 + u k ^ 2) * gaussianBucketKernel n k) =
        (∑ n ∈ K, ∑ k ∈ K,
          u n ^ 2 * gaussianBucketKernel n k) +
        (∑ n ∈ K, ∑ k ∈ K,
          u k ^ 2 * gaussianBucketKernel n k) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hsplit] at htwo
  linarith

private theorem sum_mul_comp_bucket_eq
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (mass : ι → ℝ) (bucket : ι → ℕ)
    (f : ℕ → ℝ) :
    (∑ i ∈ S, mass i * f (bucket i)) =
      ∑ n ∈ S.image bucket,
        (∑ i ∈ S.filter (fun i => bucket i = n), mass i) * f n := by
  classical
  have hmaps : ∀ i ∈ S, bucket i ∈ S.image bucket := by
    intro i hi
    exact Finset.mem_image_of_mem _ hi
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => mass i * f (bucket i))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : bucket i = n := (Finset.mem_filter.mp hi).2
  rw [hib]

/-- Collision-safe Gaussian Schur estimate. Terms in the same bucket may
have repeated or arbitrarily close frequencies; only the total mass of each
bucket enters the upper bound. -/
theorem sum_gaussianKernel_le_bucketEnergy
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (mass : ι → ℝ) (freq : ι → ℝ)
    (bucket : ι → ℕ) {m : ℝ}
    (hm : 1 ≤ m)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hgap : ∀ i ∈ S, ∀ j ∈ S,
      (((Nat.dist (bucket i) (bucket j) - 1 : ℕ) : ℝ) ≤
        |freq i - freq j|)) :
    (∑ i ∈ S, ∑ j ∈ S,
        mass i * mass j *
          Real.exp (-m * (freq i - freq j) ^ 2)) ≤
      gaussianBucketSchurConstant *
        ∑ n ∈ S.image bucket,
          (∑ i ∈ S.filter (fun i => bucket i = n), mass i) ^ 2 := by
  classical
  let K : Finset ℕ := S.image bucket
  let u : ℕ → ℝ := fun n =>
    ∑ i ∈ S.filter (fun i => bucket i = n), mass i
  have hpoint :
      ∀ i ∈ S, ∀ j ∈ S,
        mass i * mass j *
            Real.exp (-m * (freq i - freq j) ^ 2) ≤
          mass i * mass j *
            gaussianBucketKernel (bucket i) (bucket j) := by
    intro i hi j hj
    exact mul_le_mul_of_nonneg_left
      (exp_neg_mul_sq_le_gaussianBucketKernel hm (hgap i hi j hj))
      (mul_nonneg (hmass i hi) (hmass j hj))
  have hgaussian :
      (∑ i ∈ S, ∑ j ∈ S,
          mass i * mass j *
            Real.exp (-m * (freq i - freq j) ^ 2)) ≤
        ∑ i ∈ S, ∑ j ∈ S,
          mass i * mass j *
            gaussianBucketKernel (bucket i) (bucket j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hpoint i hi j hj
  have hgroup :
      (∑ i ∈ S, ∑ j ∈ S,
          mass i * mass j *
            gaussianBucketKernel (bucket i) (bucket j)) =
        ∑ n ∈ K, ∑ k ∈ K,
          u n * u k * gaussianBucketKernel n k := by
    calc
      (∑ i ∈ S, ∑ j ∈ S,
          mass i * mass j *
            gaussianBucketKernel (bucket i) (bucket j)) =
          ∑ i ∈ S, mass i *
            (∑ j ∈ S,
              mass j * gaussianBucketKernel (bucket i) (bucket j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i ∈ S, mass i *
          (∑ k ∈ K, u k * gaussianBucketKernel (bucket i) k) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        simpa [K, u] using
          sum_mul_comp_bucket_eq S mass bucket
            (gaussianBucketKernel (bucket i))
      _ = ∑ n ∈ K, u n *
          (∑ k ∈ K, u k * gaussianBucketKernel n k) := by
        simpa [K, u] using
          sum_mul_comp_bucket_eq S mass bucket
            (fun n => ∑ k ∈ K,
              u k * gaussianBucketKernel n k)
      _ = ∑ n ∈ K, ∑ k ∈ K,
          u n * u k * gaussianBucketKernel n k := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  calc
    (∑ i ∈ S, ∑ j ∈ S,
        mass i * mass j *
          Real.exp (-m * (freq i - freq j) ^ 2)) ≤
        ∑ i ∈ S, ∑ j ∈ S,
          mass i * mass j *
            gaussianBucketKernel (bucket i) (bucket j) := hgaussian
    _ = ∑ n ∈ K, ∑ k ∈ K,
        u n * u k * gaussianBucketKernel n k := hgroup
    _ ≤ gaussianBucketSchurConstant * ∑ n ∈ K, u n ^ 2 :=
      sum_mul_gaussianBucketKernel_le K u
    _ = gaussianBucketSchurConstant *
        ∑ n ∈ S.image bucket,
          (∑ i ∈ S.filter (fun i => bucket i = n), mass i) ^ 2 := rfl

end

end MathlibAux
