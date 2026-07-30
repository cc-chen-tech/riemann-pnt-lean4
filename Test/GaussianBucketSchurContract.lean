import MathlibAux.GaussianBucketSchur

open scoped BigOperators

namespace MathlibAux

#check gaussianBucketProfile
#check gaussianBucketKernel
#check gaussianBucketSchurConstant

#check
  (gaussianBucketProfile_nonneg :
    ∀ d : ℕ, 0 ≤ gaussianBucketProfile d)

#check
  (gaussianBucketKernel_nonneg :
    ∀ n k : ℕ, 0 ≤ gaussianBucketKernel n k)

#check
  (gaussianBucketKernel_comm :
    ∀ n k : ℕ,
      gaussianBucketKernel n k = gaussianBucketKernel k n)

#check
  (summable_gaussianBucketProfile :
    Summable gaussianBucketProfile)

#check
  (gaussianBucketSchurConstant_eq :
    gaussianBucketSchurConstant =
      2 * (1 + (1 - Real.exp (-1))⁻¹))

#check
  (gaussianBucketSchurConstant_pos :
    0 < gaussianBucketSchurConstant)

#check
  (sum_gaussianBucketKernel_le :
    ∀ (K : Finset ℕ) (n : ℕ),
      (∑ k ∈ K, gaussianBucketKernel n k) ≤
        gaussianBucketSchurConstant)

#check
  (exp_neg_mul_sq_le_gaussianBucketKernel :
    ∀ {m x : ℝ} {n k : ℕ},
      1 ≤ m →
      (((Nat.dist n k - 1 : ℕ) : ℝ) ≤ |x|) →
      Real.exp (-m * x ^ 2) ≤ gaussianBucketKernel n k)

#check
  (natDist_sub_one_le_abs_sub_of_mem_unit :
    ∀ {a b : ℝ} {n k : ℕ},
      (n : ℝ) ≤ a →
      a < (n : ℝ) + 1 →
      (k : ℝ) ≤ b →
      b < (k : ℝ) + 1 →
      (((Nat.dist n k - 1 : ℕ) : ℝ) ≤ |a - b|))

#check
  (sum_mul_gaussianBucketKernel_le :
    ∀ (K : Finset ℕ) (u : ℕ → ℝ),
      (∑ n ∈ K, ∑ k ∈ K,
          u n * u k * gaussianBucketKernel n k) ≤
        gaussianBucketSchurConstant * ∑ n ∈ K, u n ^ 2)

#check
  (sum_gaussianKernel_le_bucketEnergy :
    ∀ {ι : Type*} [DecidableEq ι]
      (S : Finset ι) (mass : ι → ℝ) (freq : ι → ℝ)
      (bucket : ι → ℕ) {m : ℝ},
      1 ≤ m →
      (∀ i ∈ S, 0 ≤ mass i) →
      (∀ i ∈ S, ∀ j ∈ S,
        (((Nat.dist (bucket i) (bucket j) - 1 : ℕ) : ℝ) ≤
          |freq i - freq j|)) →
      (∑ i ∈ S, ∑ j ∈ S,
          mass i * mass j *
            Real.exp (-m * (freq i - freq j) ^ 2)) ≤
        gaussianBucketSchurConstant *
          ∑ n ∈ S.image bucket,
            (∑ i ∈ S.filter (fun i => bucket i = n), mass i) ^ 2)

end MathlibAux
