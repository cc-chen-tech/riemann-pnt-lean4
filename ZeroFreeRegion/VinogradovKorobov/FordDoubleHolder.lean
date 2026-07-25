import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalizedConditioning

open scoped BigOperators NNReal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Ford's second Holder step in finite nonnegative form.  The three factors
on the right are respectively the total mass, its square moment, and the
`2s`-moment of the complex-amplitude norms used below. -/
theorem NNReal.pow_two_mul_sum_le_mass_mul_sq_mul_moment
    {ι : Type*} (S : Finset ι) (mass value : ι → ℝ≥0)
    (s : ℕ) (hs : 1 ≤ s) :
    (∑ i ∈ S, mass i * value i) ^ (2 * s) ≤
      (∑ i ∈ S, mass i) ^ (2 * (s - 1)) *
        (∑ i ∈ S, mass i ^ 2) *
          ∑ i ∈ S, value i ^ (2 * s) := by
  have hweighted :=
    NNReal.pow_weighted_sum_le S mass value s hs
  have hcauchy :
      (∑ i ∈ S, mass i * value i ^ s) ^ 2 ≤
        (∑ i ∈ S, mass i ^ 2) *
          ∑ i ∈ S, value i ^ (2 * s) := by
    simpa only [← pow_mul, Nat.mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq S mass fun i ↦ value i ^ s)
  calc
    (∑ i ∈ S, mass i * value i) ^ (2 * s) =
        ((∑ i ∈ S, mass i * value i) ^ s) ^ 2 := by
      rw [Nat.mul_comm, pow_mul]
    _ ≤ ((∑ i ∈ S, mass i) ^ (s - 1) *
        ∑ i ∈ S, mass i * value i ^ s) ^ 2 := by
      gcongr
    _ = (∑ i ∈ S, mass i) ^ (2 * (s - 1)) *
        (∑ i ∈ S, mass i * value i ^ s) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      simp only [Nat.mul_comm]
    _ ≤ (∑ i ∈ S, mass i) ^ (2 * (s - 1)) *
        ((∑ i ∈ S, mass i ^ 2) *
          ∑ i ∈ S, value i ^ (2 * s)) :=
      mul_le_mul_of_nonneg_left hcauchy (zero_le _)
    _ = (∑ i ∈ S, mass i) ^ (2 * (s - 1)) *
        (∑ i ∈ S, mass i ^ 2) *
          ∑ i ∈ S, value i ^ (2 * s) := by
      rw [mul_assoc]

/-- Complex finite-sum form of Ford's second Holder step, with natural
multiplicities.  This is the exact algebraic inequality used in equation
(5.3) of Ford's proof before the complete and incomplete mean values are
substituted. -/
theorem nnnorm_sum_natCast_mul_pow_le_fordDoubleHolder
    {ι : Type*} (S : Finset ι) (multiplicity : ι → ℕ)
    (value : ι → ℂ) (s : ℕ) (hs : 1 ≤ s) :
    ‖∑ i ∈ S, (multiplicity i : ℂ) * value i‖₊ ^ (2 * s) ≤
      (∑ i ∈ S, (multiplicity i : ℝ≥0)) ^ (2 * (s - 1)) *
        (∑ i ∈ S, (multiplicity i : ℝ≥0) ^ 2) *
          ∑ i ∈ S, ‖value i‖₊ ^ (2 * s) := by
  calc
    ‖∑ i ∈ S, (multiplicity i : ℂ) * value i‖₊ ^ (2 * s) ≤
        (∑ i ∈ S, (multiplicity i : ℝ≥0) * ‖value i‖₊) ^
          (2 * s) := by
      gcongr
      calc
        ‖∑ i ∈ S, (multiplicity i : ℂ) * value i‖₊ ≤
            ∑ i ∈ S, ‖(multiplicity i : ℂ) * value i‖₊ :=
          nnnorm_sum_le S _
        _ = ∑ i ∈ S, (multiplicity i : ℝ≥0) * ‖value i‖₊ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp
    _ ≤ (∑ i ∈ S, (multiplicity i : ℝ≥0)) ^ (2 * (s - 1)) *
        (∑ i ∈ S, (multiplicity i : ℝ≥0) ^ 2) *
          ∑ i ∈ S, ‖value i‖₊ ^ (2 * s) :=
      NNReal.pow_two_mul_sum_le_mass_mul_sq_mul_moment
        S (fun i ↦ (multiplicity i : ℝ≥0)) (fun i ↦ ‖value i‖₊) s hs

end

end ZeroFreeRegion.VinogradovKorobov
