import HardyTheorem.SelbergSqrtZetaSignedRationalSeparation
import MathlibAux.SeparatedFrequencySquareEnvelope

/-!
# Stationary square-envelope bound for rational Selberg frequencies

The collected rational frequencies are uniformly separated.  Reindexing them
as a finite set of real frequencies lets the generic stationary-safe packing
estimate control the full reciprocal-square envelope without a cardinality
loss.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The stationary-safe reciprocal-square envelope over the actual collected
rational Selberg frequencies is bounded independently of the support size. -/
theorem sum_sq_stationaryMinReciprocalEnvelope_rationalSupport_le
    {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    {H t : ℝ} (hH : 0 ≤ H) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        (MathlibAux.stationaryMinReciprocalEnvelope
          H (-deriv thetaModel t)
          (selbergSqrtZetaSignedRationalFrequency q)) ^ 2) ≤
      H ^ 2 + 12 * H * ((N * X ^ 2 : ℕ) : ℝ) := by
  classical
  let Q : Finset ℚ := selbergSqrtZetaSignedRationalSupport N X
  let omega : ℚ → ℝ := selbergSqrtZetaSignedRationalFrequency
  let S : Finset ℝ := Q.image omega
  let M : ℝ := ((N * X ^ 2 : ℕ) : ℝ)
  let F : ℝ → ℝ := fun x =>
    (MathlibAux.stationaryMinReciprocalEnvelope
      H (-deriv thetaModel t) x) ^ 2
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast Nat.mul_pos hN (pow_pos hX 2)
  have hDelta : 0 < 1 / M := by positivity
  have hQsupport : ∀ q ∈ Q,
      q ∈ selbergSqrtZetaSignedRationalSupport N X := by
    intro q hq
    exact hq
  have hinj : Set.InjOn omega (Q : Set ℚ) := by
    intro q hq r hr heq
    by_contra hne
    have hsep :=
      one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
        (hQsupport q hq) (hQsupport r hr) hne
    have hzero : |omega q - omega r| = 0 := by
      rw [heq, sub_self, abs_zero]
    rw [show ((N * X ^ 2 : ℕ) : ℝ) = M by rfl, hzero] at hsep
    exact (not_lt_of_ge hsep) hDelta
  have hsepS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      1 / M ≤ |x - y| := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
    have hqr : q ≠ r := by
      intro h
      subst r
      exact hxy rfl
    simpa only [omega, M] using
      one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
        (hQsupport q hq) (hQsupport r hr) hqr
  have hsum :
      (∑ q ∈ Q, F (omega q)) = ∑ x ∈ S, F x := by
    exact (Finset.sum_image hinj).symm
  have hbound :=
    MathlibAux.sum_sq_stationaryMinReciprocalEnvelope_le
      S (1 / M) H (-deriv thetaModel t) hDelta hH hsepS
  rw [hsum]
  calc
    (∑ x ∈ S, F x) ≤ H ^ 2 + 12 * H / (1 / M) := by
      simpa only [F] using hbound
    _ = H ^ 2 + 12 * H * M := by
      field_simp [hM.ne']
    _ = H ^ 2 + 12 * H * ((N * X ^ 2 : ℕ) : ℝ) := by
      rfl

end HardyTheorem
