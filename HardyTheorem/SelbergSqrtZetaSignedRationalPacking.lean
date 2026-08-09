import HardyTheorem.SelbergSqrtZetaSignedRationalSeparation
import MathlibAux.SeparatedFrequencyPacking

/-!
# Packing of collected rational Selberg frequencies

The uniform logarithmic frequency separation gives a linear bound for the
number of collected frequencies in any real ball.  This is the distribution
estimate needed before summing stationary-safe reciprocal-square envelopes.
-/

namespace HardyTheorem

/-- Collected rational frequencies whose logarithmic frequency lies in the
closed radius-`r` ball around `xi`. -/
noncomputable def selbergSqrtZetaSignedRationalFrequencyBallSupport
    (N X : ℕ) (xi r : ℝ) : Finset ℚ :=
  (selbergSqrtZetaSignedRationalSupport N X).filter
    (fun q => |selbergSqrtZetaSignedRationalFrequency q - xi| ≤ r)

/-- A radius-`r` frequency ball contains at most `1 + 2r * N * X^2`
collected rational frequencies, in multiplication form. -/
theorem card_sub_one_div_nat_mul_sq_le_two_mul_radius
    {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    (xi : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (((selbergSqrtZetaSignedRationalFrequencyBallSupport N X xi r).card - 1 :
        ℕ) : ℝ) *
        (1 / ((N * X ^ 2 : ℕ) : ℝ)) ≤
      2 * r := by
  classical
  let Q : Finset ℚ :=
    selbergSqrtZetaSignedRationalFrequencyBallSupport N X xi r
  let omega : ℚ → ℝ := selbergSqrtZetaSignedRationalFrequency
  let S : Finset ℝ := Q.image omega
  let M : ℝ := ((N * X ^ 2 : ℕ) : ℝ)
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast Nat.mul_pos hN (pow_pos hX 2)
  have hdelta : 0 < 1 / M := by positivity
  have hQsupport : ∀ q ∈ Q,
      q ∈ selbergSqrtZetaSignedRationalSupport N X := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hinj : Set.InjOn omega (Q : Set ℚ) := by
    intro q hq p hp heq
    by_contra hne
    have hsep :=
      one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
        (hQsupport q hq) (hQsupport p hp) hne
    have hzero : |omega q - omega p| = 0 := by
      rw [heq, sub_self, abs_zero]
    rw [show ((N * X ^ 2 : ℕ) : ℝ) = M by rfl, hzero] at hsep
    exact (not_lt_of_ge hsep) hdelta
  have hcard : S.card = Q.card := by
    exact Finset.card_image_of_injOn hinj
  have hsepS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      1 / M ≤ |x - y| := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
    have hqp : q ≠ p := by
      intro h
      subst p
      exact hxy rfl
    simpa only [omega, M] using
      one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
        (hQsupport q hq) (hQsupport p hp) hqp
  have hballS : ∀ x ∈ S, |x - xi| ≤ r := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    exact (Finset.mem_filter.mp hq).2
  have hpacking :=
    MathlibAux.card_sub_one_mul_separation_le_two_mul_radius
      S (1 / M) xi r hdelta hr hsepS hballS
  simpa only [hcard, Q, S, M] using hpacking

end HardyTheorem
