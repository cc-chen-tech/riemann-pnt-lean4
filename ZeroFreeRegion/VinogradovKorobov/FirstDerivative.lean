import ZeroFreeRegion.VinogradovKorobov.ExponentialSum
import ZeroFreeRegion.VinogradovKorobov.Trigonometric

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Finite summation by parts for a forward difference.  This is the exact
algebraic identity behind the discrete first-derivative test. -/
lemma sum_range_mul_forwardDifference (d z : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), d k * (z (k + 1) - z k) =
      d N * z (N + 1) - d 0 * z 0 +
        ∑ k ∈ Finset.range N, (d k - d (k + 1)) * z (k + 1) := by
  induction N with
  | zero => simp [mul_sub]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- If consecutive unit vectors have ratios `q k`, their sum is controlled by
the endpoints and the total variation of `(q k - 1)⁻¹`.  The monotone-phase
part of Kusmin--Landau will turn the variation term into an endpoint bound. -/
theorem norm_sum_range_le_reciprocalVariation (q z : ℕ → ℂ) (N : ℕ)
    (hq : ∀ k ≤ N, q k ≠ 1)
    (hzstep : ∀ k ≤ N, z (k + 1) = q k * z k)
    (hznorm : ∀ k ≤ N + 1, ‖z k‖ ≤ 1) :
    ‖∑ k ∈ Finset.range (N + 1), z k‖ ≤
      ‖(q 0 - 1)⁻¹‖ + ‖(q N - 1)⁻¹‖ +
        ∑ k ∈ Finset.range N,
          ‖(q k - 1)⁻¹ - (q (k + 1) - 1)⁻¹‖ := by
  let d : ℕ → ℂ := fun k ↦ (q k - 1)⁻¹
  have hrewrite : ∀ k ≤ N, d k * (z (k + 1) - z k) = z k := by
    intro k hk
    rw [hzstep k hk]
    change (q k - 1)⁻¹ * (q k * z k - z k) = z k
    rw [show q k * z k - z k = (q k - 1) * z k by ring]
    rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr (hq k hk)), one_mul]
  have hsum :
      (∑ k ∈ Finset.range (N + 1), z k) =
        ∑ k ∈ Finset.range (N + 1), d k * (z (k + 1) - z k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (hrewrite k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).symm
  have hzN : ‖z (N + 1)‖ ≤ 1 := hznorm (N + 1) le_rfl
  have hz0 : ‖z 0‖ ≤ 1 := hznorm 0 (Nat.zero_le _)
  have hzendN : ‖d N * z (N + 1)‖ ≤ ‖d N‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hzN
  have hzend0 : ‖d 0 * z 0‖ ≤ ‖d 0‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hz0
  have hzvar :
      ∑ k ∈ Finset.range N, ‖(d k - d (k + 1)) * z (k + 1)‖ ≤
        ∑ k ∈ Finset.range N, ‖d k - d (k + 1)‖ := by
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    apply hznorm
    exact Nat.succ_le_succ (Nat.le_of_lt (Finset.mem_range.mp hk))
  rw [hsum, sum_range_mul_forwardDifference]
  calc
    ‖d N * z (N + 1) - d 0 * z 0 +
          ∑ k ∈ Finset.range N, (d k - d (k + 1)) * z (k + 1)‖
        ≤ ‖d N * z (N + 1) - d 0 * z 0‖ +
            ‖∑ k ∈ Finset.range N, (d k - d (k + 1)) * z (k + 1)‖ :=
      norm_add_le _ _
    _ ≤ (‖d N * z (N + 1)‖ + ‖d 0 * z 0‖) +
            ∑ k ∈ Finset.range N, ‖(d k - d (k + 1)) * z (k + 1)‖ := by
      gcongr
      · exact norm_sub_le _ _
      · exact norm_sum_le _ _
    _ ≤ ‖d N‖ + ‖d 0‖ +
            ∑ k ∈ Finset.range N, ‖d k - d (k + 1)‖ := by
      gcongr
    _ = ‖(q 0 - 1)⁻¹‖ + ‖(q N - 1)⁻¹‖ +
            ∑ k ∈ Finset.range N,
              ‖(q k - 1)⁻¹ - (q (k + 1) - 1)⁻¹‖ := by
      simp only [d]
      ring

/-- The ratio between consecutive phase terms. -/
noncomputable def phaseRatio (f : ℕ → ℝ) (k : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((f (k + 1) - f k : ℝ) : ℂ))

lemma phaseRatio_ne_one_of_increment_mem (f : ℕ → ℝ) (k : ℕ)
    (hpos : 0 < f (k + 1) - f k)
    (hlt : f (k + 1) - f k < 2 * Real.pi) :
    phaseRatio f k ≠ 1 := by
  intro h
  have hnorm : ‖phaseRatio f k - 1‖ = 0 := by rw [h]; simp
  rw [phaseRatio, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs] at hnorm
  have hs : 0 < Real.sin ((f (k + 1) - f k) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  rw [abs_of_pos (mul_pos (by norm_num) hs)] at hnorm
  linarith

lemma phaseTerm_succ_eq_phaseRatio_mul (f : ℕ → ℝ) (k : ℕ) :
    phaseTerm f (k + 1) = phaseRatio f k * phaseTerm f k := by
  rw [phaseTerm, phaseTerm, phaseRatio, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The reciprocal-variation estimate specialized to a real phase. -/
theorem norm_phaseSum_le_reciprocalVariation (f : ℕ → ℝ) (N : ℕ)
    (hq : ∀ k ≤ N, phaseRatio f k ≠ 1) :
    ‖∑ k ∈ Finset.range (N + 1), phaseTerm f k‖ ≤
      ‖(phaseRatio f 0 - 1)⁻¹‖ + ‖(phaseRatio f N - 1)⁻¹‖ +
        ∑ k ∈ Finset.range N,
          ‖(phaseRatio f k - 1)⁻¹ - (phaseRatio f (k + 1) - 1)⁻¹‖ := by
  apply norm_sum_range_le_reciprocalVariation (phaseRatio f) (phaseTerm f) N hq
  · intro k hk
    exact phaseTerm_succ_eq_phaseRatio_mul f k
  · intro k hk
    exact (norm_phaseTerm f k).le

/-- Discrete Kusmin--Landau first-derivative estimate in endpoint form.  The
phase increments are monotone and remain in the same nonresonant turn of the
unit circle. -/
theorem kusminLandau_endpoint_bound (f : ℕ → ℝ) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < f (k + 1) - f k)
    (hlt : ∀ k ≤ N, f (k + 1) - f k < 2 * Real.pi)
    (hmono : ∀ k < N,
      f (k + 1) - f k ≤ f (k + 2) - f (k + 1)) :
    ‖∑ k ∈ Finset.range (N + 1), phaseTerm f k‖ ≤
      ‖(Complex.exp (Complex.I * ((f 1 - f 0 : ℝ) : ℂ)) - 1)⁻¹‖ +
      ‖(Complex.exp (Complex.I * ((f (N + 1) - f N : ℝ) : ℂ)) - 1)⁻¹‖ +
      (Real.cot ((f 1 - f 0) / 2) -
        Real.cot ((f (N + 1) - f N) / 2)) / 2 := by
  have hq : ∀ k ≤ N, phaseRatio f k ≠ 1 := fun k hk ↦
    phaseRatio_ne_one_of_increment_mem f k (hpos k hk) (hlt k hk)
  have hbound := norm_phaseSum_le_reciprocalVariation f N hq
  have hvariation := sum_norm_reciprocal_exp_sub_one_eq
    (fun k ↦ f (k + 1) - f k) N hpos hlt hmono
  simp only [phaseRatio] at hbound
  rw [hvariation] at hbound
  simpa using hbound

end ZeroFreeRegion.VinogradovKorobov
