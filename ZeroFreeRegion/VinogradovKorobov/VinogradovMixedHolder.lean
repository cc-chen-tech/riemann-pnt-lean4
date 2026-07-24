import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedMoment

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Normalized real moment of the main Weyl block restricted to one residue
class modulo `p^a`. -/
noncomputable def normalizedVinogradovMixedMainNormMoment
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) : ℝ :=
  (((p ^ B : ℕ) : ℝ)⁻¹ ^ k) *
    ∑ c : Fin k → ZMod (p ^ B),
      ‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖ ^ (2 * s)

/-- Normalized real moment of the affine restricted tail Weyl block. -/
noncomputable def normalizedVinogradovMixedTailNormMoment
    (p B b k s Y : ℕ) [NeZero (p ^ B)] (eta : ℤ) : ℝ :=
  (((p ^ B : ℕ) : ℝ)⁻¹ ^ k) *
    ∑ c : Fin k → ZMod (p ^ B),
      ‖vinogradovIntWeylSum (p ^ B) k Y
        (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * s)

/-- Pairing each Weyl block with its conjugate turns the mixed integrand into
the product of two nonnegative real norm powers. -/
private theorem mixedWeylIntegrand_eq_norm_product
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) (c : Fin k → ZMod (p ^ B)) :
    vinogradovMixedMainWeylSum p a (p ^ B) k X xi c ^ r *
        (starRingEnd ℂ)
            (vinogradovMixedMainWeylSum p a (p ^ B) k X xi c) ^ r *
        (starRingEnd ℂ)
            (vinogradovIntWeylSum (p ^ B) k Y
              (vinogradovMixedTailValue p b Y eta) c) ^ t *
        vinogradovIntWeylSum (p ^ B) k Y
            (vinogradovMixedTailValue p b Y eta) c ^ t =
      ((‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖ ^ (2 * r) *
        ‖vinogradovIntWeylSum (p ^ B) k Y
          (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * t) : ℝ) : ℂ) := by
  let F := vinogradovMixedMainWeylSum p a (p ^ B) k X xi c
  let G := vinogradovIntWeylSum (p ^ B) k Y
    (vinogradovMixedTailValue p b Y eta) c
  have hpair (z : ℂ) (n : ℕ) :
      z ^ n * (starRingEnd ℂ) z ^ n =
        ((‖z‖ ^ (2 * n) : ℝ) : ℂ) := by
    rw [← mul_pow, Complex.mul_conj']
    simp only [Complex.ofReal_pow, pow_mul]
  have hpair' (z : ℂ) (n : ℕ) :
      (starRingEnd ℂ) z ^ n * z ^ n =
        ((‖z‖ ^ (2 * n) : ℝ) : ℂ) := by
    rw [mul_comm]
    exact hpair z n
  change F ^ r * (starRingEnd ℂ) F ^ r *
      (starRingEnd ℂ) G ^ t * G ^ t = _
  calc
    F ^ r * (starRingEnd ℂ) F ^ r *
        (starRingEnd ℂ) G ^ t * G ^ t =
      ((‖F‖ ^ (2 * r) : ℝ) : ℂ) *
        ((‖G‖ ^ (2 * t) : ℝ) : ℂ) := by
          rw [hpair F r, mul_assoc, hpair' G t]
    _ = _ := by
      rw [← Complex.ofReal_mul]

/-- The mixed Fourier moment is a nonnegative normalized average of the
product of the main and tail norm powers. -/
theorem normalizedVinogradovMixedModConditionedMoment_eq_norm_product_average
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) :
    normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta =
      ((((p ^ B : ℕ) : ℝ)⁻¹ ^ k) *
        ∑ c : Fin k → ZMod (p ^ B),
          ‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖ ^ (2 * r) *
            ‖vinogradovIntWeylSum (p ^ B) k Y
              (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * t) : ℝ) := by
  unfold normalizedVinogradovMixedModConditionedMoment
  simp_rw [mixedWeylIntegrand_eq_norm_product]
  have hfactor :
      ((p ^ B : ℕ) : ℂ)⁻¹ ^ k =
        (((((p ^ B : ℕ) : ℝ)⁻¹ ^ k : ℝ)) : ℂ) := by
    rw [Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  rw [hfactor, ← Complex.ofReal_sum, ← Complex.ofReal_mul]

/-- Cauchy separation of the mixed moment.  Instead of discarding the tail
as `Y^(2t)` free tuple pairs, its contribution is retained as a genuine
normalized `4t`-th moment. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_separateMoments
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ^ 2 ≤
      normalizedVinogradovMixedMainNormMoment p B a k (2 * r) X xi *
        normalizedVinogradovMixedTailNormMoment p B b k (2 * t) Y eta := by
  rw [normalizedVinogradovMixedModConditionedMoment_eq_norm_product_average]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · unfold normalizedVinogradovMixedMainNormMoment
    unfold normalizedVinogradovMixedTailNormMoment
    let q : ℝ := (((p ^ B : ℕ) : ℝ)⁻¹ ^ k)
    let main : (Fin k → ZMod (p ^ B)) → ℝ := fun c ↦
      ‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖ ^ (2 * r)
    let tail : (Fin k → ZMod (p ^ B)) → ℝ := fun c ↦
      ‖vinogradovIntWeylSum (p ^ B) k Y
        (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * t)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin k → ZMod (p ^ B))) main tail
    have hmain :
        (∑ c : Fin k → ZMod (p ^ B), main c ^ 2) =
          ∑ c : Fin k → ZMod (p ^ B),
            ‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖ ^
              (2 * (2 * r)) := by
      apply Fintype.sum_congr
      intro c
      dsimp only [main]
      rw [← pow_mul]
      congr 1
      omega
    have htail :
        (∑ c : Fin k → ZMod (p ^ B), tail c ^ 2) =
          ∑ c : Fin k → ZMod (p ^ B),
            ‖vinogradovIntWeylSum (p ^ B) k Y
              (vinogradovMixedTailValue p b Y eta) c‖ ^
              (2 * (2 * t)) := by
      apply Fintype.sum_congr
      intro c
      dsimp only [tail]
      rw [← pow_mul]
      congr 1
      omega
    change (q * ∑ c, main c * tail c) ^ 2 ≤
      (q * ∑ c,
        ‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖ ^
          (2 * (2 * r))) *
      (q * ∑ c,
        ‖vinogradovIntWeylSum (p ^ B) k Y
          (vinogradovMixedTailValue p b Y eta) c‖ ^
          (2 * (2 * t)))
    rw [← hmain, ← htail]
    calc
      (q * ∑ c, main c * tail c) ^ 2 =
          q ^ 2 * (∑ c, main c * tail c) ^ 2 := by ring
      _ ≤ q ^ 2 * ((∑ c, main c ^ 2) * ∑ c, tail c ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg q)
      _ = (q * ∑ c, main c ^ 2) * (q * ∑ c, tail c ^ 2) := by ring
  · positivity

end

end ZeroFreeRegion.VinogradovKorobov
