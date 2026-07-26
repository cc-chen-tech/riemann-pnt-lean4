import ZeroFreeRegion.VinogradovKorobov.VinogradovTailResidueReparameterization

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The mixed norm-product average after exposing one residue digit in the
tail while retaining the original main factor. -/
noncomputable def normalizedVinogradovMixedOneStepRefinedNormAverage
    (p B a b k r t X Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (xi eta : ℤ) : ℝ :=
  (((p ^ B : ℕ) : ℝ)⁻¹ ^ k) *
    ∑ rho : ZMod p, ∑ c : Fin k → ZMod (p ^ B),
      ‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖ ^ (2 * r) *
        ‖vinogradovMixedTailResidueWeylSum
          p B b k Y eta rho c‖ ^ (2 * t)

/-- Refine the tail inside the mixed average before applying Cauchy.  The
main block remains coupled to every residue fiber, and the one-step Holder
cost uses the original tail order `2t` rather than the doubled order `4t`
created by prior Cauchy separation. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_le_oneStepCoupledRefinement
    (p B a b k r t X Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (ht : 0 < t) (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ≤
      (p : ℝ) ^ (2 * t - 1) *
        normalizedVinogradovMixedOneStepRefinedNormAverage
          p B a b k r t X Y xi eta := by
  rw [normalizedVinogradovMixedModConditionedMoment_eq_norm_product_average]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · unfold normalizedVinogradovMixedOneStepRefinedNormAverage
    let q : ℝ := (((p ^ B : ℕ) : ℝ)⁻¹ ^ k)
    let P : ℝ := (p : ℝ) ^ (2 * t - 1)
    let main : (Fin k → ZMod (p ^ B)) → ℝ := fun c ↦
      ‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖ ^ (2 * r)
    let tail :
        (Fin k → ZMod (p ^ B)) → ZMod p → ℝ := fun c rho ↦
      ‖vinogradovMixedTailResidueWeylSum
        p B b k Y eta rho c‖ ^ (2 * t)
    have hsum :
        (∑ c : Fin k → ZMod (p ^ B),
          main c *
            ‖vinogradovIntWeylSum (p ^ B) k Y
              (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * t)) ≤
          P * ∑ rho : ZMod p, ∑ c : Fin k → ZMod (p ^ B),
            main c * tail c rho := by
      calc
        (∑ c : Fin k → ZMod (p ^ B),
          main c *
            ‖vinogradovIntWeylSum (p ^ B) k Y
              (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * t)) ≤
            ∑ c : Fin k → ZMod (p ^ B),
              P * ∑ rho : ZMod p, main c * tail c rho := by
          apply Finset.sum_le_sum
          intro c hc
          have htail :=
            norm_vinogradovIntWeylSum_pow_le_tailResidueRefinement
              p B b k t Y ht eta c
          calc
            main c *
                ‖vinogradovIntWeylSum (p ^ B) k Y
                  (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * t) ≤
              main c * (P * ∑ rho : ZMod p, tail c rho) :=
                mul_le_mul_of_nonneg_left htail (by positivity)
            _ = P * ∑ rho : ZMod p, main c * tail c rho := by
              rw [← Finset.mul_sum]
              ring
        _ = P * ∑ c : Fin k → ZMod (p ^ B),
              ∑ rho : ZMod p, main c * tail c rho := by
          rw [Finset.mul_sum]
        _ = P * ∑ rho : ZMod p,
              ∑ c : Fin k → ZMod (p ^ B), main c * tail c rho := by
          rw [Finset.sum_comm]
    change q * ∑ c : Fin k → ZMod (p ^ B),
        main c *
          ‖vinogradovIntWeylSum (p ^ B) k Y
            (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * t) ≤
      P * (q * ∑ rho : ZMod p,
        ∑ c : Fin k → ZMod (p ^ B), main c * tail c rho)
    calc
      q * ∑ c : Fin k → ZMod (p ^ B),
          main c *
            ‖vinogradovIntWeylSum (p ^ B) k Y
              (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * t) ≤
        q * (P * ∑ rho : ZMod p,
          ∑ c : Fin k → ZMod (p ^ B), main c * tail c rho) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = P * (q * ∑ rho : ZMod p,
          ∑ c : Fin k → ZMod (p ^ B), main c * tail c rho) := by
        ring
  · positivity

/-- Exact residue reparameterization identifies the refined mixed average
with the sum of ordinary mixed moments at tail scale `b+1`.  Endpoint fibers
retain their true lengths and centers. -/
theorem normalizedVinogradovMixedOneStepRefinedNormAverage_eq_nextScale
    (p B a b k r t X Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (xi eta : ℤ) :
    normalizedVinogradovMixedOneStepRefinedNormAverage
        p B a b k r t X Y xi eta =
      ∑ rho : ZMod p,
        ‖normalizedVinogradovMixedModConditionedMoment
          p B a (b + 1) k r t X
            (vinogradovTailResidueLength p Y rho) xi
            (vinogradovTailResidueRefinedCenter p b eta rho)‖ := by
  unfold normalizedVinogradovMixedOneStepRefinedNormAverage
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro rho
  rw [normalizedVinogradovMixedModConditionedMoment_eq_norm_product_average]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · simp_rw [
      vinogradovMixedTailResidueWeylSum_eq_refinedTailWeylSum]
  · positivity

/-- One coupled terminal-tail recurrence.  Compared with Cauchy-first
reconditioning, it preserves the mixed moment order and pays only the sharp
one-step tail Holder factor `p^(2t-1)`. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_le_nextScaleCoupledSum
    (p B a b k r t X Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (ht : 0 < t) (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ≤
      (p : ℝ) ^ (2 * t - 1) *
        ∑ rho : ZMod p,
          ‖normalizedVinogradovMixedModConditionedMoment
            p B a (b + 1) k r t X
              (vinogradovTailResidueLength p Y rho) xi
              (vinogradovTailResidueRefinedCenter p b eta rho)‖ := by
  calc
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ≤
      (p : ℝ) ^ (2 * t - 1) *
        normalizedVinogradovMixedOneStepRefinedNormAverage
          p B a b k r t X Y xi eta :=
      norm_normalizedVinogradovMixedModConditionedMoment_le_oneStepCoupledRefinement
        p B a b k r t X Y ht xi eta
    _ = (p : ℝ) ^ (2 * t - 1) *
        ∑ rho : ZMod p,
          ‖normalizedVinogradovMixedModConditionedMoment
            p B a (b + 1) k r t X
              (vinogradovTailResidueLength p Y rho) xi
              (vinogradovTailResidueRefinedCenter p b eta rho)‖ := by
      rw [normalizedVinogradovMixedOneStepRefinedNormAverage_eq_nextScale]

end

end ZeroFreeRegion.VinogradovKorobov
