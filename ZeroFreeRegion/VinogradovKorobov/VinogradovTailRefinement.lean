import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedHolder
import ZeroFreeRegion.VinogradovKorobov.VinogradovResidueConditioning

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The affine tail Weyl sum restricted to one residue class of its internal
index modulo `p`.  These are the one-digit finer pieces used to condition the
tail from scale `b` toward scale `b + 1`. -/
noncomputable def vinogradovMixedTailResidueWeylSum
    (p B b k Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (eta : ℤ) (rho : ZMod p) (c : Fin k → ZMod (p ^ B)) : ℂ :=
  vinogradovResidueClassSum p Y rho fun n ↦
    ZMod.stdAddChar
      (vinogradovIntPhaseMod (p ^ B) c
        (vinogradovMixedTailValue p b Y eta n))

/-- Every internal-index residue fiber lies in one affine residue class at
the next tail scale `b + 1`. -/
theorem vinogradovMixedTailValue_modEq_refinedCenter
    (p b Y : ℕ) [Fact p.Prime] (eta : ℤ) (rho : ZMod p) (n : Fin Y)
    (hn : n ∈ vinogradovResidueClassFinset p Y rho) :
    Int.ModEq ((p : ℤ) ^ (b + 1))
      (vinogradovMixedTailValue p b Y eta n)
      (eta + (p : ℤ) ^ b * (rho.val : ℤ)) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hresidue :
      (((n.val + 1 : ℕ) : ZMod p)) = (rho.val : ZMod p) := by
    exact (mem_vinogradovResidueClassFinset p Y rho n).1 hn |>.trans
      (ZMod.natCast_zmod_val rho).symm
  have hmod : Nat.ModEq p (n.val + 1) rho.val :=
    (ZMod.natCast_eq_natCast_iff (n.val + 1) rho.val p).1 hresidue
  have hdvd :
      (p : ℤ) ∣ (rho.val : ℤ) - ((n.val + 1 : ℕ) : ℤ) :=
    hmod.dvd
  obtain ⟨d, hd⟩ := hdvd
  rw [Int.modEq_iff_dvd]
  refine ⟨d, ?_⟩
  unfold vinogradovMixedTailValue
  push_cast
  calc
    eta + (p : ℤ) ^ b * (rho.val : ℤ) -
        (eta + (p : ℤ) ^ b * ((n.val + 1 : ℕ) : ℤ)) =
      (p : ℤ) ^ b *
        ((rho.val : ℤ) - ((n.val + 1 : ℕ) : ℤ)) := by ring
    _ = (p : ℤ) ^ b * ((p : ℤ) * d) := by rw [hd]
    _ = (p : ℤ) ^ (b + 1) * d := by rw [pow_succ]; ring

/-- The original affine tail Weyl sum is exactly the sum of its `p`
one-digit residue refinements. -/
theorem sum_vinogradovMixedTailResidueWeylSum_eq
    (p B b k Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (eta : ℤ) (c : Fin k → ZMod (p ^ B)) :
    (∑ rho : ZMod p,
      vinogradovMixedTailResidueWeylSum p B b k Y eta rho c) =
        vinogradovIntWeylSum (p ^ B) k Y
          (vinogradovMixedTailValue p b Y eta) c := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold vinogradovMixedTailResidueWeylSum vinogradovIntWeylSum
  exact sum_vinogradovResidueClassSum_eq_full p Y fun n ↦
    ZMod.stdAddChar
      (vinogradovIntPhaseMod (p ^ B) c
        (vinogradovMixedTailValue p b Y eta n))

/-- One finite Holder conditioning step for the affine tail Weyl sum.  Its
`2s`-th power costs `p^(2s-1)` and leaves the sum of the corresponding powers
on the one-digit finer residue classes. -/
theorem norm_vinogradovIntWeylSum_pow_le_tailResidueRefinement
    (p B b k s Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (hs : 0 < s) (eta : ℤ) (c : Fin k → ZMod (p ^ B)) :
    ‖vinogradovIntWeylSum (p ^ B) k Y
        (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * s) ≤
      (p : ℝ) ^ (2 * s - 1) *
        ∑ rho : ZMod p,
          ‖vinogradovMixedTailResidueWeylSum
            p B b k Y eta rho c‖ ^ (2 * s) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← sum_vinogradovMixedTailResidueWeylSum_eq p B b k Y eta c]
  have hrefine :=
    norm_finset_sum_pow_le_card_mul_sum_norm_pow
      (Finset.univ : Finset (ZMod p))
      (fun rho ↦
        vinogradovMixedTailResidueWeylSum p B b k Y eta rho c)
      (2 * s - 1)
  have hexponent : 2 * s - 1 + 1 = 2 * s := by omega
  simpa [ZMod.card, hexponent] using hrefine

/-- The normalized tail norm moment after one residue-digit refinement.  The
coefficient average is unchanged; only the tail Weyl sum is split into its
`p` finer residue classes. -/
noncomputable def normalizedVinogradovMixedTailOneStepRefinedNormMoment
    (p B b k s Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (eta : ℤ) : ℝ :=
  (((p ^ B : ℕ) : ℝ)⁻¹ ^ k) *
    ∑ rho : ZMod p, ∑ c : Fin k → ZMod (p ^ B),
      ‖vinogradovMixedTailResidueWeylSum
        p B b k Y eta rho c‖ ^ (2 * s)

/-- The standard tail norm moment is controlled by its one-step conditioned
version with the sharp finite Holder loss `p^(2s-1)`. -/
theorem normalizedVinogradovMixedTailNormMoment_le_oneStepRefinement
    (p B b k s Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (hs : 0 < s) (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
      (p : ℝ) ^ (2 * s - 1) *
        normalizedVinogradovMixedTailOneStepRefinedNormMoment
          p B b k s Y eta := by
  unfold normalizedVinogradovMixedTailNormMoment
  unfold normalizedVinogradovMixedTailOneStepRefinedNormMoment
  let q : ℝ := (((p ^ B : ℕ) : ℝ)⁻¹ ^ k)
  let P : ℝ := (p : ℝ) ^ (2 * s - 1)
  let F :
      (Fin k → ZMod (p ^ B)) → ZMod p → ℝ := fun c rho ↦
    ‖vinogradovMixedTailResidueWeylSum
      p B b k Y eta rho c‖ ^ (2 * s)
  have hsum :
      (∑ c : Fin k → ZMod (p ^ B),
        ‖vinogradovIntWeylSum (p ^ B) k Y
          (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * s)) ≤
        ∑ c : Fin k → ZMod (p ^ B), P * ∑ rho : ZMod p, F c rho := by
    apply Finset.sum_le_sum
    intro c _
    exact norm_vinogradovIntWeylSum_pow_le_tailResidueRefinement
      p B b k s Y hs eta c
  calc
    q * ∑ c : Fin k → ZMod (p ^ B),
        ‖vinogradovIntWeylSum (p ^ B) k Y
          (vinogradovMixedTailValue p b Y eta) c‖ ^ (2 * s) ≤
      q * ∑ c : Fin k → ZMod (p ^ B),
        P * ∑ rho : ZMod p, F c rho :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = P * (q * ∑ rho : ZMod p,
        ∑ c : Fin k → ZMod (p ^ B), F c rho) := by
      calc
        q * ∑ c : Fin k → ZMod (p ^ B),
            P * ∑ rho : ZMod p, F c rho =
          q * (P * ∑ c : Fin k → ZMod (p ^ B),
            ∑ rho : ZMod p, F c rho) := by
              congr 1
              rw [Finset.mul_sum]
        _ = P * (q * ∑ c : Fin k → ZMod (p ^ B),
            ∑ rho : ZMod p, F c rho) := by ring
        _ = P * (q * ∑ rho : ZMod p,
            ∑ c : Fin k → ZMod (p ^ B), F c rho) := by
              rw [Finset.sum_comm]

end

end ZeroFreeRegion.VinogradovKorobov
