import ZeroFreeRegion.VinogradovKorobov.VinogradovResidueConditioning
import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedMoment

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The weighted Weyl sum restricted to one residue class modulo `Q`. -/
def vinogradovWeightedResidueWeylSum
    (p coefficientScale k X Q : ℕ) [Fact p.Prime] [NeZero Q]
    (ξ : ZMod Q) (c : VinogradovWeightedCoefficient p coefficientScale k) : ℂ :=
  vinogradovResidueClassSum Q X ξ
    (vinogradovWeightedPhaseTerm p coefficientScale c)

/-- A finite conditioned `(n+1)`-st moment of the weighted Weyl sums.  This
is the discrete coefficient-space model of the conditioned mean values used
in efficient congruencing. -/
def vinogradovWeightedConditionedMoment
    (p coefficientScale k X Q n : ℕ) [Fact p.Prime] [NeZero Q]
    (ξ : ZMod Q) : ℝ :=
  ∑ c : VinogradovWeightedCoefficient p coefficientScale k,
    ‖vinogradovWeightedResidueWeylSum p coefficientScale k X Q ξ c‖ ^ (n + 1)

/-- A genuine scale transition for the finite conditioned weighted moment:
conditioning from residue level `a` to level `b` costs
`p^((b-a)n)` and sums the finer conditioned moments over all lifts. -/
theorem vinogradovWeightedConditionedMoment_le_refinement
    (p coefficientScale k X a b n : ℕ) [Fact p.Prime]
    (hab : a ≤ b) [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) :
    vinogradovWeightedConditionedMoment
        p coefficientScale k X (p ^ a) n ξ ≤
      ((p ^ (b - a) : ℕ) : ℝ) ^ n *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          vinogradovWeightedConditionedMoment
            p coefficientScale k X (p ^ b) n z := by
  simpa [vinogradovWeightedConditionedMoment,
    vinogradovWeightedResidueWeylSum] using
      (sum_norm_vinogradovResidueClassSum_pow_le_refinement
        (C := VinogradovWeightedCoefficient p coefficientScale k)
        p a b X (Fact.out : p.Prime).pos hab ξ
        (fun c ↦ vinogradovWeightedPhaseTerm p coefficientScale c) n)

end

end ZeroFreeRegion.VinogradovKorobov
