import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalizedConditionedMoment
import Mathlib.Algebra.Order.Floor.Div

open scoped BigOperators NNReal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

private instance primePower_neZero
    (p n : ℕ) [Fact p.Prime] : NeZero (p ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- The refined residue scale `ceil ((k-r+1)b / r)` from Wooley's
approximate translation-dilation step. -/
def vinogradovRefinedScale (k r b : ℕ) : ℕ :=
  ((k - r + 1) * b) ⌈/⌉ r

/-- The refined scale is the least scale whose `r`-fold multiple reaches the
target `(k-r+1)b`. -/
theorem vinogradovRefinedScale_le_iff
    (k r b c : ℕ) (hr : 0 < r) :
    vinogradovRefinedScale k r b ≤ c ↔
      (k - r + 1) * b ≤ r * c := by
  exact ceilDiv_le_iff_le_mul hr

/-- The target is bounded by `r` times the refined scale. -/
theorem target_le_mul_vinogradovRefinedScale
    (k r b : ℕ) (hr : 0 < r) :
    (k - r + 1) * b ≤ r * vinogradovRefinedScale k r b := by
  exact (vinogradovRefinedScale_le_iff k r b
    (vinogradovRefinedScale k r b) hr).mp le_rfl

/-- If the target lies above `r*a`, then the refined scale lies above `a`. -/
theorem le_vinogradovRefinedScale
    (k r a b : ℕ) (hr : 0 < r)
    (hlower : r * a ≤ (k - r + 1) * b) :
    a ≤ vinogradovRefinedScale k r b := by
  have h := hlower.trans (target_le_mul_vinogradovRefinedScale k r b hr)
  exact Nat.le_of_mul_le_mul_left h hr

/-- If the target exceeds `r*a` by at most `error`, then the refined scale
exceeds `a` by at most `ceil (error/r)`. -/
theorem vinogradovRefinedScale_sub_le_errorCeil
    (k r a b error : ℕ) (hr : 0 < r)
    (hupper : (k - r + 1) * b ≤ r * a + error) :
    vinogradovRefinedScale k r b - a ≤ error ⌈/⌉ r := by
  have herror : error ≤ r * (error ⌈/⌉ r) :=
    (ceilDiv_le_iff_le_mul hr).mp le_rfl
  have htarget : (k - r + 1) * b ≤ r * (a + error ⌈/⌉ r) := by
    calc
      (k - r + 1) * b ≤ r * a + error := hupper
      _ ≤ r * a + r * (error ⌈/⌉ r) := Nat.add_le_add_left herror _
      _ = r * (a + error ⌈/⌉ r) := by rw [Nat.mul_add]
  have hrefined : vinogradovRefinedScale k r b ≤ a + error ⌈/⌉ r :=
    (vinogradovRefinedScale_le_iff k r b _ hr).mpr htarget
  omega

/-- The close-scale branch of approximate translation-dilation invariance.
When the target scale differs from `r*a` by at most `error`, normalized
conditioning reaches the refined scale with loss
`p^(ceil(error/r) * w)`. -/
theorem vinogradovNormalizedConditionedMoment_le_refinedScale_of_gap
    {C : Type*} [Fintype C]
    (p k r a b error X w : ℕ) (hp : 0 < p) (hr : 0 < r)
    (hlower : r * a ≤ (k - r + 1) * b)
    (hupper : (k - r + 1) * b ≤ r * a + error)
    [NeZero (p ^ a)]
    [NeZero (p ^ vinogradovRefinedScale k r b)]
    (ξ : ZMod (p ^ a)) (coefficient : Fin X → ℂ)
    (phase : C → Fin X → ℂ) (hw : 1 ≤ w) :
    vinogradovNormalizedConditionedMoment
        (p ^ a) X w ξ coefficient phase ≤
      (((p ^ (error ⌈/⌉ r) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z :
            ZMod (p ^ vinogradovRefinedScale k r b) ↦
          ZMod.castHom
              (pow_dvd_pow p
                (le_vinogradovRefinedScale k r a b hr hlower))
              (ZMod (p ^ a)) z = ξ),
          vinogradovNormalizedConditionedMoment
            (p ^ vinogradovRefinedScale k r b) X w z coefficient phase := by
  let refined := vinogradovRefinedScale k r b
  have harefined : a ≤ refined :=
    le_vinogradovRefinedScale k r a b hr hlower
  have hgap : refined - a ≤ error ⌈/⌉ r :=
    vinogradovRefinedScale_sub_le_errorCeil
      k r a b error hr hupper
  have htransition := vinogradovNormalizedConditionedMoment_le_refinement
    p a refined X w hp harefined ξ coefficient phase hw
  have hpowNat : p ^ (refined - a) ≤ p ^ (error ⌈/⌉ r) :=
    Nat.pow_le_pow_right hp hgap
  have hfactor :
      (((p ^ (refined - a) : ℕ) : ℝ≥0) ^ w) ≤
        (((p ^ (error ⌈/⌉ r) : ℕ) : ℝ≥0) ^ w) := by
    gcongr
  exact htransition.trans (by gcongr)

/-- The close-scale transition specialized to the finite degree-weighted Weyl
coefficient space. -/
theorem vinogradovWeightedNormalizedConditionedMoment_le_refinedScale_of_gap
    (p coefficientScale k r a b error X w : ℕ) [Fact p.Prime]
    (hr : 0 < r)
    (hlower : r * a ≤ (k - r + 1) * b)
    (hupper : (k - r + 1) * b ≤ r * a + error)
    (ξ : ZMod (p ^ a)) (coefficient : Fin X → ℂ) (hw : 1 ≤ w) :
    vinogradovWeightedNormalizedConditionedMoment
        p coefficientScale k X (p ^ a) w ξ coefficient ≤
      (((p ^ (error ⌈/⌉ r) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z :
            ZMod (p ^ vinogradovRefinedScale k r b) ↦
          ZMod.castHom
              (pow_dvd_pow p
                (le_vinogradovRefinedScale k r a b hr hlower))
              (ZMod (p ^ a)) z = ξ),
          vinogradovWeightedNormalizedConditionedMoment
            p coefficientScale k X
              (p ^ vinogradovRefinedScale k r b) w z coefficient := by
  exact vinogradovNormalizedConditionedMoment_le_refinedScale_of_gap
    (C := VinogradovWeightedCoefficient p coefficientScale k)
    p k r a b error X w (Fact.out : p.Prime).pos hr hlower hupper
      ξ coefficient
      (fun c ↦ vinogradovWeightedPhaseTerm p coefficientScale c) hw

end

end ZeroFreeRegion.VinogradovKorobov
