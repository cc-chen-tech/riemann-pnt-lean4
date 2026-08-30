import PrimeNumberTheorem.MWKFCubicAFEDyadicReassembly

open Complex Set MeasureTheory
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

-- These must be actual absolutely convergent reassemblies. A pointwise
-- partition alone must not be accepted as permission to commute two sums.
#check summable_cubicAFEProgression_dyadic_weighted
#check tsum_cubicAFEProgression_eq_dyadic
#check summable_cubicAFEProgressionSummand
#check cubicAFEShiftFiber_eq_dyadicPoisson
#check summable_cubicAFEDyadicPoissonTerm
#check cubicAFEProgressionIntegral_eq_dyadic
#check summable_cubicAFEProgressionDyadicIntegral

-- Joint convergence is a conclusion, not an extra interchange hypothesis.
#check (@summable_cubicAFEProgression_dyadic_weighted :
  ∀ {d e : ℕ} (he : 0 < e) (δ : ℤ) (f : cubicAFEProgression d e δ → ℂ),
    Summable f → Summable (fun z : cubicAFEProgression d e δ × (ℕ × ℕ) ↦
      (cubicAFEProgressionDyadicCutoff (d := d) he δ z.2.1 z.2.2 z.1.val : ℂ) * f z.1))

-- The returned box scales concern the real second index, not a rounded
-- quantity or an independent surrogate variable.
#check (@cubicAFEProgressionDyadicCutoff_scales :
  ∀ {d e : ℕ} (he : 0 < e) {δ : ℤ} {j k : ℕ} {x : ℝ},
    cubicAFEProgressionDyadicCutoff (d := d) he δ j k x ≠ 0 →
    x ∈ Icc ((2 : ℝ)^j / 2) (2 * (2 : ℝ)^j) ∧
      cubicAFEProgressionRealSecond d e δ x ∈ Icc ((2 : ℝ)^k / 2) (2 * (2 : ℝ)^k))

-- Unfolded end-to-end contract: no arbitrary cutoff, summability,
-- partition-of-unity or spectral hypothesis may enter the actual identity.
-- The order of the two infinite sums is deliberately part of the contract.
#check (@cubicAFEShiftFiber_eq_dyadicPoisson :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (_hd : 0 < d) (he : 0 < e)
    (δ : ℤ) (t : ℝ), 1 / 2 < X →
    (∑' p : cubicAFEShiftFiber d e δ, cubicAFECombinedSummandFinite W T X V d e t p.val) =
      ∑' jk : ℕ × ℕ, (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
        𝓕 (cubicAFEProgressionCutoffSummand W T X V
          (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t)
          ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
            (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
              ((e / Nat.gcd d e : ℕ) : ℂ)))

#check (@summable_cubicAFEDyadicPoissonTerm :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < d → ∀ (he : 0 < e)
    (δ : ℤ) (t : ℝ), 1 / 2 < X →
    Summable (fun jk : ℕ × ℕ ↦ cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t))

-- Literal full-line integrals, not an assumed time-integral interchange.
#check (@cubicAFEProgressionIntegral_eq_dyadic :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, d ≠ 0 → ∀ (he : 0 < e) (δ : ℤ),
      (∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
        cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) =
        ∑' jk : ℕ × ℕ, ∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
          (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
            cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val))

end PrimeNumberTheorem.MWKFCubic
