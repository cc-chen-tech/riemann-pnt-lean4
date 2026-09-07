import PrimeNumberTheorem.MWKFCubicAFEFrequencyMoment

open PrimeNumberTheorem.MWKFCubic

#check cubicAFEFrequencyMomentFinite
#check cubicAFEMollifiedMomentFinite_eq_diagonal_add_frequency
#check tendsto_cubicAFEDiagonal_add_frequency

open Complex Filter MeasureTheory
open scoped FourierTransform

-- Literal full mollifier support, both signs of nonzero shift, both dyadic
-- indices, and frequencies *outside* the actual time integral.
example (W : CubicTestWeight) (T X V : ℝ) :
    cubicAFEFrequencyMomentFinite W T X V =
    ∑ d ∈ (cubicMollifierSupport T).attach,
      ∑ e ∈ (cubicMollifierSupport T).attach,
        ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
          (((e.val / Nat.gcd d.val e.val : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
            (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V
              (cubicAFEProgressionDyadicCutoff (d := d.val)
                (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val jk.1 jk.2) t)
                ((h : ℝ) / ((e.val / Nat.gcd d.val e.val : ℕ) : ℝ))) *
            Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ.val : ℂ) *
              (Nat.gcdA (d.val / Nat.gcd d.val e.val) (e.val / Nat.gcd d.val e.val) : ℂ) /
                ((e.val / Nat.gcd d.val e.val : ℕ) : ℂ)) := rfl

#check (@cubicAFEMollifiedMomentFinite_eq_diagonal_add_frequency :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X → ∀ V : ℝ,
    cubicAFEMollifiedMomentFinite W T X V =
      cubicAFEDiagonalMomentFinite W T X V + cubicAFEFrequencyMomentFinite W T X V)

-- The limit is of the recombined expression only, at fixed physical T.
#check (@tendsto_cubicAFEDiagonal_add_frequency :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFEFrequencyMomentFinite W T X V)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)))
