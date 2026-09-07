import PrimeNumberTheorem.MWKFCubicAFEDyadicMoment

open Complex Filter Set MeasureTheory

namespace PrimeNumberTheorem.MWKFCubic

-- The global finite-height expression must contain the actual mollifier
-- support and all signed nonzero shifts, not an abstract remainder.
#check cubicAFEDyadicPoissonMomentFinite
#check cubicAFEProgressionMomentFinite_eq_dyadicPoisson
#check cubicAFEMollifiedMomentFinite_eq_diagonal_add_dyadicPoisson
#check tendsto_cubicAFEDiagonal_add_dyadicPoisson

-- Literal support, all signed nonzero shifts, both dyadic indices, and
-- the full physical integral. Changing this to positive shifts only or
-- moving the height limit through a subseries must fail this contract.
example (W : CubicTestWeight) (T X V : ℝ) :
    cubicAFEDyadicPoissonMomentFinite W T X V =
      ∑ d ∈ (cubicMollifierSupport T).attach,
        ∑ e ∈ (cubicMollifierSupport T).attach,
          ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ, ∫ t : ℝ,
            cubicAFEDyadicPoissonTerm (d := d.val) W T X V
              (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val jk t := rfl

#check (@cubicAFEMollifiedMomentFinite_eq_diagonal_add_dyadicPoisson :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ V : ℝ, cubicAFEMollifiedMomentFinite W T X V =
      cubicAFEDiagonalMomentFinite W T X V + cubicAFEDyadicPoissonMomentFinite W T X V)

#check (@tendsto_cubicAFEDiagonal_add_dyadicPoisson :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFEDyadicPoissonMomentFinite W T X V)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)))

#check (@summable_shift_integral_cubicAFEDyadicPoissonTerm :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, 0 < d → ∀ he : 0 < e,
      Summable (fun δ : {δ : ℤ // δ ≠ 0} ↦ ∑' jk : ℕ × ℕ, ∫ t : ℝ,
        cubicAFEDyadicPoissonTerm (d := d) W T X V he δ.val jk t))

end PrimeNumberTheorem.MWKFCubic
