import PrimeNumberTheorem.MWKFCubicAFEIntegratedPoisson

open Complex Filter MeasureTheory
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Full finite-height moment with frequencies outside physical time integration

The order is `(d,e), delta, (j,k), h, integral_t`. Replacing each whole box
uses proved equalities; no reordering across shifts, boxes or height limits.
-/

noncomputable def cubicAFEFrequencyBoxFinite
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) : ℂ :=
  (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
    (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t)
        ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ))) *
    Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
      (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
        ((e / Nat.gcd d e : ℕ) : ℂ))

theorem integral_cubicAFEDyadicPoissonTerm_eq_frequencyBox
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    (∫ t : ℝ, cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t) =
      cubicAFEFrequencyBoxFinite (d := d) W T X V he δ jk :=
  integral_cubicAFEDyadicPoissonTerm_eq_frequencySum W hT hX V hd he δ jk

theorem summable_cubicAFEFrequencyBoxFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    Summable (fun jk : ℕ × ℕ ↦ cubicAFEFrequencyBoxFinite (d := d) W T X V he δ jk) := by
  apply (summable_integral_cubicAFEDyadicPoissonTerm W hT hX V hd he δ).congr
  intro jk
  exact integral_cubicAFEDyadicPoissonTerm_eq_frequencyBox W hT hX V hd he δ jk

theorem summable_shift_cubicAFEFrequencyBoxFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Summable (fun δ : {δ : ℤ // δ ≠ 0} ↦ ∑' jk : ℕ × ℕ,
      cubicAFEFrequencyBoxFinite (d := d) W T X V he δ.val jk) := by
  apply (summable_shift_integral_cubicAFEDyadicPoissonTerm W hT hX V hd he).congr
  intro δ
  apply tsum_congr
  intro jk
  exact integral_cubicAFEDyadicPoissonTerm_eq_frequencyBox W hT hX V hd he δ.val jk

noncomputable def cubicAFEFrequencyMomentFinite (W : CubicTestWeight) (T X V : ℝ) : ℂ :=
  ∑ d ∈ (cubicMollifierSupport T).attach,
    ∑ e ∈ (cubicMollifierSupport T).attach,
      ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
        cubicAFEFrequencyBoxFinite (d := d.val) W T X V
          (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val jk

theorem cubicAFEDyadicPoissonMomentFinite_eq_frequency
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEDyadicPoissonMomentFinite W T X V = cubicAFEFrequencyMomentFinite W T X V := by
  unfold cubicAFEDyadicPoissonMomentFinite cubicAFEFrequencyMomentFinite
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  apply tsum_congr
  intro δ
  apply tsum_congr
  intro jk
  exact integral_cubicAFEDyadicPoissonTerm_eq_frequencyBox W hT hX V
    (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp e.property).1 δ.val jk

theorem cubicAFEMollifiedMomentFinite_eq_diagonal_add_frequency
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEMollifiedMomentFinite W T X V =
      cubicAFEDiagonalMomentFinite W T X V + cubicAFEFrequencyMomentFinite W T X V := by
  rw [cubicAFEMollifiedMomentFinite_eq_diagonal_add_dyadicPoisson W hT hX V,
    cubicAFEDyadicPoissonMomentFinite_eq_frequency W hT hX V]

theorem tendsto_cubicAFEDiagonal_add_frequency
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFEFrequencyMomentFinite W T X V)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) := by
  apply (tendsto_cubicAFEMollifiedMomentFinite W hT hX).congr'
  exact Eventually.of_forall (fun V ↦ cubicAFEMollifiedMomentFinite_eq_diagonal_add_frequency W hT hX V)

end PrimeNumberTheorem.MWKFCubic
