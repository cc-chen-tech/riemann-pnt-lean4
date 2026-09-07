import PrimeNumberTheorem.MWKFCubicAFEDyadicTimeIntegral

open Complex Filter Set MeasureTheory

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual finite-height moment in integrated dyadic Poisson coordinates

Both mollifier indices range over the literal cubic support, and the shift
ranges over every signed nonzero integer. The nesting order is
`(d,e), delta, (j,k), integral_t, h`. No independent height limit of the
diagonal or the off-diagonal is assumed or asserted.
-/

noncomputable def cubicAFEDyadicPoissonMomentFinite
    (W : CubicTestWeight) (T X V : ℝ) : ℂ :=
  ∑ d ∈ (cubicMollifierSupport T).attach,
    ∑ e ∈ (cubicMollifierSupport T).attach,
      ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ, ∫ t : ℝ,
        cubicAFEDyadicPoissonTerm (d := d.val) W T X V
          (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val jk t

theorem summable_shift_integral_cubicAFEDyadicPoissonTerm
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Summable (fun δ : {δ : ℤ // δ ≠ 0} ↦ ∑' jk : ℕ × ℕ, ∫ t : ℝ,
      cubicAFEDyadicPoissonTerm (d := d) W T X V he δ.val jk t) := by
  apply (hasSum_integral_cubicAFE_shiftFibers W hT hX V hd.ne' he.ne').summable.congr
  intro δ
  rw [tsum_cubicAFEShiftFiber_eq_progression (d := d) he δ.val
    (fun p : ℕ × ℕ ↦ ∫ t : ℝ, cubicAFECombinedSummandFinite W T X V d e t p)]
  exact cubicAFEProgressionIntegral_eq_dyadicPoisson W hT hX V hd he δ.val

theorem cubicAFEProgressionMomentFinite_eq_dyadicPoisson
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEProgressionMomentFinite W T X V = cubicAFEDyadicPoissonMomentFinite W T X V := by
  let f (d e : ℕ) : ℂ := ∑' δ : {δ : ℤ // δ ≠ 0},
    ∑' m : cubicAFEProgression d e δ.val, ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ.val m.val)
  have hsum : cubicAFEDyadicPoissonMomentFinite W T X V =
      ∑ d ∈ (cubicMollifierSupport T).attach,
        ∑ e ∈ (cubicMollifierSupport T).attach, f d.val e.val := by
    unfold cubicAFEDyadicPoissonMomentFinite
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [f]
    apply tsum_congr
    intro δ
    exact (cubicAFEProgressionIntegral_eq_dyadicPoisson W hT hX V
      (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp e.property).1 δ.val).symm
  rw [hsum]
  simp only [Finset.sum_attach]
  rw [Finset.sum_attach (cubicMollifierSupport T)
    (fun d : ℕ ↦ ∑ e ∈ cubicMollifierSupport T, f d e)]
  rfl

theorem cubicAFEMollifiedMomentFinite_eq_diagonal_add_dyadicPoisson
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEMollifiedMomentFinite W T X V =
      cubicAFEDiagonalMomentFinite W T X V + cubicAFEDyadicPoissonMomentFinite W T X V := by
  rw [cubicAFEMollifiedMomentFinite_eq_diagonal_add_progression W hT hX V,
    cubicAFEProgressionMomentFinite_eq_dyadicPoisson W hT hX V]

/-- The height limit applies only to the recombined expression. This is
still fixed physical T, not the final cubic-mollifier asymptotic. -/
theorem tendsto_cubicAFEDiagonal_add_dyadicPoisson
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFEDyadicPoissonMomentFinite W T X V)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) := by
  apply (tendsto_cubicAFEMollifiedMomentFinite W hT hX).congr'
  exact Eventually.of_forall (fun V ↦
    cubicAFEMollifiedMomentFinite_eq_diagonal_add_dyadicPoisson W hT hX V)

end PrimeNumberTheorem.MWKFCubic
